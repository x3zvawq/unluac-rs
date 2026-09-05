//! `installer_iife`：把需要独立展示的匿名立即调用从合法 AST 收回成局部函数名。
//!
//! 这个 pass 处理两类 IIFE。匿名安装器会先得到一个局部函数名：
//!
//! ` (function(x) local f = function(y) return x, y end; emit = f end)("ax") `
//!
//! 会收成
//!
//! ` do local l0 = function(x) local f = function(y) return x, y end; emit = f end; l0("ax") end `
//!
//! 其它包含多条语句或复合控制流的 IIFE 同样放进最小 `do` 作用域：
//!
//! ` do local l0 = function() BODY end; l0() end `
//!
//! 这样新增 closure binding 会在原调用点后立即死亡，不会把 closure root 生命周期延长到
//! 父 block 末尾。改写只新增一个 `Recovered`、无 attr 的 synthetic binding；原 function 与
//! 调用参数以完整 AST 节点克隆，既有 PhysicalRoot/DebugHinted origin、local attr、binding ref
//! 与 capture 身份都不重建。单条简单语句的短 IIFE 保留原样。两类结果都交给后面的
//! `function_sugar` 再决定是否继续变成 `local function l0(...) ... end`。
//!
//! AST build 已把 callee 落成合法 `FunctionExpr`。新增 binding 从模块分配器取得
//! `Ast` 身份，与 `materialize-temps` 保留的 `HirTemp` 分域；分配进度随模块快照保存，
//! 不因进入子函数或新一轮改写重置，也不扫描前层编号来避让。
//!
//! 它不负责：
//! - 判断多值转发与物化约束，它们由 HIR value-pack owner 负责；
//! - 把这个局部函数进一步降成方法声明或 `local function`，那属于 `function_sugar`。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstLocalOrigin, AstModule, AstNameRef, AstRewriteAuthority, AstStmt,
    AstSyntheticLocalId,
};

use super::ReadabilityContext;
use super::local_scope_limit::{
    direct_local_count, function_entry_local_count, stmt_child_local_count,
};
use super::walk::{self, ScopedAstRewritePass};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    let mut pass = InstallerIifePass {
        next_synthetic_local: module.next_synthetic_local,
    };
    let changed =
        walk::rewrite_module_scoped(module, &InstallerIifeScope { active_locals: 0 }, &mut pass);
    module.next_synthetic_local = pass.next_synthetic_local;
    changed
}

struct InstallerIifePass {
    next_synthetic_local: usize,
}

#[derive(Clone)]
struct InstallerIifeScope {
    active_locals: usize,
}

impl ScopedAstRewritePass for InstallerIifePass {
    type Scope = InstallerIifeScope;

    fn enter_function(
        &mut self,
        function: &mut AstFunctionExpr,
        _outer_scope: &Self::Scope,
    ) -> Self::Scope {
        InstallerIifeScope {
            active_locals: function_entry_local_count(function),
        }
    }

    fn scope_for_stmt_children(&mut self, stmt: &AstStmt, scope: &Self::Scope) -> Self::Scope {
        InstallerIifeScope {
            active_locals: scope
                .active_locals
                .saturating_add(stmt_child_local_count(stmt)),
        }
    }

    fn scope_after_stmt(&mut self, stmt: &AstStmt, scope: &Self::Scope) -> Self::Scope {
        InstallerIifeScope {
            active_locals: scope.active_locals.saturating_add(direct_local_count(stmt)),
        }
    }

    fn rewrite_stmt(&mut self, stmt: &mut AstStmt, scope: &Self::Scope) -> bool {
        let next_synthetic_local = self.next_synthetic_local;
        let Some(rewritten) = rewrite_installer_iife_stmt(stmt, next_synthetic_local) else {
            return false;
        };
        if scope.active_locals >= crate::SOURCE_LOCAL_LIMIT {
            // 候选拒绝[TargetConstraint]：命名 IIFE 会在调用点新增一个 active local；现有词法 owner 已耗尽项目源码 local 预算时，后置缩域无法保证释放外层或长生命周期槽。
            return false;
        }
        self.next_synthetic_local += 1;
        *stmt = rewritten;
        true
    }
}

fn rewrite_installer_iife_stmt(stmt: &AstStmt, next_synthetic_local: usize) -> Option<AstStmt> {
    let AstStmt::CallStmt(call_stmt) = stmt else {
        return None;
    };
    let AstCallKind::Call(call) = &call_stmt.call else {
        return None;
    };
    let AstExpr::FunctionExpr(function) = &call.callee else {
        return None;
    };
    let is_named_installer = function_expr_looks_like_named_installer(function);
    if !is_named_installer && !function_expr_is_substantial(function) {
        // 候选拒绝[PolicyBoundary]：单条简单 IIFE 保留紧凑原形；这是展示阈值，不是等价性要求。
        return None;
    }

    let binding_id = AstSyntheticLocalId::Ast(next_synthetic_local);

    let rewritten = vec![
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::SyntheticLocal(binding_id),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
                rewrite_authority: AstRewriteAuthority::AstOwned,
            }],
            values: vec![AstExpr::FunctionExpr(function.clone())],
            initializer_merge_transaction: None,
            initializer_root_profile: None,
        })),
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::SyntheticLocal(binding_id)),
                args: call.args.clone(),
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            })),
        })),
    ];

    Some(AstStmt::DoBlock(Box::new(AstBlock { stmts: rewritten })))
}

pub(super) fn function_expr_is_substantial(function: &AstFunctionExpr) -> bool {
    let body_stmts = substantive_function_body_stmts(function);
    body_stmts.len() > 1
        || matches!(
            body_stmts.first(),
            Some(
                AstStmt::If(_)
                    | AstStmt::While(_)
                    | AstStmt::Repeat(_)
                    | AstStmt::NumericFor(_)
                    | AstStmt::GenericFor(_)
                    | AstStmt::DoBlock(_)
                    | AstStmt::FunctionDecl(_)
                    | AstStmt::LocalFunctionDecl(_)
            )
        )
}

fn substantive_function_body_stmts(function: &AstFunctionExpr) -> &[AstStmt] {
    let body_stmts = function.body.stmts.as_slice();
    match body_stmts.last() {
        Some(AstStmt::Return(ret)) if ret.values.is_empty() => &body_stmts[..body_stmts.len() - 1],
        _ => body_stmts,
    }
}

fn function_expr_looks_like_named_installer(function: &AstFunctionExpr) -> bool {
    let body_stmts = substantive_function_body_stmts(function);
    let Some((installer_stmt, setup_stmts)) = body_stmts.split_last() else {
        return false;
    };

    if !setup_stmts.iter().all(stmt_is_installer_setup) {
        return false;
    }

    let function_bindings = collect_function_bindings(setup_stmts);
    stmt_looks_like_installer_export(installer_stmt, &function_bindings)
}

fn stmt_is_installer_setup(stmt: &AstStmt) -> bool {
    matches!(stmt, AstStmt::LocalDecl(_) | AstStmt::LocalFunctionDecl(_))
}

fn collect_function_bindings(stmts: &[AstStmt]) -> BTreeSet<AstBindingRef> {
    let mut bindings = BTreeSet::new();
    for stmt in stmts {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                for (binding, value) in local_decl.bindings.iter().zip(local_decl.values.iter()) {
                    if matches!(value, AstExpr::FunctionExpr(_)) {
                        bindings.insert(binding.id);
                    }
                }
            }
            AstStmt::LocalFunctionDecl(function_decl) => {
                bindings.insert(function_decl.name);
            }
            _ => {}
        }
    }
    bindings
}

fn stmt_looks_like_installer_export(
    stmt: &AstStmt,
    function_bindings: &BTreeSet<AstBindingRef>,
) -> bool {
    match stmt {
        AstStmt::Assign(assign) => assign_looks_like_installer_export(assign, function_bindings),
        AstStmt::FunctionDecl(function_decl) => {
            function_decl_looks_like_installer_export(function_decl)
        }
        AstStmt::LocalDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::DoBlock(_)
        | AstStmt::Error(_) => false,
    }
}

fn assign_looks_like_installer_export(
    assign: &AstAssign,
    function_bindings: &BTreeSet<AstBindingRef>,
) -> bool {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return false;
    }
    lvalue_looks_like_export_slot(&assign.targets[0])
        && expr_looks_like_exported_function_value(&assign.values[0], function_bindings)
}

fn function_decl_looks_like_installer_export(function_decl: &AstFunctionDecl) -> bool {
    function_name_looks_like_export_slot(&function_decl.target)
}

fn function_name_looks_like_export_slot(target: &AstFunctionName) -> bool {
    match target {
        AstFunctionName::Plain(path) => {
            matches!(path.root, AstNameRef::Global(_)) || !path.fields.is_empty()
        }
        // 这里要和 `assign` 路径对齐：只要源码目标是“向某个名字路径/receiver 挂函数”，
        // 它就是安装器在导出函数值。否则 `t.f = function ... end` 和
        // `function t:f() ... end` 会在两个语法糖入口上被判出不同结果。
        AstFunctionName::Method(_, _) => true,
    }
}

fn lvalue_looks_like_export_slot(target: &AstLValue) -> bool {
    matches!(
        target,
        AstLValue::Name(AstNameRef::Global(_)) | AstLValue::FieldAccess(_)
    )
}

fn expr_looks_like_exported_function_value(
    expr: &AstExpr,
    function_bindings: &BTreeSet<AstBindingRef>,
) -> bool {
    match expr {
        AstExpr::FunctionExpr(_) => true,
        AstExpr::Var(AstNameRef::Param(_)) => true,
        AstExpr::Var(AstNameRef::Local(local)) => {
            function_bindings.contains(&AstBindingRef::Local(*local))
        }
        AstExpr::Var(AstNameRef::SyntheticLocal(local)) => {
            function_bindings.contains(&AstBindingRef::SyntheticLocal(*local))
        }
        AstExpr::Var(AstNameRef::Temp(_))
        | AstExpr::Var(AstNameRef::Upvalue(_))
        | AstExpr::Var(AstNameRef::Environment)
        | AstExpr::Var(AstNameRef::Global(_))
        | AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::FieldAccess(_)
        | AstExpr::IndexAccess(_)
        | AstExpr::Unary(_)
        | AstExpr::Binary(_)
        | AstExpr::LogicalAnd(_)
        | AstExpr::LogicalOr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::SingleValue(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::Error(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{AstIf, AstTargetDialect};
    use crate::decompile::DecompileDialect;
    use crate::hir::{HirInlineDisposition, HirProtoRef, LocalId, TempId};

    fn substantial_iife_call() -> AstStmt {
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                    function: HirProtoRef(1),
                    params: Vec::new(),
                    is_vararg: false,
                    named_vararg: None,
                    body: AstBlock {
                        stmts: vec![
                            AstStmt::Error("first".to_owned()),
                            AstStmt::Error("second".to_owned()),
                        ],
                    },
                    captured_bindings: BTreeSet::new(),
                    captured_params: BTreeSet::new(),
                    capture_names_by_upvalue: std::collections::BTreeMap::new(),
                    capture_write_names: BTreeSet::new(),
                })),
                args: Vec::new(),
                method_key: None,
                callee_root_handoff: None,
                method_rewrite_transaction: None,
            })),
        }))
    }

    #[test]
    fn nested_iife_separates_hir_identity_and_preserves_allocation() {
        let outer = AstSyntheticLocalId::HirTemp(TempId(0));
        let mut module = AstModule {
            next_synthetic_local: 0,
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: vec![AstLocalBinding {
                            id: AstBindingRef::SyntheticLocal(outer),
                            attr: AstLocalAttr::None,
                            origin: AstLocalOrigin::Recovered,
                            rewrite_authority: AstRewriteAuthority::Hir(
                                HirInlineDisposition::Unknown,
                            ),
                        }],
                        values: vec![AstExpr::Integer(1)],
                        initializer_merge_transaction: None,
                        initializer_root_profile: None,
                    })),
                    AstStmt::If(Box::new(AstIf {
                        cond: AstExpr::Boolean(true),
                        then_block: AstBlock {
                            stmts: vec![substantial_iife_call()],
                        },
                        else_block: None,
                    })),
                ],
            },
        };

        assert!(apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(DecompileDialect::Lua54),
                options: super::super::ReadabilityOptions::default(),
            },
        ));

        let AstStmt::If(if_stmt) = &module.body.stmts[1] else {
            panic!("second statement should remain the containing if");
        };
        let [AstStmt::DoBlock(iife_scope)] = if_stmt.then_block.stmts.as_slice() else {
            panic!("nested IIFE should become one do scope");
        };
        let Some(AstStmt::LocalDecl(installer)) = iife_scope.stmts.first() else {
            panic!("IIFE scope should start with the installer local");
        };
        assert_eq!(
            installer.bindings[0].id,
            AstBindingRef::SyntheticLocal(AstSyntheticLocalId::Ast(0))
        );
        let context = ReadabilityContext {
            target: AstTargetDialect::new(DecompileDialect::Lua54),
            options: super::super::ReadabilityOptions::default(),
        };
        assert!(!apply(&mut module, context));
        module.body.stmts.push(substantial_iife_call());
        assert!(apply(&mut module, context));
        let Some(AstStmt::DoBlock(scope)) = module.body.stmts.last() else {
            panic!("second installer should receive its own scope");
        };
        let AstStmt::LocalDecl(installer) = &scope.stmts[0] else {
            panic!("second scope should declare its installer");
        };
        assert_eq!(
            installer.bindings[0].id,
            AstBindingRef::SyntheticLocal(AstSyntheticLocalId::Ast(1))
        );
    }

    #[test]
    fn nested_iife_keeps_call_shape_when_active_locals_exhaust_budget() {
        let mut module = AstModule {
            next_synthetic_local: 0,
            entry_function: HirProtoRef(0),
            body: AstBlock {
                stmts: vec![
                    AstStmt::LocalDecl(Box::new(AstLocalDecl {
                        bindings: (0..crate::SOURCE_LOCAL_LIMIT)
                            .map(|index| AstLocalBinding {
                                id: AstBindingRef::Local(LocalId(index)),
                                attr: AstLocalAttr::None,
                                origin: AstLocalOrigin::Recovered,
                                rewrite_authority: AstRewriteAuthority::AstOwned,
                            })
                            .collect(),
                        values: Vec::new(),
                        initializer_merge_transaction: None,
                        initializer_root_profile: None,
                    })),
                    AstStmt::If(Box::new(AstIf {
                        cond: AstExpr::Boolean(true),
                        then_block: AstBlock {
                            stmts: vec![substantial_iife_call()],
                        },
                        else_block: None,
                    })),
                ],
            },
        };

        assert!(!apply(
            &mut module,
            ReadabilityContext {
                target: AstTargetDialect::new(DecompileDialect::Lua54),
                options: super::super::ReadabilityOptions::default(),
            },
        ));

        let AstStmt::If(if_stmt) = &module.body.stmts[1] else {
            panic!("second statement should remain the containing if");
        };
        assert!(matches!(
            if_stmt.then_block.stmts.as_slice(),
            [AstStmt::CallStmt(_)]
        ));
    }
}
