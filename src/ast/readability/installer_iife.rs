//! 为需要独立展示的匿名立即调用恢复局部函数名。
//!
//! 消费合法 FunctionExpr 及 binding/capture，保留原调用和闭包根的作用域。

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
    // 分配进度随模块保存，不能在子函数或下一轮重置；Ast 与 HirTemp 身份分域。
    let mut pass = InstallerIifePass {
        next_synthetic_local: module.next_synthetic_local,
    };
    let changed = walk::rewrite_module_scoped(module, 0, &mut pass);
    module.next_synthetic_local = pass.next_synthetic_local;
    changed
}

struct InstallerIifePass {
    next_synthetic_local: usize,
}

impl ScopedAstRewritePass for InstallerIifePass {
    type Scope = usize;

    fn enter_function(&mut self, function: &mut AstFunctionExpr, scope: &mut Self::Scope) {
        *scope = function_entry_local_count(function);
    }

    fn enter_stmt_children(&mut self, stmt: &AstStmt, scope: &mut Self::Scope) {
        *scope = scope.saturating_add(stmt_child_local_count(stmt));
    }

    fn after_stmt(&mut self, stmt: &AstStmt, scope: &mut Self::Scope) {
        *scope = scope.saturating_add(direct_local_count(stmt));
    }

    fn rewrite_stmt(&mut self, stmt: &mut AstStmt, scope: &Self::Scope) -> bool {
        let next_synthetic_local = self.next_synthetic_local;
        let Some(rewritten) = rewrite_installer_iife_stmt(stmt, next_synthetic_local) else {
            return false;
        };
        if *scope >= crate::SOURCE_LOCAL_LIMIT {
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
    if call.required_luau_inlining.is_some() {
        // 候选拒绝[ProofGap]：必须内联的调用不能改换已证明的 callee 身份。
        return None;
    }
    let AstExpr::FunctionExpr(function) = &call.callee else {
        return None;
    };
    let is_named_installer = function_expr_looks_like_named_installer(function);
    if !is_named_installer && !function_expr_is_substantial(function) {
        // 候选拒绝[PolicyBoundary]：单条简单 IIFE 保留紧凑原形；这是展示阈值，不是等价性要求。
        return None;
    }

    let binding_id = AstSyntheticLocalId::Ast(next_synthetic_local);

    // 只新增无属性的 Recovered binding；原函数及参数整节点保留，避免重建
    // PhysicalRoot/DebugHinted origin、attr 或 capture 身份。
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
                required_luau_inlining: None,
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
        | AstExpr::IfExpr(_)
        | AstExpr::Call(_)
        | AstExpr::MethodCall(_)
        | AstExpr::SingleValue(_)
        | AstExpr::CaptureInitializer(_)
        | AstExpr::VarArg
        | AstExpr::TableConstructor(_)
        | AstExpr::Error(_) => false,
    }
}
