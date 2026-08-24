//! `installer_iife`：把需要独立展示的匿名立即调用从合法 AST 收回成局部函数名。
//!
//! 这个 pass 处理两类 IIFE。匿名安装器沿用父 block 中的局部名：
//!
//! ` (function(x) local f = function(y) return x, y end; emit = f end)("ax") `
//!
//! 会收成
//!
//! ` local l0 = function(x) local f = function(y) return x, y end; emit = f end; l0("ax") `
//!
//! 其它包含多条语句或复合控制流的 IIFE 则放进最小 `do` 作用域：
//!
//! ` do local l0 = function() BODY end; l0() end `
//!
//! 这样新增 closure binding 会在原调用点后立即死亡，不会把 captured value 的 root
//! 生命周期延长到父 block 末尾。单条简单语句的短 IIFE 保留原样。两类结果都交给后面的
//! `function_sugar` 再决定是否继续变成 `local function l0(...) ... end`。
//!
//! 它依赖 AST build 已经把直接调用的 callee 落成合法 `FunctionExpr`，也依赖
//! `materialize-temps` 先把 AST 自己残留的 temp 物化掉，这样这里新增的名字只需要走
//! synthetic-local 命名空间，不会越权复用前层 temp。
//!
//! 它不负责：
//! - 判断多值转发与物化约束，它们由 HIR value-pack owner 负责；
//! - 把这个局部函数进一步降成方法声明或 `local function`，那属于 `function_sugar`。

use std::collections::BTreeSet;

use crate::ast::common::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstLocalOrigin, AstModule, AstNameRef, AstStmt, AstSyntheticLocalId,
};
use crate::hir::TempId;

use super::ReadabilityContext;
use super::visit::{self, AstVisitor};
use super::walk::{self, AstRewritePass, BlockKind};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut InstallerIifePass)
}

struct InstallerIifePass;

impl AstRewritePass for InstallerIifePass {
    fn rewrite_block(&mut self, block: &mut AstBlock, _kind: BlockKind) -> bool {
        let mut next_synthetic_local = next_synthetic_local_index_in_block(block);
        let mut changed = false;
        let mut index = 0;
        while index < block.stmts.len() {
            let Some(rewritten) =
                rewrite_installer_iife_stmt(&block.stmts[index], &mut next_synthetic_local)
            else {
                index += 1;
                continue;
            };
            let rewritten_len = rewritten.len();
            block.stmts.splice(index..=index, rewritten);
            changed = true;
            index += rewritten_len;
        }
        changed
    }
}

fn rewrite_installer_iife_stmt(
    stmt: &AstStmt,
    next_synthetic_local: &mut usize,
) -> Option<Vec<AstStmt>> {
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
        return None;
    }

    let binding_id = AstSyntheticLocalId(TempId(*next_synthetic_local));
    *next_synthetic_local += 1;

    let rewritten = vec![
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::SyntheticLocal(binding_id),
                attr: AstLocalAttr::None,
                origin: AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::FunctionExpr(function.clone())],
        })),
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::SyntheticLocal(binding_id)),
                args: call.args.clone(),
                method_name: None,
            })),
        })),
    ];

    if is_named_installer {
        Some(rewritten)
    } else {
        Some(vec![AstStmt::DoBlock(Box::new(AstBlock {
            stmts: rewritten,
        }))])
    }
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

fn next_synthetic_local_index_in_block(block: &AstBlock) -> usize {
    let mut collector = SyntheticLocalCollector::default();
    visit::visit_block(block, &mut collector);
    collector.next
}

#[derive(Default)]
struct SyntheticLocalCollector {
    next: usize,
}

impl AstVisitor for SyntheticLocalCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::LocalDecl(local_decl) => {
                for binding in &local_decl.bindings {
                    self.collect_binding_ref(binding.id);
                }
            }
            AstStmt::NumericFor(numeric_for) => {
                self.collect_binding_ref(numeric_for.binding);
            }
            AstStmt::GenericFor(generic_for) => {
                for binding in &generic_for.bindings {
                    self.collect_binding_ref(*binding);
                }
            }
            AstStmt::FunctionDecl(function_decl) => {
                self.collect_function_name(&function_decl.target);
            }
            AstStmt::LocalFunctionDecl(function_decl) => {
                self.collect_binding_ref(function_decl.name);
            }
            AstStmt::GlobalDecl(_)
            | AstStmt::Assign(_)
            | AstStmt::CallStmt(_)
            | AstStmt::Return(_)
            | AstStmt::If(_)
            | AstStmt::While(_)
            | AstStmt::Repeat(_)
            | AstStmt::DoBlock(_)
            | AstStmt::Break
            | AstStmt::Continue
            | AstStmt::Goto(_)
            | AstStmt::Label(_)
            | AstStmt::Error(_) => {}
        }
    }

    fn visit_lvalue(&mut self, target: &AstLValue) {
        if let AstLValue::Name(name) = target {
            self.collect_name_ref(name);
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Var(name) = expr {
            self.collect_name_ref(name);
        }
    }

    fn visit_function_expr(&mut self, function: &AstFunctionExpr) -> bool {
        if let Some(vararg) = function.named_vararg {
            self.collect_binding_ref(vararg);
        }
        for binding in &function.captured_bindings {
            self.collect_binding_ref(*binding);
        }
        true
    }
}

impl SyntheticLocalCollector {
    fn collect_function_name(&mut self, target: &AstFunctionName) {
        match target {
            AstFunctionName::Plain(path) => self.collect_name_ref(&path.root),
            AstFunctionName::Method(path, _) => self.collect_name_ref(&path.root),
        }
    }

    fn collect_name_ref(&mut self, name: &AstNameRef) {
        if let AstNameRef::SyntheticLocal(id) = name {
            self.next = self.next.max(id.index() + 1);
        }
    }

    fn collect_binding_ref(&mut self, binding: AstBindingRef) {
        if let AstBindingRef::SyntheticLocal(id) = binding {
            self.next = self.next.max(id.index() + 1);
        }
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
