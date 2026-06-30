//! binding 集合引用查询。
//!
//! `binding_flow` 主文件负责 use-count / mention 统计；这个模块只回答“某个
//! stmt/block/expr 是否引用这一组 binding”。它主要服务 `statement_merge` 这类需要
//! 判断 hoisted local 能否安全下沉的 pass，不负责计数或改写。

use std::collections::BTreeSet;

use super::super::binding_ref::binding_from_name_ref;
use crate::ast::common::{
    AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalBinding, AstNameRef, AstStmt, AstTableField, AstTableKey,
};

#[derive(Debug, Default)]
pub(in crate::ast::readability) struct BindingRefSet {
    ids: BTreeSet<AstBindingRef>,
}

impl BindingRefSet {
    pub(in crate::ast::readability) fn from_bindings(bindings: &[AstLocalBinding]) -> Self {
        Self {
            ids: bindings.iter().map(|binding| binding.id).collect(),
        }
    }
}

trait BindingLookup {
    fn contains_binding(&self, binding: AstBindingRef) -> bool;
}

impl BindingLookup for BindingRefSet {
    fn contains_binding(&self, binding: AstBindingRef) -> bool {
        self.ids.contains(&binding)
    }
}

pub(in crate::ast::readability) fn stmt_references_any_binding(
    stmt: &AstStmt,
    bindings: &[AstLocalBinding],
) -> bool {
    let refs = BindingRefSet::from_bindings(bindings);
    stmt_references_binding_set(stmt, &refs)
}

pub(in crate::ast::readability) fn stmt_references_binding_set(
    stmt: &AstStmt,
    bindings: &BindingRefSet,
) -> bool {
    stmt_references_binding_lookup(stmt, bindings)
}

fn stmt_references_binding_lookup(stmt: &AstStmt, bindings: &dyn BindingLookup) -> bool {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            local_decl
                .bindings
                .iter()
                .any(|binding| bindings.contains_binding(binding.id))
                || local_decl
                    .values
                    .iter()
                    .any(|value| expr_references_binding_lookup(value, bindings))
        }
        AstStmt::GlobalDecl(global_decl) => global_decl
            .values
            .iter()
            .any(|value| expr_references_binding_lookup(value, bindings)),
        AstStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_references_binding_lookup(target, bindings))
                || assign
                    .values
                    .iter()
                    .any(|value| expr_references_binding_lookup(value, bindings))
        }
        AstStmt::CallStmt(call_stmt) => call_references_binding_lookup(&call_stmt.call, bindings),
        AstStmt::Return(ret) => ret
            .values
            .iter()
            .any(|value| expr_references_binding_lookup(value, bindings)),
        AstStmt::If(if_stmt) => {
            expr_references_binding_lookup(&if_stmt.cond, bindings)
                || block_references_binding_lookup(&if_stmt.then_block, bindings)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_references_binding_lookup(block, bindings))
        }
        AstStmt::While(while_stmt) => {
            expr_references_binding_lookup(&while_stmt.cond, bindings)
                || block_references_binding_lookup(&while_stmt.body, bindings)
        }
        AstStmt::Repeat(repeat_stmt) => {
            block_references_binding_lookup(&repeat_stmt.body, bindings)
                || expr_references_binding_lookup(&repeat_stmt.cond, bindings)
        }
        AstStmt::NumericFor(numeric_for) => {
            bindings.contains_binding(numeric_for.binding)
                || expr_references_binding_lookup(&numeric_for.start, bindings)
                || expr_references_binding_lookup(&numeric_for.limit, bindings)
                || expr_references_binding_lookup(&numeric_for.step, bindings)
                || block_references_binding_lookup(&numeric_for.body, bindings)
        }
        AstStmt::GenericFor(generic_for) => {
            generic_for
                .bindings
                .iter()
                .any(|binding| bindings.contains_binding(*binding))
                || generic_for
                    .iterator
                    .iter()
                    .any(|expr| expr_references_binding_lookup(expr, bindings))
                || block_references_binding_lookup(&generic_for.body, bindings)
        }
        AstStmt::DoBlock(block) => block_references_binding_lookup(block, bindings),
        AstStmt::FunctionDecl(function_decl) => {
            function_name_references_binding_lookup(&function_decl.target, bindings)
                || function_capture_references_binding_lookup(&function_decl.func, bindings)
        }
        AstStmt::LocalFunctionDecl(function_decl) => {
            bindings.contains_binding(function_decl.name)
                || function_capture_references_binding_lookup(&function_decl.func, bindings)
        }
        AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => false,
    }
}

pub(in crate::ast::readability) fn block_references_binding_set(
    block: &AstBlock,
    bindings: &BindingRefSet,
) -> bool {
    block_references_binding_lookup(block, bindings)
}

fn block_references_binding_lookup(block: &AstBlock, bindings: &dyn BindingLookup) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_references_binding_lookup(stmt, bindings))
}

pub(in crate::ast::readability) fn expr_references_any_binding(
    expr: &AstExpr,
    bindings: &[AstLocalBinding],
) -> bool {
    let refs = BindingRefSet::from_bindings(bindings);
    expr_references_binding_set(expr, &refs)
}

pub(in crate::ast::readability) fn expr_references_binding_set(
    expr: &AstExpr,
    bindings: &BindingRefSet,
) -> bool {
    expr_references_binding_lookup(expr, bindings)
}

fn expr_references_binding_lookup(expr: &AstExpr, bindings: &dyn BindingLookup) -> bool {
    match expr {
        AstExpr::Var(name) => name_ref_matches_binding_lookup(name, bindings),
        AstExpr::FieldAccess(access) => expr_references_binding_lookup(&access.base, bindings),
        AstExpr::IndexAccess(access) => {
            expr_references_binding_lookup(&access.base, bindings)
                || expr_references_binding_lookup(&access.index, bindings)
        }
        AstExpr::Unary(unary) => expr_references_binding_lookup(&unary.expr, bindings),
        AstExpr::Binary(binary) => {
            expr_references_binding_lookup(&binary.lhs, bindings)
                || expr_references_binding_lookup(&binary.rhs, bindings)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_references_binding_lookup(&logical.lhs, bindings)
                || expr_references_binding_lookup(&logical.rhs, bindings)
        }
        AstExpr::Call(call) => {
            expr_references_binding_lookup(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstExpr::MethodCall(call) => {
            expr_references_binding_lookup(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstExpr::SingleValue(expr) => expr_references_binding_lookup(expr, bindings),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            AstTableField::Array(value) => expr_references_binding_lookup(value, bindings),
            AstTableField::Record(record) => {
                let key_references_binding = match &record.key {
                    AstTableKey::Name(_) => false,
                    AstTableKey::Expr(expr) => expr_references_binding_lookup(expr, bindings),
                };
                key_references_binding || expr_references_binding_lookup(&record.value, bindings)
            }
        }),
        AstExpr::FunctionExpr(function) => {
            function_capture_references_binding_lookup(function, bindings)
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. }
        | AstExpr::VarArg
        | AstExpr::Error(_) => false,
    }
}

fn call_references_binding_lookup(call: &AstCallKind, bindings: &dyn BindingLookup) -> bool {
    match call {
        AstCallKind::Call(call) => {
            expr_references_binding_lookup(&call.callee, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
        AstCallKind::MethodCall(call) => {
            expr_references_binding_lookup(&call.receiver, bindings)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_binding_lookup(arg, bindings))
        }
    }
}

fn function_name_references_binding_lookup(
    target: &AstFunctionName,
    bindings: &dyn BindingLookup,
) -> bool {
    let path = match target {
        AstFunctionName::Plain(path) => path,
        AstFunctionName::Method(path, _) => path,
    };
    name_ref_matches_binding_lookup(&path.root, bindings)
}

fn function_capture_references_binding_lookup(
    function: &AstFunctionExpr,
    bindings: &dyn BindingLookup,
) -> bool {
    function
        .captured_bindings
        .iter()
        .any(|binding| bindings.contains_binding(*binding))
}

fn lvalue_references_binding_lookup(target: &AstLValue, bindings: &dyn BindingLookup) -> bool {
    match target {
        AstLValue::Name(name) => name_ref_matches_binding_lookup(name, bindings),
        AstLValue::FieldAccess(access) => expr_references_binding_lookup(&access.base, bindings),
        AstLValue::IndexAccess(access) => {
            expr_references_binding_lookup(&access.base, bindings)
                || expr_references_binding_lookup(&access.index, bindings)
        }
    }
}

fn name_ref_matches_binding_lookup(name: &AstNameRef, bindings: &dyn BindingLookup) -> bool {
    binding_from_name_ref(name).is_some_and(|binding| bindings.contains_binding(binding))
}
