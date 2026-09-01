//! repeat collective suffix 的 AST 词法生命周期边界。
//!
//! VM 物理 root、closure escape 与值身份由 HIR fixed-point 后的
//! `repeat_root_lifetimes` 证明，并通过 `AstLocalOrigin` 传入。本层只消费稳定
//! provenance 与 Lua 源码词法事实：条件直接引用的 binding 不能被包进更短的 `do`
//! 作用域，`<close>`、debug identity 和 physical root 也不能被提前结束。

use crate::ast::common::{AstExpr, AstLocalAttr, AstLocalBinding, AstLocalOrigin, AstStmt};

use super::super::super::binding_flow::binding_mentions_in_expr;

pub(super) fn suffix_shortens_referenced_binding(stmts: &[AstStmt], expr: &AstExpr) -> bool {
    let expr_bindings = binding_mentions_in_expr(expr);
    direct_suffix_bindings(stmts).any(|binding| expr_bindings.contains(&binding.id))
}

pub(super) fn suffix_has_preserved_lifetime(stmts: &[AstStmt], start: usize) -> bool {
    direct_suffix_bindings(&stmts[start..]).any(binding_has_intrinsic_lifetime)
}

fn direct_suffix_bindings(stmts: &[AstStmt]) -> impl Iterator<Item = AstLocalBinding> + '_ {
    stmts.iter().flat_map(|stmt| match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl.bindings.clone(),
        AstStmt::LocalFunctionDecl(function_decl) => vec![AstLocalBinding {
            id: function_decl.name,
            attr: AstLocalAttr::None,
            origin: function_decl.origin,
        }],
        AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::Return(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::If(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => Vec::new(),
    })
}

fn binding_has_intrinsic_lifetime(binding: AstLocalBinding) -> bool {
    binding.attr == AstLocalAttr::Close || !matches!(binding.origin, AstLocalOrigin::Recovered)
}
