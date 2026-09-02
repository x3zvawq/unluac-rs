//! repeat collective suffix 的 AST 词法生命周期边界。
//!
//! VM 物理 root、closure escape 与值身份由 HIR fixed-point 后的
//! `repeat_root_lifetimes` 证明，并通过当前 `AstRepeat::lifetime` 的 typed binding 集传入。
//! 本层只把实际 suffix 的 HIR-origin 直属声明与该 repeat condition 边界精确配对；条件直接
//! 引用、`<close>` 与 debug identity 仍是 AST 源码事实，不会被 HIR certificate 越权放行。

use crate::ast::common::{AstExpr, AstLocalAttr, AstLocalBinding, AstStmt};
use crate::hir::HirRepeatConditionLifetimeFacts;

use super::super::super::binding_flow::binding_mentions_in_expr;
use super::super::super::repeat_lifetime::binding_must_live_through_condition;

pub(super) fn suffix_shortens_referenced_binding(stmts: &[AstStmt], expr: &AstExpr) -> bool {
    let expr_bindings = binding_mentions_in_expr(expr);
    direct_suffix_bindings(stmts).any(|binding| expr_bindings.contains(&binding.id))
}

pub(super) fn suffix_has_preserved_lifetime(
    stmts: &[AstStmt],
    start: usize,
    lifetime: &HirRepeatConditionLifetimeFacts,
) -> bool {
    direct_suffix_bindings(&stmts[start..])
        .any(|binding| binding_must_live_through_condition(&binding, lifetime))
}

fn direct_suffix_bindings(stmts: &[AstStmt]) -> impl Iterator<Item = AstLocalBinding> + '_ {
    stmts.iter().flat_map(|stmt| match stmt {
        AstStmt::LocalDecl(local_decl) => local_decl.bindings.clone(),
        AstStmt::LocalFunctionDecl(function_decl) => vec![AstLocalBinding {
            id: function_decl.name,
            attr: AstLocalAttr::None,
            origin: function_decl.origin,
            rewrite_authority: function_decl.rewrite_authority.clone(),
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
