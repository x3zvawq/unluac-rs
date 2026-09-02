//! repeat collective suffix 的 AST 词法生命周期边界。
//!
//! VM 物理 root、closure escape 与值身份由 HIR fixed-point 后的
//! `repeat_root_lifetimes` 证明，并通过当前 `AstRepeat::lifetime` 的 typed binding 集传入。
//! 本层只把实际 suffix 的 HIR-origin 直属声明与该 repeat condition 边界精确配对；条件直接
//! 引用、`<close>` 与 debug identity 仍是 AST 源码事实，不会被 HIR certificate 越权放行。

use crate::ast::common::{
    AstBindingRef, AstExpr, AstLocalAttr, AstLocalBinding, AstRewriteAuthority, AstStmt,
};
use crate::hir::{HirRepeatBinding, HirRepeatConditionLifetimeFacts};

use super::super::super::binding_flow::binding_mentions_in_expr;

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
        .any(|binding| binding_has_intrinsic_lifetime(binding, lifetime))
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

fn binding_has_intrinsic_lifetime(
    binding: AstLocalBinding,
    lifetime: &HirRepeatConditionLifetimeFacts,
) -> bool {
    binding.attr == AstLocalAttr::Close
        || binding.origin.is_debug_hinted()
        || binding.rewrite_authority.must_preserve()
        || match binding.rewrite_authority {
            // AST 自己创建的 binding 不借用 HIR 许可；它仍由本 pass 的源码级候选证明负责。
            AstRewriteAuthority::AstOwned => false,
            AstRewriteAuthority::Hir(_) => hir_repeat_binding(binding.id)
                .is_none_or(|binding| !lifetime.may_end_before_condition.contains(&binding)),
        }
}

/// 把 AST materialize 后的名字归一化回 HIR 发布 certificate 时的稳定 binding 身份。
///
/// `SyntheticLocal(temp)` 只有携带 `AstRewriteAuthority::Hir` 时才会走到这里，因此不会把
/// AST 自建的同号 synthetic local 冒充 HIR temp；materialize pass 也无需改写 certificate。
fn hir_repeat_binding(binding: AstBindingRef) -> Option<HirRepeatBinding> {
    match binding {
        AstBindingRef::Local(local) => Some(HirRepeatBinding::Local(local)),
        AstBindingRef::Temp(temp) => Some(HirRepeatBinding::Temp(temp)),
        AstBindingRef::SyntheticLocal(local) => Some(HirRepeatBinding::Temp(local.0)),
    }
}
