//! AST 对 `repeat ... until` 条件边界的 typed HIR 生命周期事实适配。
//!
//! 这个模块只把 AST 的稳定 binding identity 投影回 HIR certificate，并保留
//! `<close>`、debug identity 与 HIR `Preserve` 这些源码/跨层硬边界。对象流、闭包
//! escape 与物理 home 已由 `repeat_root_lifetimes` 证明，AST consumer 不再从表达式
//! 形状重新推断。

use crate::ast::common::{AstBindingRef, AstLocalAttr, AstLocalBinding, AstRewriteAuthority};
use crate::hir::{HirRepeatBinding, HirRepeatConditionLifetimeFacts};

pub(super) fn binding_must_live_through_condition(
    binding: &AstLocalBinding,
    lifetime: &HirRepeatConditionLifetimeFacts,
) -> bool {
    binding.attr == AstLocalAttr::Close
        || binding.origin.is_debug_hinted()
        || binding.rewrite_authority.must_preserve()
        || match binding.rewrite_authority {
            // AST 自己创建的 binding 不借用 HIR 许可；具体 consumer 仍须证明其候选
            // 没有引入 AST-owned 的资源生命周期。
            AstRewriteAuthority::AstOwned => false,
            AstRewriteAuthority::Hir(_) => {
                !hir_binding_may_end_before_condition(binding.id, lifetime)
            }
        }
}

pub(super) fn hir_binding_may_end_before_condition(
    binding: AstBindingRef,
    lifetime: &HirRepeatConditionLifetimeFacts,
) -> bool {
    hir_repeat_binding(binding)
        .is_some_and(|binding| lifetime.may_end_before_condition.contains(&binding))
}

/// 把 AST materialize 后的名字归一化回 HIR 发布 certificate 时的稳定 binding 身份。
///
/// `SyntheticLocal(temp)` 只有在 caller 已证明它来自 HIR 时才能使用；AST 自建的同号
/// synthetic local 不能冒充 HIR temp。
fn hir_repeat_binding(binding: AstBindingRef) -> Option<HirRepeatBinding> {
    match binding {
        AstBindingRef::Local(local) => Some(HirRepeatBinding::Local(local)),
        AstBindingRef::Temp(temp) => Some(HirRepeatBinding::Temp(temp)),
        AstBindingRef::SyntheticLocal(local) => Some(HirRepeatBinding::Temp(local.0)),
    }
}
