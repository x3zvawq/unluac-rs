//! 整理 alias 内联后暴露的字面量比较和布尔包装。
//!
//! 消费共享常量与无事件证明，保留原操作和可观察求值。

use super::super::common::{AstExpr, AstModule, AstTargetDialect, AstUnaryOpKind};
use super::ReadabilityContext;
use super::expr_analysis::{
    constant_truthiness, expr_is_boolean_valued, is_discard_safe_expr_for_target,
    primitive_literal_comparison_value,
};
use super::walk::{self, AstRewritePass};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    walk::rewrite_module(
        module,
        &mut LiteralFoldPass {
            target: context.target,
        },
    )
}

struct LiteralFoldPass {
    target: AstTargetDialect,
}

impl AstRewritePass for LiteralFoldPass {
    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        let replacement = match expr {
            AstExpr::Binary(binary) if !binary.original_operation => {
                primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs, self.target)
                    .map(AstExpr::Boolean)
            }
            AstExpr::LogicalAnd(logical)
                if !logical.preserves_boolean_prewrite
                    && expr_is_boolean_valued(&logical.lhs)
                    && matches!(logical.rhs, AstExpr::Boolean(true)) =>
            {
                Some(logical.lhs.clone())
            }
            AstExpr::LogicalOr(logical)
                if !logical.preserves_boolean_prewrite
                    && expr_is_boolean_valued(&logical.lhs)
                    && matches!(logical.rhs, AstExpr::Boolean(false)) =>
            {
                Some(logical.lhs.clone())
            }
            AstExpr::Unary(unary)
                if unary.op == AstUnaryOpKind::Not && !unary.original_operation =>
            {
                constant_truthiness(&unary.expr)
                    .filter(|_| is_discard_safe_expr_for_target(&unary.expr, self.target))
                    .map(|value| AstExpr::Boolean(!value))
            }
            _ => None,
        };

        let Some(replacement) = replacement else {
            return false;
        };
        *expr = replacement;
        true
    }
}
