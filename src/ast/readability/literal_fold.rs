//! 收回 alias 内联后才暴露的原始字面量比较和布尔逻辑壳。
//!
//! 这里只使用 `expr_analysis` 的严格常量与无事件证明；动态访问、元方法、跨数值表示和
//! 会创建可观察对象的 truthy 结果都保留原形状。`not` 可在操作数 truthiness 已知且整次
//! 求值可删除时归一，不改写循环/分支 owner。

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
            AstExpr::Binary(binary) => {
                primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs, self.target)
                    .map(AstExpr::Boolean)
            }
            AstExpr::LogicalAnd(logical)
                if expr_is_boolean_valued(&logical.lhs)
                    && matches!(logical.rhs, AstExpr::Boolean(true)) =>
            {
                Some(logical.lhs.clone())
            }
            AstExpr::LogicalOr(logical)
                if expr_is_boolean_valued(&logical.lhs)
                    && matches!(logical.rhs, AstExpr::Boolean(false)) =>
            {
                Some(logical.lhs.clone())
            }
            AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
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
