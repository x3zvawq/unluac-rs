//! 收回 alias 内联后才暴露的原始字面量比较和布尔逻辑壳。
//!
//! 这里只使用 `expr_analysis` 的严格字面量证明；动态值、元方法、跨数值表示和
//! 非布尔值的 truthy 结果都保留原形状。Boolean 的 `not` 也只做无事件的字面量归一，
//! 不改写循环/分支 owner。

use super::super::common::{AstExpr, AstModule, AstUnaryOpKind};
use super::ReadabilityContext;
use super::expr_analysis::{expr_is_boolean_valued, primitive_literal_comparison_value};
use super::walk::{self, AstRewritePass};

pub(super) fn apply(module: &mut AstModule, _context: ReadabilityContext) -> bool {
    walk::rewrite_module(module, &mut LiteralFoldPass)
}

struct LiteralFoldPass;

impl AstRewritePass for LiteralFoldPass {
    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        let replacement = match expr {
            AstExpr::Binary(binary) => {
                primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
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
            AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => match &unary.expr {
                AstExpr::Boolean(value) => Some(AstExpr::Boolean(!*value)),
                _ => None,
            },
            _ => None,
        };

        let Some(replacement) = replacement else {
            return false;
        };
        *expr = replacement;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::AstUnaryExpr;

    #[test]
    fn folds_boolean_not_without_guessing_truthy_values() {
        let mut expr = AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: AstExpr::Boolean(true),
        }));
        assert!(LiteralFoldPass.rewrite_expr(&mut expr));
        assert_eq!(expr, AstExpr::Boolean(false));

        let mut dynamic = AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: AstExpr::Integer(0),
        }));
        assert!(!LiteralFoldPass.rewrite_expr(&mut dynamic));
        assert!(matches!(dynamic, AstExpr::Unary(_)));
    }

    #[test]
    fn folds_false_boolean_not_to_true() {
        let mut expr = AstExpr::Unary(Box::new(AstUnaryExpr {
            op: AstUnaryOpKind::Not,
            expr: AstExpr::Boolean(false),
        }));
        assert!(LiteralFoldPass.rewrite_expr(&mut expr));
        assert_eq!(expr, AstExpr::Boolean(true));
    }
}
