//! AST 输出层共享的不改变求值顺序的语法简写。
//!
//! 比较方向由 HIR 的原操作数准备事实决定，debug / generate 按 AST 原左右发射，
//! 不根据表达式复杂度换向。例如 `lookup < callback()` 的两次观察不能被调换。
//! 本模块仅处理 `not (a == b)` 的 `a ~= b` 形式及 numeric-for 默认步长省略。

use super::common::{AstBinaryOpKind, AstExpr, AstUnaryExpr, AstUnaryOpKind};
use crate::decompile::DecompileDialect;

pub(crate) struct PreferredRelationalRender<'a> {
    pub(crate) lhs: &'a AstExpr,
    pub(crate) op_text: &'static str,
    pub(crate) rhs: &'a AstExpr,
}

pub(crate) fn preferred_negated_relational_render(
    unary: &AstUnaryExpr,
) -> Option<PreferredRelationalRender<'_>> {
    if unary.op != AstUnaryOpKind::Not {
        return None;
    }
    let AstExpr::Binary(binary) = &unary.expr else {
        return None;
    };
    if binary.op != AstBinaryOpKind::Eq {
        return None;
    }

    Some(PreferredRelationalRender {
        lhs: &binary.lhs,
        op_text: "~=",
        rhs: &binary.rhs,
    })
}

#[cfg(feature = "decompile-debug")]
pub(crate) fn is_default_numeric_for_step(step: &AstExpr) -> bool {
    match step {
        AstExpr::Integer(1) => true,
        AstExpr::Number(value) => *value == 1.0,
        _ => false,
    }
}

pub(crate) fn is_default_numeric_for_step_for_target(
    step: &AstExpr,
    dialect: DecompileDialect,
) -> bool {
    match step {
        AstExpr::Integer(1) => true,
        AstExpr::Number(value) => {
            *value == 1.0
                && !matches!(
                    dialect,
                    DecompileDialect::Lua53 | DecompileDialect::Lua54 | DecompileDialect::Lua55
                )
        }
        _ => false,
    }
}
