//! AST 输出层共用的语法简写查询。
//!
//! 消费现有表达式，提供不改变求值顺序的比较拼写与 numeric-for 步长形式。

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
