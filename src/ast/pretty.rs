//! 这个文件集中放 AST 输出层共享的“源码形态偏好”启发式。
//!
//! AST 本身只保存稳定语义，不会专门为 `elseif`、`>` / `>=` 之类的打印糖再扩一层
//! 语法节点。这里提供跨 debug / generate 共享的轻量规则，让不同输出入口在不改变
//! AST 语义的前提下，尽量收敛到更接近源码的文本形状。

use super::common::{AstBinaryExpr, AstBinaryOpKind, AstExpr, AstTableField, AstTableKey};

pub(crate) struct PreferredRelationalRender<'a> {
    pub(crate) lhs: &'a AstExpr,
    pub(crate) op_text: &'static str,
    pub(crate) rhs: &'a AstExpr,
}

pub(crate) fn preferred_relational_render(
    binary: &AstBinaryExpr,
) -> Option<PreferredRelationalRender<'_>> {
    let flipped = should_flip_relational_operands(&binary.lhs, &binary.rhs);
    match (binary.op, flipped) {
        (AstBinaryOpKind::Lt, false) => Some(PreferredRelationalRender {
            lhs: &binary.lhs,
            op_text: "<",
            rhs: &binary.rhs,
        }),
        (AstBinaryOpKind::Lt, true) => Some(PreferredRelationalRender {
            lhs: &binary.rhs,
            op_text: ">",
            rhs: &binary.lhs,
        }),
        (AstBinaryOpKind::Le, false) => Some(PreferredRelationalRender {
            lhs: &binary.lhs,
            op_text: "<=",
            rhs: &binary.rhs,
        }),
        (AstBinaryOpKind::Le, true) => Some(PreferredRelationalRender {
            lhs: &binary.rhs,
            op_text: ">=",
            rhs: &binary.lhs,
        }),
        _ => None,
    }
}

fn should_flip_relational_operands(lhs: &AstExpr, rhs: &AstExpr) -> bool {
    expr_display_complexity(lhs) < expr_display_complexity(rhs)
}

fn expr_display_complexity(expr: &AstExpr) -> usize {
    match expr {
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Complex { .. } => 1,
        // 把变量刻意排在常量之上，这样 `0 < value` 会更倾向翻成 `value > 0`。
        AstExpr::Var(_) | AstExpr::VarArg => 2,
        AstExpr::Unary(unary) => 1 + expr_display_complexity(&unary.expr),
        AstExpr::FieldAccess(access) => 2 + expr_display_complexity(&access.base),
        AstExpr::IndexAccess(access) => {
            2 + expr_display_complexity(&access.base) + expr_display_complexity(&access.index)
        }
        AstExpr::Binary(binary) => {
            1 + expr_display_complexity(&binary.lhs) + expr_display_complexity(&binary.rhs)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            1 + expr_display_complexity(&logical.lhs) + expr_display_complexity(&logical.rhs)
        }
        AstExpr::Call(call) => {
            3 + expr_display_complexity(&call.callee)
                + call.args.iter().map(expr_display_complexity).sum::<usize>()
        }
        AstExpr::MethodCall(call) => {
            3 + expr_display_complexity(&call.receiver)
                + call.args.iter().map(expr_display_complexity).sum::<usize>()
        }
        AstExpr::TableConstructor(table) => {
            2 + table
                .fields
                .iter()
                .map(|field| match field {
                    AstTableField::Array(value) => expr_display_complexity(value),
                    AstTableField::Record(record) => {
                        let key_cost = match &record.key {
                            AstTableKey::Name(_) => 1,
                            AstTableKey::Expr(key) => expr_display_complexity(key),
                        };
                        key_cost + expr_display_complexity(&record.value)
                    }
                })
                .sum::<usize>()
        }
        AstExpr::FunctionExpr(function) => 2 + function.body.stmts.len(),
    }
}
