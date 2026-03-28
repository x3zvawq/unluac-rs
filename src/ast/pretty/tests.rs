use crate::ast::{AstBinaryExpr, AstBinaryOpKind, AstExpr, AstUnaryExpr, AstUnaryOpKind};

use super::preferred_negated_relational_render;

#[test]
fn prefers_not_equal_render_for_negated_equality() {
    let unary = AstUnaryExpr {
        op: AstUnaryOpKind::Not,
        expr: AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Eq,
            lhs: AstExpr::String("lhs".to_owned()),
            rhs: AstExpr::Nil,
        })),
    };

    let preferred =
        preferred_negated_relational_render(&unary).expect("negated equality should render as ~=");
    assert_eq!(preferred.op_text, "~=");
    assert_eq!(preferred.lhs, &AstExpr::String("lhs".to_owned()));
    assert_eq!(preferred.rhs, &AstExpr::Nil);
}
