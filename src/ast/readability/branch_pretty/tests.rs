//! 这个文件承载 `branch_pretty` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstDialectVersion, AstExpr, AstLogicalExpr, AstModule, AstNameRef, AstStmt, AstTargetDialect,
    AstUnaryExpr, AstUnaryOpKind,
};
use crate::hir::ParamId;

use super::{super::ReadabilityContext, apply};

#[test]
fn flips_negative_truthy_ternary_to_positive_polarity() {
    let param = ParamId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                values: vec![AstExpr::LogicalOr(Box::new(AstLogicalExpr {
                    lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                        lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Param(param)),
                        })),
                        rhs: AstExpr::String("f".to_owned()),
                    })),
                    rhs: AstExpr::String("t".to_owned()),
                }))],
            }))],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let AstStmt::Return(ret) = &module.body.stmts[0] else {
        panic!("return should remain a return");
    };
    assert_eq!(
        ret.values,
        vec![AstExpr::LogicalOr(Box::new(AstLogicalExpr {
            lhs: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: AstExpr::Var(AstNameRef::Param(param)),
                rhs: AstExpr::String("t".to_owned()),
            })),
            rhs: AstExpr::String("f".to_owned()),
        }))],
    );
}
