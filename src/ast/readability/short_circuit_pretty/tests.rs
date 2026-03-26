//! 这个文件承载 `short_circuit_pretty` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBlock, AstDialectVersion, AstExpr, AstLogicalExpr, AstModule, AstNameRef, AstStmt,
    AstTargetDialect, AstUnaryExpr, AstUnaryOpKind,
};
use crate::hir::ParamId;

use super::super::ReadabilityContext;
use super::{apply, hir_from_ast_expr};

fn and(lhs: AstExpr, rhs: AstExpr) -> AstExpr {
    AstExpr::LogicalAnd(Box::new(AstLogicalExpr { lhs, rhs }))
}

fn or(lhs: AstExpr, rhs: AstExpr) -> AstExpr {
    AstExpr::LogicalOr(Box::new(AstLogicalExpr { lhs, rhs }))
}

fn not(expr: AstExpr) -> AstExpr {
    AstExpr::Unary(Box::new(AstUnaryExpr {
        op: AstUnaryOpKind::Not,
        expr,
    }))
}

#[test]
fn rewrites_ultimate_mess_shape_towards_guarded_source_form() {
    let a = AstExpr::Var(AstNameRef::Param(ParamId(1)));
    let b = AstExpr::Var(AstNameRef::Param(ParamId(2)));
    let c = AstExpr::Var(AstNameRef::Param(ParamId(3)));
    let fallback = and(not(a.clone()), not(b.clone()));
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                values: vec![or(
                    or(
                        and(a.clone(), b.clone()),
                        and(
                            c.clone(),
                            or(b.clone(), or(and(c.clone(), a.clone()), fallback.clone())),
                        ),
                    ),
                    fallback.clone(),
                )],
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
        panic!("expected return");
    };
    let expected = or(
        and(or(and(a.clone(), b.clone()), c.clone()), or(b, and(c, a))),
        fallback,
    );
    assert_eq!(ret.values, vec![expected]);
}

#[test]
fn rejects_impure_index_accesses() {
    let expr = AstExpr::IndexAccess(Box::new(crate::ast::AstIndexAccess {
        base: AstExpr::Var(AstNameRef::Param(ParamId(0))),
        index: AstExpr::Var(AstNameRef::Param(ParamId(1))),
    }));
    assert!(hir_from_ast_expr(&expr).is_none());
}
