//! 这个文件承载 `branch_pretty` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBinaryExpr, AstBinaryOpKind, AstBlock, AstCallExpr, AstCallKind, AstCallStmt,
    AstDialectVersion, AstExpr, AstIf, AstLocalBinding, AstLocalDecl, AstLogicalExpr, AstModule,
    AstNameRef, AstReturn, AstStmt, AstTargetDialect, AstUnaryExpr, AstUnaryOpKind,
};
use crate::hir::{LocalId, ParamId};

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

#[test]
fn lifts_terminating_return_else_branch_into_guard_return_shape() {
    let param = ParamId(0);
    let acc = ParamId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Eq,
                    lhs: AstExpr::Var(AstNameRef::Param(param)),
                    rhs: AstExpr::Integer(0),
                })),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Var(AstNameRef::Param(acc))],
                    }))],
                },
                else_block: Some(AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn {
                        values: vec![AstExpr::Integer(1)],
                    }))],
                }),
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

    assert_eq!(module.body.stmts.len(), 2);
    let AstStmt::If(if_stmt) = &module.body.stmts[0] else {
        panic!("expected guard if");
    };
    assert!(if_stmt.else_block.is_none(), "{if_stmt:?}");
    let AstStmt::Return(ret) = &module.body.stmts[1] else {
        panic!("expected lifted tail return");
    };
    assert_eq!(ret.values, vec![AstExpr::Integer(1)]);
}

#[test]
fn lifts_terminating_else_branch_by_negating_condition() {
    let param = ParamId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Lt,
                    lhs: AstExpr::Var(AstNameRef::Param(param)),
                    rhs: AstExpr::Integer(10),
                })),
                then_block: AstBlock {
                    stmts: vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                        call: AstCallKind::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Param(param)),
                            args: Vec::new(),
                        })),
                    }))],
                },
                else_block: Some(AstBlock {
                    stmts: vec![AstStmt::Break],
                }),
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

    assert_eq!(module.body.stmts.len(), 2);
    let AstStmt::If(if_stmt) = &module.body.stmts[0] else {
        panic!("expected lifted guard if");
    };
    assert!(if_stmt.else_block.is_none(), "{if_stmt:?}");
    assert_eq!(
        if_stmt.cond,
        AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Le,
            lhs: AstExpr::Integer(10),
            rhs: AstExpr::Var(AstNameRef::Param(param)),
        }))
    );
    let AstStmt::CallStmt(call_stmt) = &module.body.stmts[1] else {
        panic!("expected lifted then tail");
    };
    assert_eq!(
        call_stmt.call,
        AstCallKind::Call(Box::new(AstCallExpr {
            callee: AstExpr::Var(AstNameRef::Param(param)),
            args: Vec::new(),
        }))
    );
}

#[test]
fn wraps_lifted_tail_with_do_block_when_branch_declares_local() {
    let local = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn { values: Vec::new() }))],
                },
                else_block: Some(AstBlock {
                    stmts: vec![
                        AstStmt::LocalDecl(Box::new(AstLocalDecl {
                            bindings: vec![AstLocalBinding {
                                id: crate::ast::AstBindingRef::Local(local),
                                attr: crate::ast::AstLocalAttr::None,
                                origin: crate::ast::AstLocalOrigin::Recovered,
                            }],
                            values: vec![AstExpr::Integer(1)],
                        })),
                        AstStmt::Return(Box::new(AstReturn {
                            values: vec![AstExpr::Var(AstNameRef::Local(local))],
                        })),
                    ],
                }),
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

    assert_eq!(module.body.stmts.len(), 2);
    assert!(matches!(module.body.stmts[1], AstStmt::DoBlock(_)));
}

#[test]
fn collapses_nested_guard_if_chain_into_single_short_circuit_condition() {
    let lhs = ParamId(0);
    let rhs = ParamId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Lt,
                    lhs: AstExpr::Integer(10),
                    rhs: AstExpr::Var(AstNameRef::Param(lhs)),
                })),
                then_block: AstBlock {
                    stmts: vec![AstStmt::If(Box::new(AstIf {
                        cond: AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Eq,
                            lhs: AstExpr::Var(AstNameRef::Param(rhs)),
                            rhs: AstExpr::Integer(0),
                        })),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::Break],
                        },
                        else_block: None,
                    }))],
                },
                else_block: None,
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

    assert_eq!(
        module.body.stmts,
        vec![AstStmt::If(Box::new(AstIf {
            cond: AstExpr::LogicalAnd(Box::new(AstLogicalExpr {
                lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Lt,
                    lhs: AstExpr::Integer(10),
                    rhs: AstExpr::Var(AstNameRef::Param(lhs)),
                })),
                rhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Eq,
                    lhs: AstExpr::Var(AstNameRef::Param(rhs)),
                    rhs: AstExpr::Integer(0),
                })),
            })),
            then_block: AstBlock {
                stmts: vec![AstStmt::Break],
            },
            else_block: None,
        }))]
    );
}
