//! 这个文件承载 `loop_header_merge` 模块的局部不变量测试。

use super::ReadabilityContext;
use crate::ast::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstLValue, AstLocalBinding,
    AstLocalOrigin, AstNameRef, AstRepeat,
};
use crate::ast::{
    AstBlock, AstExpr, AstLocalAttr, AstLocalDecl, AstModule, AstNumericFor, AstStmt,
    AstTargetDialect,
};
use crate::hir::{LocalId, TempId};

fn apply_loop_header_merge(module: &AstModule) -> AstModule {
    let mut module = module.clone();
    super::apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: Default::default(),
        },
    );
    module
}

#[test]
fn collapses_recovered_local_run_into_numeric_for_header() {
    let start = LocalId(0);
    let limit = LocalId(1);
    let step = LocalId(2);
    let module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                local_decl(start, AstExpr::Integer(1)),
                local_decl(limit, AstExpr::Integer(5)),
                local_decl(step, AstExpr::Integer(1)),
                AstStmt::NumericFor(Box::new(AstNumericFor {
                    binding: AstBindingRef::Local(LocalId(10)),
                    start: AstExpr::Var(AstNameRef::Local(start)),
                    limit: AstExpr::Var(AstNameRef::Local(limit)),
                    step: AstExpr::Var(AstNameRef::Local(step)),
                    body: AstBlock { stmts: Vec::new() },
                })),
            ],
        },
    };

    let module = apply_loop_header_merge(&module);
    assert_eq!(module.body.stmts.len(), 1);
    let AstStmt::NumericFor(numeric_for) = &module.body.stmts[0] else {
        panic!("expected numeric-for after collapsing header aliases");
    };
    assert_eq!(numeric_for.start, AstExpr::Integer(1));
    assert_eq!(numeric_for.limit, AstExpr::Integer(5));
    assert_eq!(numeric_for.step, AstExpr::Integer(1));
}

#[test]
fn does_not_collapse_when_header_alias_is_used_after_loop() {
    let start = LocalId(0);
    let limit = LocalId(1);
    let step = LocalId(2);
    let module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                local_decl(start, AstExpr::Integer(1)),
                local_decl(limit, AstExpr::Integer(5)),
                local_decl(step, AstExpr::Integer(1)),
                AstStmt::NumericFor(Box::new(AstNumericFor {
                    binding: AstBindingRef::Local(LocalId(10)),
                    start: AstExpr::Var(AstNameRef::Local(start)),
                    limit: AstExpr::Var(AstNameRef::Local(limit)),
                    step: AstExpr::Var(AstNameRef::Local(step)),
                    body: AstBlock { stmts: Vec::new() },
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(limit))],
                })),
            ],
        },
    };

    let module = apply_loop_header_merge(&module);
    assert_eq!(module.body.stmts.len(), 3);
    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected remaining header alias local");
    };
    assert_eq!(local_decl.bindings[0].id, AstBindingRef::Local(limit));
    let AstStmt::Return(ret) = &module.body.stmts[2] else {
        panic!("expected trailing return");
    };
    assert_eq!(ret.values, vec![AstExpr::Var(AstNameRef::Local(limit))]);
}

#[test]
fn collapses_repeat_tail_temp_into_until_condition() {
    let temp = TempId(0);
    let carried = LocalId(0);
    let limit = LocalId(1);
    let module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Temp(temp),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![],
                })),
                AstStmt::Repeat(Box::new(AstRepeat {
                    body: AstBlock {
                        stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                            values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                                op: AstBinaryOpKind::Add,
                                lhs: AstExpr::Var(AstNameRef::Local(limit)),
                                rhs: AstExpr::Integer(10),
                            }))],
                        }))],
                    },
                    cond: AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Lt,
                        lhs: AstExpr::Var(AstNameRef::Temp(temp)),
                        rhs: AstExpr::Var(AstNameRef::Local(carried)),
                    })),
                })),
            ],
        },
    };

    let module = apply_loop_header_merge(&module);
    let AstStmt::Repeat(repeat_stmt) = &module.body.stmts[1] else {
        panic!("expected repeat statement to remain");
    };
    assert!(repeat_stmt.body.stmts.is_empty());
    assert_eq!(
        repeat_stmt.cond,
        AstExpr::Binary(Box::new(AstBinaryExpr {
            op: AstBinaryOpKind::Lt,
            lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Add,
                lhs: AstExpr::Var(AstNameRef::Local(limit)),
                rhs: AstExpr::Integer(10),
            })),
            rhs: AstExpr::Var(AstNameRef::Local(carried)),
        }))
    );
}

fn local_decl(binding: LocalId, value: AstExpr) -> AstStmt {
    AstStmt::LocalDecl(Box::new(AstLocalDecl {
        bindings: vec![AstLocalBinding {
            id: AstBindingRef::Local(binding),
            attr: AstLocalAttr::None,
            origin: AstLocalOrigin::Recovered,
        }],
        values: vec![value],
    }))
}
