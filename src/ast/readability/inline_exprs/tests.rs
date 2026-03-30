//! 这个文件承载 `inline_exprs` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::common::{
    AstCallExpr, AstFieldAccess, AstGlobalName, AstIndexAccess, AstLocalBinding, AstMethodCallExpr,
    AstRecordField, AstReturn, AstTableConstructor, AstTableField, AstTableKey,
};
use crate::ast::{
    AstBinaryExpr, AstBinaryOpKind, AstCallKind, AstExpr, AstLValue, AstLocalAttr, AstModule,
    AstNameRef, AstStmt, AstTargetDialect, AstUnaryExpr, AstUnaryOpKind,
};
use crate::hir::{LocalId, TempId};

use crate::readability::ReadabilityOptions;

use super::{ReadabilityContext, apply};

#[test]
fn inlines_safe_expr_into_single_return_within_threshold() {
    let temp = TempId(0);
    let local = LocalId(0);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Temp(temp),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::Unary(Box::new(AstUnaryExpr {
                        op: AstUnaryOpKind::Not,
                        expr: AstExpr::Var(AstNameRef::Local(local)),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                })),
            ],
        },
    };

    let module = crate::ast::make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::Unary(Box::new(AstUnaryExpr {
                op: AstUnaryOpKind::Not,
                expr: AstExpr::Var(AstNameRef::Local(local)),
            }))],
        }))]
    );
}

#[test]
fn does_not_inline_call_arg_when_expr_exceeds_arg_threshold() {
    let temp = TempId(0);
    let lhs = LocalId(0);
    let rhs = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::LogicalAnd(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Local(lhs)),
                        })),
                        rhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Local(rhs)),
                        })),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                        args: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                    })),
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                args_inline_max_complexity: 3,
                ..ReadabilityOptions::default()
            },
        }
    ));
}

#[test]
fn inlines_temp_into_index_slot_with_custom_threshold() {
    let temp = TempId(0);
    let base = LocalId(0);
    let lhs = LocalId(1);
    let rhs = LocalId(2);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Not,
                            expr: AstExpr::Var(AstNameRef::Local(lhs)),
                        })),
                        rhs: AstExpr::Var(AstNameRef::Local(rhs)),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(base)),
                        index: AstExpr::Var(AstNameRef::Temp(temp)),
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                index_inline_max_complexity: 4,
                ..ReadabilityOptions::default()
            },
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                base: AstExpr::Var(AstNameRef::Local(base)),
                index: AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                    lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                        op: AstUnaryOpKind::Not,
                        expr: AstExpr::Var(AstNameRef::Local(lhs)),
                    })),
                    rhs: AstExpr::Var(AstNameRef::Local(rhs)),
                })),
            }))],
        }))]
    );
}

#[test]
fn does_not_inline_expr_with_potential_runtime_behavior_changes() {
    let temp = TempId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        receiver: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        method: "push".to_owned(),
                        args: vec![AstExpr::Var(AstNameRef::Temp(temp))],
                    })),
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                args_inline_max_complexity: usize::MAX,
                ..ReadabilityOptions::default()
            },
        }
    ));
}

#[test]
fn inlines_named_field_access_base_into_adjacent_index_assign() {
    let root = LocalId(0);
    let first = TempId(0);
    let second = TempId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(first))],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(root)),
                        field: "branches".to_owned(),
                    }))],
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(second))],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Temp(first)),
                        index: AstExpr::String("picked".to_owned()),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Temp(second)),
                        field: "value".to_owned(),
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                access_base_inline_max_complexity: 5,
                ..ReadabilityOptions::default()
            },
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![
            AstStmt::Assign(Box::new(crate::ast::AstAssign {
                targets: vec![AstLValue::Name(AstNameRef::Temp(second))],
                values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(root)),
                        field: "branches".to_owned(),
                    })),
                    index: AstExpr::String("picked".to_owned()),
                }))],
            })),
            AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Temp(second)),
                    field: "value".to_owned(),
                }))],
            })),
        ]
    );
}

#[test]
fn reruns_field_access_sugar_after_inlining_string_key_alias_in_lvalue() {
    let table = LocalId(0);
    let key = LocalId(1);
    let current = LocalId(2);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(key),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("n".to_owned())],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(current),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        field: "n".to_owned(),
                    }))],
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Var(AstNameRef::Local(key)),
                    }))],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(current)),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
            ],
        },
    };

    let module = crate::ast::make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );

    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Assign(Box::new(crate::ast::AstAssign {
            targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                base: AstExpr::Var(AstNameRef::Local(table)),
                field: "n".to_owned(),
            }))],
            values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Add,
                lhs: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Local(table)),
                    field: "n".to_owned(),
                })),
                rhs: AstExpr::Integer(1),
            }))],
        }))]
    );
}

#[test]
fn collapses_mechanical_lookup_chain_into_terminal_local_decl() {
    let table = LocalId(0);
    let item = LocalId(1);
    let scaled = LocalId(2);
    let tail = LocalId(3);
    let before = LocalId(4);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(scaled),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Mul,
                        lhs: AstExpr::Var(AstNameRef::Local(item)),
                        rhs: AstExpr::Integer(10),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(tail),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(table)),
                            field: "n".to_owned(),
                        })),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(before),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(scaled)),
                        rhs: AstExpr::Var(AstNameRef::Local(tail)),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(before))],
                })),
            ],
        },
    };

    let module = crate::ast::make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );

    assert_eq!(
        module.body.stmts,
        vec![
            AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(before),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Add,
                    lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Mul,
                        lhs: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(table)),
                            index: AstExpr::Integer(1),
                        })),
                        rhs: AstExpr::Integer(10),
                    })),
                    rhs: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(table)),
                            field: "n".to_owned(),
                        })),
                    })),
                }))],
            })),
            AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::Var(AstNameRef::Local(before))],
            })),
        ]
    );
}

#[test]
fn collapses_lookup_only_run_into_index_assign() {
    let table = LocalId(0);
    let index = LocalId(1);
    let item1 = LocalId(2);
    let item2 = LocalId(3);
    let head = LocalId(4);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(index),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        field: "n".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item1),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item2),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(2),
                    }))],
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Var(AstNameRef::Local(index)),
                    }))],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Add,
                            lhs: AstExpr::Var(AstNameRef::Local(item1)),
                            rhs: AstExpr::Var(AstNameRef::Local(item2)),
                        })),
                        rhs: AstExpr::Var(AstNameRef::Local(head)),
                    }))],
                })),
            ],
        },
    };

    let module = crate::ast::make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );

    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Assign(Box::new(crate::ast::AstAssign {
            targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                base: AstExpr::Var(AstNameRef::Local(table)),
                index: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Local(table)),
                    field: "n".to_owned(),
                })),
            }))],
            values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Add,
                lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Add,
                    lhs: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(1),
                    })),
                    rhs: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(2),
                    })),
                })),
                rhs: AstExpr::Var(AstNameRef::Local(head)),
            }))],
        }))]
    );
}

#[test]
fn collapses_mechanical_alias_run_into_nested_assignment_expr() {
    let table = LocalId(0);
    let first = LocalId(1);
    let second = LocalId(2);
    let index = LocalId(3);
    let left = LocalId(4);
    let middle = LocalId(5);
    let right = LocalId(6);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(index),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                            op: AstUnaryOpKind::Length,
                            expr: AstExpr::Var(AstNameRef::Local(table)),
                        })),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(left),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(first)),
                        field: "name".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(middle),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("+".to_owned())],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(right),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(second)),
                        field: "name".to_owned(),
                    }))],
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Var(AstNameRef::Local(index)),
                    }))],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Concat,
                        lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Concat,
                            lhs: AstExpr::Var(AstNameRef::Local(left)),
                            rhs: AstExpr::Var(AstNameRef::Local(middle)),
                        })),
                        rhs: AstExpr::Var(AstNameRef::Local(right)),
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua54),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Assign(Box::new(crate::ast::AstAssign {
            targets: vec![AstLValue::IndexAccess(Box::new(AstIndexAccess {
                base: AstExpr::Var(AstNameRef::Local(table)),
                index: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Add,
                    lhs: AstExpr::Unary(Box::new(AstUnaryExpr {
                        op: AstUnaryOpKind::Length,
                        expr: AstExpr::Var(AstNameRef::Local(table)),
                    })),
                    rhs: AstExpr::Integer(1),
                })),
            }))],
            values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Concat,
                lhs: AstExpr::Binary(Box::new(AstBinaryExpr {
                    op: AstBinaryOpKind::Concat,
                    lhs: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(first)),
                        field: "name".to_owned(),
                    })),
                    rhs: AstExpr::String("+".to_owned()),
                })),
                rhs: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Local(second)),
                    field: "name".to_owned(),
                })),
            }))],
        }))]
    );
}

#[test]
fn does_not_collapse_stage_locals_into_flat_return_values() {
    let first = LocalId(0);
    let second = LocalId(1);
    let lhs = LocalId(2);
    let rhs = LocalId(3);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(first),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(lhs)),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(second),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(rhs)),
                        rhs: AstExpr::Integer(2),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![
                        AstExpr::Var(AstNameRef::Local(first)),
                        AstExpr::Var(AstNameRef::Local(second)),
                    ],
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua54),
            options: ReadabilityOptions::default(),
        }
    ));
}

#[test]
fn does_not_collapse_lookup_stage_chain_into_nested_return_access() {
    let root = LocalId(0);
    let branch = LocalId(1);
    let item = LocalId(2);
    let selector = LocalId(3);
    let index = LocalId(4);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(branch),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(root)),
                            field: "branches".to_owned(),
                        })),
                        index: AstExpr::Var(AstNameRef::Local(selector)),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(branch)),
                            field: "items".to_owned(),
                        })),
                        index: AstExpr::Var(AstNameRef::Local(index)),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(item)),
                        field: "value".to_owned(),
                    }))],
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua54),
            options: ReadabilityOptions::default(),
        }
    ));
}

#[test]
fn inlines_single_use_local_alias_into_call_callee_with_access_base_threshold() {
    let alias = LocalId(0);
    let table_arg = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "concat".to_owned(),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(alias)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(table_arg)),
                            AstExpr::String(",".to_owned()),
                        ],
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                access_base_inline_max_complexity: 5,
                ..ReadabilityOptions::default()
            },
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "table".to_owned(),
                    })),
                    field: "concat".to_owned(),
                })),
                args: vec![
                    AstExpr::Var(AstNameRef::Local(table_arg)),
                    AstExpr::String(",".to_owned()),
                ],
            }))],
        }))]
    );
}

#[test]
fn does_not_inline_local_alias_into_plain_return_value() {
    let alias = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "concat".to_owned(),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(alias))],
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions {
                access_base_inline_max_complexity: 5,
                return_inline_max_complexity: usize::MAX,
                ..ReadabilityOptions::default()
            },
        }
    ));
}

#[test]
fn inlines_recovered_constructor_alias_into_direct_return_value() {
    let alias = LocalId(0);
    let values = LocalId(1);
    let table_expr = AstExpr::TableConstructor(Box::new(AstTableConstructor {
        fields: vec![
            AstTableField::Record(AstRecordField {
                key: AstTableKey::Name("first".to_owned()),
                value: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(AstNameRef::Local(values)),
                    index: AstExpr::Integer(1),
                })),
            }),
            AstTableField::Record(AstRecordField {
                key: AstTableKey::Name("last".to_owned()),
                value: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(AstNameRef::Local(values)),
                    index: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(values)),
                        field: "n".to_owned(),
                    })),
                })),
            }),
            AstTableField::Record(AstRecordField {
                key: AstTableKey::Name("n".to_owned()),
                value: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Local(values)),
                    field: "n".to_owned(),
                })),
            }),
        ],
    }));
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![table_expr.clone()],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(alias))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![table_expr],
        }))]
    );
}

#[test]
fn inlines_recovered_call_alias_inside_nested_return_value_expr() {
    let alias = LocalId(0);
    let arg = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "step".to_owned(),
                        })),
                        args: vec![AstExpr::Var(AstNameRef::Local(arg))],
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(alias)),
                        rhs: AstExpr::Integer(1),
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Add,
                lhs: AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "step".to_owned(),
                    })),
                    args: vec![AstExpr::Var(AstNameRef::Local(arg))],
                })),
                rhs: AstExpr::Integer(1),
            }))],
        }))]
    );
}

#[test]
fn inlines_recovered_call_alias_inside_comparison_operand() {
    let alias = LocalId(0);
    let arg = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "fn".to_owned(),
                        })),
                        args: vec![AstExpr::Var(AstNameRef::Local(arg))],
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String("self".to_owned()),
                            AstExpr::Binary(Box::new(AstBinaryExpr {
                                op: AstBinaryOpKind::Eq,
                                lhs: AstExpr::Var(AstNameRef::Local(alias)),
                                rhs: AstExpr::Var(AstNameRef::Local(arg)),
                            })),
                        ],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: "print".to_owned(),
                })),
                args: vec![
                    AstExpr::String("self".to_owned()),
                    AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Eq,
                        lhs: AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                text: "fn".to_owned(),
                            })),
                            args: vec![AstExpr::Var(AstNameRef::Local(arg))],
                        })),
                        rhs: AstExpr::Var(AstNameRef::Local(arg)),
                    })),
                ],
            })),
        }))]
    );
}

#[test]
fn does_not_inline_debug_hinted_call_alias_inside_comparison_operand() {
    let alias = LocalId(0);
    let arg = LocalId(1);
    let original = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::DebugHinted,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "fn".to_owned(),
                        })),
                        args: vec![AstExpr::Var(AstNameRef::Local(arg))],
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String("self".to_owned()),
                            AstExpr::Binary(Box::new(AstBinaryExpr {
                                op: AstBinaryOpKind::Eq,
                                lhs: AstExpr::Var(AstNameRef::Local(alias)),
                                rhs: AstExpr::Var(AstNameRef::Local(arg)),
                            })),
                        ],
                    })),
                })),
            ],
        },
    };
    let mut module = original.clone();

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(module, original);
}

#[test]
fn collapses_adjacent_local_alias_run_into_final_call_stmt() {
    let print_alias = LocalId(0);
    let label_alias = LocalId(1);
    let stage_alias = LocalId(2);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(print_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "print".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(label_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("nested-closure".to_owned())],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(stage_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(3))),
                        args: vec![AstExpr::Integer(1)],
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(print_alias)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(label_alias)),
                            AstExpr::Call(Box::new(AstCallExpr {
                                callee: AstExpr::Var(AstNameRef::Local(stage_alias)),
                                args: vec![AstExpr::Integer(2)],
                            })),
                        ],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                    text: "print".to_owned(),
                })),
                args: vec![
                    AstExpr::String("nested-closure".to_owned()),
                    AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(LocalId(3))),
                            args: vec![AstExpr::Integer(1)],
                        })),
                        args: vec![AstExpr::Integer(2)],
                    })),
                ],
            })),
        }))]
    );
}

#[test]
fn does_not_collapse_single_call_chain_alias_before_final_call_stmt() {
    let stage1 = LocalId(0);
    let stage2 = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(stage1),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                        args: vec![AstExpr::Integer(2)],
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(stage2),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(stage1)),
                        args: vec![AstExpr::Integer(3)],
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String("nested-closure".to_owned()),
                            AstExpr::Call(Box::new(AstCallExpr {
                                callee: AstExpr::Var(AstNameRef::Local(stage2)),
                                args: vec![AstExpr::Integer(4)],
                            })),
                        ],
                    })),
                })),
            ],
        },
    };

    let before = module.clone();
    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));
    assert_eq!(module.body.stmts, before.body.stmts);
}

#[test]
fn collapses_indexed_call_alias_run_back_into_final_print_args() {
    let table_local = LocalId(0);
    let item1 = LocalId(1);
    let value1 = LocalId(2);
    let item2 = LocalId(3);
    let value2 = LocalId(4);
    let item3 = LocalId(5);
    let value3 = LocalId(6);
    let item4 = LocalId(7);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(table_local),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(20))),
                        args: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item1),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(value1),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(item1)),
                        args: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item2),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(3),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(value2),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(item2)),
                        args: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item3),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(6),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(value3),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(item3)),
                        args: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item4),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(7),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String("repeat-closure".to_owned()),
                            AstExpr::Var(AstNameRef::Local(value1)),
                            AstExpr::Var(AstNameRef::Local(value2)),
                            AstExpr::Var(AstNameRef::Local(value3)),
                            AstExpr::Binary(Box::new(AstBinaryExpr {
                                op: AstBinaryOpKind::Eq,
                                lhs: AstExpr::Var(AstNameRef::Local(item4)),
                                rhs: AstExpr::Nil,
                            })),
                        ],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    assert_eq!(
        module.body.stmts,
        vec![
            AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(table_local),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Local(LocalId(20))),
                    args: Vec::new(),
                }))],
            })),
            AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "print".to_owned(),
                    })),
                    args: vec![
                        AstExpr::String("repeat-closure".to_owned()),
                        AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                                base: AstExpr::Var(AstNameRef::Local(table_local)),
                                index: AstExpr::Integer(1),
                            })),
                            args: Vec::new(),
                        })),
                        AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                                base: AstExpr::Var(AstNameRef::Local(table_local)),
                                index: AstExpr::Integer(3),
                            })),
                            args: Vec::new(),
                        })),
                        AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                                base: AstExpr::Var(AstNameRef::Local(table_local)),
                                index: AstExpr::Integer(6),
                            })),
                            args: Vec::new(),
                        })),
                        AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Eq,
                            lhs: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                                base: AstExpr::Var(AstNameRef::Local(table_local)),
                                index: AstExpr::Integer(7),
                            })),
                            rhs: AstExpr::Nil,
                        })),
                    ],
                })),
            })),
        ]
    );
}

#[test]
fn inlines_local_alias_inside_function_body_after_other_locals() {
    let func = crate::hir::HirProtoRef(1);
    let table_local = LocalId(0);
    let helper = LocalId(1);
    let ok = LocalId(2);
    let concat = LocalId(3);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(LocalId(10)),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::FunctionExpr(Box::new(
                    crate::ast::AstFunctionExpr {
                        function: func,
                        params: vec![crate::hir::ParamId(0), crate::hir::ParamId(1)],
                        is_vararg: false,
                        named_vararg: None,
                        body: crate::ast::AstBlock {
                            stmts: vec![
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(table_local),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::TableConstructor(Box::new(
                                        crate::ast::AstTableConstructor { fields: vec![] },
                                    ))],
                                })),
                                AstStmt::LocalFunctionDecl(Box::new(
                                    crate::ast::AstLocalFunctionDecl {
                                        name: crate::ast::AstBindingRef::Local(helper),
                                        func: crate::ast::AstFunctionExpr {
                                            function: crate::hir::HirProtoRef(2),
                                            params: vec![
                                                crate::hir::ParamId(0),
                                                crate::hir::ParamId(1),
                                            ],
                                            is_vararg: false,
                                            named_vararg: None,
                                            body: crate::ast::AstBlock {
                                                stmts: vec![AstStmt::Return(Box::new(AstReturn {
                                                    values: vec![AstExpr::Var(AstNameRef::Param(
                                                        crate::hir::ParamId(1),
                                                    ))],
                                                }))],
                                            },
                                            captured_bindings: Default::default(),
                                        },
                                    },
                                )),
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(ok),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::Boolean(true)],
                                })),
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(concat),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                                            text: "table".to_owned(),
                                        })),
                                        field: "concat".to_owned(),
                                    }))],
                                })),
                                AstStmt::Return(Box::new(AstReturn {
                                    values: vec![
                                        AstExpr::Var(AstNameRef::Local(ok)),
                                        AstExpr::Call(Box::new(AstCallExpr {
                                            callee: AstExpr::Var(AstNameRef::Local(concat)),
                                            args: vec![
                                                AstExpr::Var(AstNameRef::Local(table_local)),
                                                AstExpr::String(",".to_owned()),
                                            ],
                                        })),
                                    ],
                                })),
                            ],
                        },
                        captured_bindings: Default::default(),
                    },
                ))],
            }))],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected function wrapper local");
    };
    let AstExpr::FunctionExpr(function) = &local_decl.values[0] else {
        panic!("expected function expr");
    };
    assert!(matches!(
        function.body.stmts.as_slice(),
        [
            _,
            _,
            _,
            AstStmt::Return(ret)
        ] if matches!(
            ret.values.as_slice(),
            [
                AstExpr::Var(AstNameRef::Local(ok_name)),
                AstExpr::Call(call)
            ] if *ok_name == ok && matches!(&call.callee, AstExpr::FieldAccess(_))
        )
    ));
}

#[test]
fn collapses_lookup_alias_run_back_into_final_print_args() {
    let table_local = LocalId(0);
    let item1 = LocalId(1);
    let item2 = LocalId(2);
    let item3 = LocalId(3);
    let field_a = LocalId(4);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(table_local),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(20))),
                        args: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item1),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item2),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(2),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item3),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        index: AstExpr::Integer(3),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(field_a),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(table_local)),
                        field: "a".to_owned(),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String("crazy-table".to_owned()),
                            AstExpr::Var(AstNameRef::Local(item1)),
                            AstExpr::Var(AstNameRef::Local(item2)),
                            AstExpr::Var(AstNameRef::Local(item3)),
                            AstExpr::Var(AstNameRef::Local(field_a)),
                        ],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    assert_eq!(
        module.body.stmts,
        vec![
            AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(table_local),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Local(LocalId(20))),
                    args: Vec::new(),
                }))],
            })),
            AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "print".to_owned(),
                    })),
                    args: vec![
                        AstExpr::String("crazy-table".to_owned()),
                        AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(table_local)),
                            index: AstExpr::Integer(1),
                        })),
                        AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(table_local)),
                            index: AstExpr::Integer(2),
                        })),
                        AstExpr::IndexAccess(Box::new(AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(table_local)),
                            index: AstExpr::Integer(3),
                        })),
                        AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(table_local)),
                            field: "a".to_owned(),
                        })),
                    ],
                })),
            })),
        ]
    );
}

#[test]
fn inlines_lookup_alias_inside_nested_return_value() {
    let branch = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(branch),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "obj".to_owned(),
                        })),
                        field: "branch".to_owned(),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(branch)),
                        index: AstExpr::Integer(4),
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    assert_eq!(
        module.body.stmts,
        vec![AstStmt::Return(Box::new(AstReturn {
            values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "obj".to_owned(),
                    })),
                    field: "branch".to_owned(),
                })),
                index: AstExpr::Integer(4),
            }))],
        }))]
    );
}

#[test]
fn folds_access_base_alias_into_adjacent_local_alias_initializer_chain() {
    let unpack_alias = LocalId(0);
    let fn_alias = LocalId(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(unpack_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "unpack".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(fn_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Var(AstNameRef::Local(unpack_alias)),
                        rhs: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "unpack".to_owned(),
                        })),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(fn_alias))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    assert_eq!(
        module.body.stmts,
        vec![
            AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(fn_alias),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                    lhs: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "unpack".to_owned(),
                    })),
                    rhs: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "unpack".to_owned(),
                    })),
                }))],
            })),
            AstStmt::Return(Box::new(AstReturn {
                values: vec![AstExpr::Var(AstNameRef::Local(fn_alias))],
            })),
        ]
    );
}

#[test]
fn does_not_count_shadowed_nested_function_locals_as_outer_alias_uses() {
    let outer_alias = LocalId(0);
    let func = crate::hir::HirProtoRef(1);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(outer_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "table".to_owned(),
                        })),
                        field: "unpack".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Var(AstNameRef::Local(outer_alias)),
                        rhs: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "unpack".to_owned(),
                        })),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(LocalId(2)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(
                        crate::ast::AstFunctionExpr {
                            function: func,
                            params: Vec::new(),
                            is_vararg: false,
                            named_vararg: None,
                            body: crate::ast::AstBlock {
                                stmts: vec![AstStmt::LocalDecl(Box::new(
                                    crate::ast::AstLocalDecl {
                                        bindings: vec![AstLocalBinding {
                                            id: crate::ast::AstBindingRef::Local(LocalId(0)),
                                            attr: AstLocalAttr::None,
                                            origin: crate::ast::AstLocalOrigin::Recovered,
                                        }],
                                        values: vec![AstExpr::Integer(1)],
                                    },
                                ))],
                            },
                            captured_bindings: Default::default(),
                        },
                    ))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        }
    ));

    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected alias initializer to fold into second local");
    };
    assert_eq!(
        local_decl.bindings[0].id,
        crate::ast::AstBindingRef::Local(LocalId(1))
    );
}

#[test]
fn inlines_lookup_alias_into_adjacent_multi_return_call_callee() {
    let funcs = LocalId(0);
    let callee = LocalId(1);
    let first = LocalId(2);
    let second = LocalId(3);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(callee),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(funcs)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![
                        AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(first),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                        AstLocalBinding {
                            id: crate::ast::AstBindingRef::Local(second),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                    ],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(callee)),
                        args: vec![AstExpr::Integer(2)],
                    }))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        }
    ));

    assert_eq!(
        module.body.stmts,
        vec![AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
            bindings: vec![
                AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(first),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                },
                AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(second),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                },
            ],
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(AstNameRef::Local(funcs)),
                    index: AstExpr::Integer(1),
                })),
                args: vec![AstExpr::Integer(2)],
            }))],
        }))]
    );
}
