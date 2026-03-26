//! 这个文件承载 `inline_exprs` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::common::{
    AstCallExpr, AstFieldAccess, AstGlobalName, AstIndexAccess, AstLocalBinding, AstMethodCallExpr,
    AstReturn,
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
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Global(AstGlobalName {
                        text: "print".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(label_alias),
                        attr: AstLocalAttr::None,
                    }],
                    values: vec![AstExpr::String("nested-closure".to_owned())],
                })),
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(stage_alias),
                        attr: AstLocalAttr::None,
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
                }],
                values: vec![AstExpr::FunctionExpr(Box::new(
                    crate::ast::AstFunctionExpr {
                        function: func,
                        params: vec![crate::hir::ParamId(0), crate::hir::ParamId(1)],
                        is_vararg: false,
                        body: crate::ast::AstBlock {
                            stmts: vec![
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(table_local),
                                        attr: AstLocalAttr::None,
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
                                            body: crate::ast::AstBlock {
                                                stmts: vec![AstStmt::Return(Box::new(AstReturn {
                                                    values: vec![AstExpr::Var(AstNameRef::Param(
                                                        crate::hir::ParamId(1),
                                                    ))],
                                                }))],
                                            },
                                        },
                                    },
                                )),
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(ok),
                                        attr: AstLocalAttr::None,
                                    }],
                                    values: vec![AstExpr::Boolean(true)],
                                })),
                                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(concat),
                                        attr: AstLocalAttr::None,
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
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(
                        crate::ast::AstFunctionExpr {
                            function: func,
                            params: Vec::new(),
                            is_vararg: false,
                            body: crate::ast::AstBlock {
                                stmts: vec![AstStmt::LocalDecl(Box::new(
                                    crate::ast::AstLocalDecl {
                                        bindings: vec![AstLocalBinding {
                                            id: crate::ast::AstBindingRef::Local(LocalId(0)),
                                            attr: AstLocalAttr::None,
                                        }],
                                        values: vec![AstExpr::Integer(1)],
                                    },
                                ))],
                            },
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
