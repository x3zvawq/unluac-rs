//! 这个文件承载 `temp_inline` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCallStmt, HirCapture, HirClosureExpr,
    HirGenericFor, HirGlobalRef, HirIf, HirModule, HirNumericFor, HirProtoRef, HirReturn,
    HirUnaryExpr, HirUnaryOpKind, LocalId, ParamId,
};
use crate::hir::promotion::ProtoPromotionFacts;

#[test]
fn removes_immediate_temp_forwarding_chain() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: vec![HirExpr::Integer(41)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(1))],
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
            HirStmt::CallStmt(Box::new(HirCallStmt {
                call: HirCallExpr {
                    callee: HirExpr::GlobalRef(HirGlobalRef {
                        name: "print".to_owned(),
                    }),
                    args: vec![HirExpr::TempRef(TempId(1))],
                    multiret: false,
                    method: false,
                    method_name: None,
                },
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
        ],
    });

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    assert_eq!(proto.body.stmts.len(), 3);
    assert!(matches!(
        &proto.body.stmts[1],
        HirStmt::CallStmt(call_stmt)
            if matches!(call_stmt.call.args.as_slice(), [HirExpr::TempRef(TempId(0))])
    ));
}

#[test]
fn does_not_inline_across_control_barrier() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: vec![HirExpr::Integer(1)],
            })),
            HirStmt::Label(Box::new(crate::hir::common::HirLabel {
                id: crate::hir::common::HirLabelId(0),
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
        ],
    });

    inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
    );
    assert_eq!(proto.body.stmts.len(), 3);
}

#[test]
fn collapses_terminal_forwarding_chain_in_single_proto_pass() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: vec![HirExpr::Integer(7)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(1))],
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TempRef(TempId(1))],
            })),
        ],
    });

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Integer(7)])
    ));
}

#[test]
fn does_not_inline_temp_into_nested_return_base_access() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: vec![HirExpr::TableAccess(Box::new(
                    crate::hir::common::HirTableAccess {
                        base: HirExpr::GlobalRef(HirGlobalRef {
                            name: "root".to_owned(),
                        }),
                        key: HirExpr::String("items".to_owned()),
                    },
                ))],
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TableAccess(Box::new(
                    crate::hir::common::HirTableAccess {
                        base: HirExpr::TempRef(TempId(0)),
                        key: HirExpr::String("value".to_owned()),
                    },
                ))],
            })),
        ],
    });

    inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
    );
    println!("{proto:#?}");
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Return(ret)]
            if matches!(
                ret.values.as_slice(),
                [HirExpr::TableAccess(access)]
                    if matches!(access.base, HirExpr::TempRef(TempId(0)))
            )
    ));
}

#[test]
fn does_not_inline_self_referential_loop_state_update_into_following_call() {
    let mut proto = HirProto {
        locals: vec![LocalId(0)],
        local_debug_hints: Vec::new(),
        ..dummy_proto(HirBlock {
            stmts: vec![HirStmt::NumericFor(Box::new(HirNumericFor {
                binding: LocalId(0),
                start: HirExpr::Integer(1),
                limit: HirExpr::Integer(2),
                step: HirExpr::Integer(1),
                body: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(0))],
                            values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                                op: HirBinaryOpKind::Add,
                                lhs: HirExpr::TempRef(TempId(0)),
                                rhs: HirExpr::Integer(1),
                            }))],
                        })),
                        HirStmt::CallStmt(Box::new(HirCallStmt {
                            call: HirCallExpr {
                                callee: HirExpr::GlobalRef(HirGlobalRef {
                                    name: "yield".to_owned(),
                                }),
                                args: vec![HirExpr::TempRef(TempId(0))],
                                multiret: false,
                                method: false,
                                method_name: None,
                            },
                        })),
                    ],
                },
            }))],
        })
    };

    inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
    );
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::NumericFor(numeric_for)]
            if matches!(
                numeric_for.body.stmts.as_slice(),
                [HirStmt::Assign(assign), HirStmt::CallStmt(call_stmt)]
                    if matches!(
                        assign.targets.as_slice(),
                        [HirLValue::Temp(TempId(0))]
                    )
                        && matches!(
                            assign.values.as_slice(),
                            [HirExpr::Binary(binary)]
                                if binary.op == HirBinaryOpKind::Add
                                    && matches!(binary.lhs, HirExpr::TempRef(TempId(0)))
                                    && matches!(binary.rhs, HirExpr::Integer(1))
                        )
                        && matches!(
                            call_stmt.call.args.as_slice(),
                            [HirExpr::TempRef(TempId(0))]
                        )
            )
    ));
}

#[test]
fn does_not_inline_debug_hinted_generic_for_loop_state_update() {
    let mut proto = HirProto {
        locals: vec![LocalId(0), LocalId(1), LocalId(2), LocalId(3)],
        temps: vec![TempId(0)],
        temp_debug_locals: vec![Some("value".to_owned())],
        ..dummy_proto(HirBlock {
            stmts: vec![HirStmt::GenericFor(Box::new(HirGenericFor {
                bindings: vec![LocalId(0), LocalId(1)],
                iterator: vec![
                    HirExpr::GlobalRef(HirGlobalRef {
                        name: "ipairs".to_owned(),
                    }),
                    HirExpr::LocalRef(LocalId(2)),
                ],
                body: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(0))],
                            values: vec![HirExpr::Call(Box::new(HirCallExpr {
                                callee: HirExpr::GlobalRef(HirGlobalRef {
                                    name: "step".to_owned(),
                                }),
                                args: vec![
                                    HirExpr::LocalRef(LocalId(3)),
                                    HirExpr::LocalRef(LocalId(1)),
                                    HirExpr::LocalRef(LocalId(0)),
                                ],
                                multiret: false,
                                method: false,
                                method_name: None,
                            }))],
                        })),
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(LocalId(3))],
                            values: vec![HirExpr::TempRef(TempId(0))],
                        })),
                    ],
                },
            }))],
        })
    };

    inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
    );
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::GenericFor(generic_for)]
            if matches!(
                generic_for.body.stmts.as_slice(),
                [HirStmt::Assign(assign), HirStmt::Assign(update)]
                    if matches!(
                        assign.targets.as_slice(),
                        [HirLValue::Temp(TempId(0))]
                    )
                        && matches!(
                            update.targets.as_slice(),
                            [HirLValue::Local(LocalId(3))]
                        )
                        && matches!(
                            update.values.as_slice(),
                            [HirExpr::TempRef(TempId(0))]
                        )
            )
    ));
}

#[test]
fn does_not_inline_generic_for_carried_state_update_from_loop_prefix() {
    let mut proto = HirProto {
        locals: vec![LocalId(0), LocalId(1)],
        temps: (0..10).map(TempId).collect(),
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(0)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(9))],
                    values: vec![HirExpr::Integer(4)],
                })),
                HirStmt::GenericFor(Box::new(HirGenericFor {
                    bindings: vec![LocalId(0), LocalId(1)],
                    iterator: vec![
                        HirExpr::TempRef(TempId(1)),
                        HirExpr::TempRef(TempId(2)),
                        HirExpr::TempRef(TempId(3)),
                    ],
                    body: HirBlock {
                        stmts: vec![
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(4))],
                                values: vec![HirExpr::TempRef(TempId(9))],
                            })),
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(5))],
                                values: vec![HirExpr::LocalRef(LocalId(1))],
                            })),
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(6))],
                                values: vec![HirExpr::LocalRef(LocalId(0))],
                            })),
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(9))],
                                values: vec![HirExpr::Call(Box::new(HirCallExpr {
                                    callee: HirExpr::GlobalRef(HirGlobalRef {
                                        name: "step".to_owned(),
                                    }),
                                    args: vec![
                                        HirExpr::TempRef(TempId(4)),
                                        HirExpr::TempRef(TempId(5)),
                                        HirExpr::TempRef(TempId(6)),
                                    ],
                                    multiret: false,
                                    method: false,
                                    method_name: None,
                                }))],
                            })),
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::TableAccess(Box::new(
                                    crate::hir::common::HirTableAccess {
                                        base: HirExpr::TempRef(TempId(0)),
                                        key: HirExpr::Integer(1),
                                    },
                                ))],
                                values: vec![HirExpr::TempRef(TempId(9))],
                            })),
                        ],
                    },
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(9))],
                })),
            ],
        })
    };

    inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
    );
    let generic_for = proto
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            HirStmt::GenericFor(generic_for) => Some(generic_for.as_ref()),
            _ => None,
        })
        .expect("test fixture should still contain a generic-for");
    assert!(generic_for.body.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Assign(assign)
                if matches!(assign.targets.as_slice(), [HirLValue::Temp(TempId(9))])
                    && matches!(assign.values.as_slice(), [HirExpr::Call(_)])
        )
    }));
    assert!(generic_for.body.stmts.iter().any(|stmt| {
        matches!(
            stmt,
            HirStmt::Assign(assign)
                if matches!(assign.targets.as_slice(), [HirLValue::TableAccess(_)])
                    && matches!(assign.values.as_slice(), [HirExpr::TempRef(TempId(9))])
        )
    }));
    assert!(matches!(
        proto.body.stmts.last(),
        Some(HirStmt::Return(ret)) if matches!(ret.values.as_slice(), [HirExpr::TempRef(TempId(9))])
    ));
}

#[test]
fn inlines_named_field_access_base_into_immediate_assign_when_threshold_allows() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2), TempId(3)],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                            key: HirExpr::String("branches".to_owned()),
                        },
                    ))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::TempRef(TempId(0)),
                            key: HirExpr::String("picked".to_owned()),
                        },
                    ))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::TempRef(TempId(1)),
                            key: HirExpr::String("value".to_owned()),
                        },
                    ))],
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions {
            access_base_inline_max_complexity: 5,
            ..crate::readability::ReadabilityOptions::default()
        }
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(assign), HirStmt::Return(ret)]
            if matches!(
                assign.values.as_slice(),
                [HirExpr::TableAccess(access)]
                    if matches!(&access.base, HirExpr::TableAccess(inner)
                        if matches!(inner.base, HirExpr::ParamRef(_))
                            && matches!(inner.key, HirExpr::String(ref value) if value == "branches"))
                        && matches!(access.key, HirExpr::String(ref value) if value == "picked")
            )
                && matches!(
                    ret.values.as_slice(),
                    [HirExpr::TableAccess(access)]
                        if matches!(access.base, HirExpr::TempRef(TempId(1)))
                            && matches!(access.key, HirExpr::String(ref value) if value == "value")
                )
    ));
}

#[test]
fn does_not_chain_access_base_inline_past_single_segment() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2)],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                            key: HirExpr::String("branches".to_owned()),
                        },
                    ))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::TempRef(TempId(0)),
                            key: HirExpr::String("picked".to_owned()),
                        },
                    ))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(2))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::TempRef(TempId(1)),
                            key: HirExpr::String("value".to_owned()),
                        },
                    ))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(2))],
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions {
            access_base_inline_max_complexity: usize::MAX,
            ..crate::readability::ReadabilityOptions::default()
        }
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(assign), HirStmt::Return(ret)]
            if matches!(
                assign.values.as_slice(),
                [HirExpr::TableAccess(access)]
                    if matches!(&access.base, HirExpr::TableAccess(inner)
                        if matches!(inner.base, HirExpr::ParamRef(_))
                            && matches!(inner.key, HirExpr::String(ref value) if value == "branches"))
                        && matches!(access.key, HirExpr::String(ref value) if value == "picked")
            )
                && matches!(
                    ret.values.as_slice(),
                    [HirExpr::TableAccess(access)]
                        if matches!(access.base, HirExpr::TempRef(TempId(1)))
                            && matches!(access.key, HirExpr::String(ref value) if value == "value")
                )
    ));
}

#[test]
fn still_inlines_temp_directly_in_index_context() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2)],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::String("picked".to_owned())],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::GlobalRef(HirGlobalRef {
                                name: "root".to_owned(),
                            }),
                            key: HirExpr::TempRef(TempId(0)),
                        },
                    ))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(1))],
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions {
            index_inline_max_complexity: 5,
            ..crate::readability::ReadabilityOptions::default()
        }
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(
                ret.values.as_slice(),
                [HirExpr::TableAccess(access)]
                    if matches!(access.base, HirExpr::GlobalRef(_))
                        && matches!(access.key, HirExpr::String(ref value) if value == "picked")
            )
    ));
}

#[test]
fn preserves_index_context_through_pure_wrapper_layers() {
    let mut proto = HirProto {
        upvalues: vec![crate::hir::common::UpvalueId(0)],
        upvalue_debug_hints: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::UpvalueRef(crate::hir::common::UpvalueId(0))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                        op: crate::hir::common::HirUnaryOpKind::Length,
                        expr: HirExpr::TempRef(TempId(0)),
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::TableAccess(Box::new(
                        crate::hir::common::HirTableAccess {
                            base: HirExpr::TempRef(TempId(0)),
                            key: HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
                                op: crate::hir::common::HirBinaryOpKind::Add,
                                lhs: HirExpr::TempRef(TempId(1)),
                                rhs: HirExpr::Integer(1),
                            })),
                        },
                    ))],
                    values: vec![HirExpr::ParamRef(crate::hir::common::ParamId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::ParamRef(crate::hir::common::ParamId(1))],
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    let [upvalue_assign, assign_stmt, return_stmt] = proto.body.stmts.as_slice() else {
        panic!(
            "expected temp forward + assign + return after inline: {:?}",
            proto.body.stmts
        );
    };
    let HirStmt::Assign(upvalue_assign) = upvalue_assign else {
        panic!("expected first stmt to remain temp forward: {upvalue_assign:?}");
    };
    assert!(matches!(
        upvalue_assign.targets.as_slice(),
        [HirLValue::Temp(TempId(0))]
    ));
    assert!(matches!(
        upvalue_assign.values.as_slice(),
        [HirExpr::UpvalueRef(crate::hir::common::UpvalueId(0))]
    ));
    let HirStmt::Assign(assign) = assign_stmt else {
        panic!("expected first stmt to be assign: {assign_stmt:?}");
    };
    let HirStmt::Return(ret) = return_stmt else {
        panic!("expected second stmt to be return: {return_stmt:?}");
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        panic!("expected single table access target: {:?}", assign.targets);
    };
    assert!(matches!(access.base, HirExpr::TempRef(TempId(0))));
    let HirExpr::Binary(binary) = &access.key else {
        panic!("expected binary key after inline: {:?}", access.key);
    };
    assert_eq!(binary.op, crate::hir::common::HirBinaryOpKind::Add);
    let HirExpr::Unary(unary) = &binary.lhs else {
        panic!("expected unary lhs after inline: {:?}", binary.lhs);
    };
    assert_eq!(unary.op, crate::hir::common::HirUnaryOpKind::Length);
    assert!(matches!(&unary.expr, HirExpr::TempRef(TempId(0))));
    assert!(matches!(&binary.rhs, HirExpr::Integer(1)));
    assert!(matches!(
        assign.values.as_slice(),
        [HirExpr::ParamRef(crate::hir::common::ParamId(0))]
    ));
    assert!(matches!(
        ret.values.as_slice(),
        [HirExpr::ParamRef(crate::hir::common::ParamId(1))]
    ));
}

#[test]
fn does_not_inline_direct_return_when_temp_has_debug_local_hint() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: vec![HirExpr::Integer(41)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
        ],
    });
    proto.temp_debug_locals[0] = Some("x".to_owned());

    assert!(!inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions {
            return_inline_max_complexity: usize::MAX,
            index_inline_max_complexity: usize::MAX,
            args_inline_max_complexity: usize::MAX,
            access_base_inline_max_complexity: usize::MAX,
        }
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::TempRef(TempId(0))])
    ));
}

#[test]
fn does_not_inline_temp_into_closure_capture() {
    let mut proto = HirProto {
        temps: vec![TempId(0)],
        temp_debug_locals: vec![None],
        local_debug_hints: Vec::new(),
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::ParamRef(ParamId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: HirProtoRef(1),
                        captures: vec![HirCapture {
                            value: HirExpr::TempRef(TempId(0)),
                        }],
                    }))],
                })),
            ],
        })
    };
    proto.signature.num_params = 1;
    proto.params = vec![ParamId(0)];

    assert!(!inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(assign), HirStmt::Return(ret)]
            if matches!(
                assign.values.as_slice(),
                [HirExpr::ParamRef(ParamId(0))]
            )
                && matches!(
                    ret.values.as_slice(),
                    [HirExpr::Closure(closure)]
                        if matches!(closure.captures.as_slice(), [HirCapture { value: HirExpr::TempRef(TempId(0)) }])
                )
    ));
}

#[test]
fn does_not_inline_rebind_after_captured_home_slot_writeback() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2)],
        temp_debug_locals: vec![None, None, None],
        local_debug_hints: Vec::new(),
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: HirProtoRef(1),
                        captures: vec![HirCapture {
                            value: HirExpr::TempRef(TempId(0)),
                        }],
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(2))],
                    values: vec![HirExpr::Integer(2)],
                })),
                HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "print".to_owned(),
                        }),
                        args: vec![HirExpr::TempRef(TempId(2))],
                        multiret: false,
                        method: false,
                        method_name: None,
                    },
                })),
            ],
        })
    };
    let facts = ProtoPromotionFacts::for_test(vec![Some(0), Some(1), Some(0)]);

    assert!(!inline_temps_in_proto_with_facts(
        &mut proto,
        crate::readability::ReadabilityOptions::default(),
        &facts,
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Assign(_), HirStmt::Assign(assign), HirStmt::CallStmt(call_stmt)]
            if matches!(
                assign.targets.as_slice(),
                [HirLValue::Temp(TempId(2))]
            ) && matches!(
                assign.values.as_slice(),
                [HirExpr::Integer(2)]
            ) && matches!(
                call_stmt.call.args.as_slice(),
                [HirExpr::TempRef(TempId(2))]
            )
    ));
}

fn dummy_proto(body: HirBlock) -> HirProto {
    HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: crate::parser::ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: crate::parser::ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        body,
        children: Vec::new(),
    }
}

#[test]
fn simplify_module_runs_until_fixed_point() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(7)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(1))],
                })),
            ],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
        crate::generate::GenerateMode::Strict, crate::ast::AstDialectVersion::Lua51,
        );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Integer(7)])
    ));
}

#[test]
fn inlines_single_use_temps_into_numeric_for_header() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2)],
        locals: vec![LocalId(0)],
        local_debug_hints: Vec::new(),
        temp_debug_locals: vec![None, None, None],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::ParamRef(ParamId(0))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(2))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::NumericFor(Box::new(HirNumericFor {
                    binding: LocalId(0),
                    start: HirExpr::TempRef(TempId(0)),
                    limit: HirExpr::TempRef(TempId(1)),
                    step: HirExpr::TempRef(TempId(2)),
                    body: HirBlock::default(),
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::NumericFor(numeric_for)]
            if matches!(numeric_for.start, HirExpr::Integer(1))
                && matches!(numeric_for.limit, HirExpr::ParamRef(ParamId(0)))
                && matches!(numeric_for.step, HirExpr::Integer(1))
    ));
}

#[test]
fn inlines_small_nested_exprs_into_condition_and_assign_value() {
    let mut proto = HirProto {
        temps: vec![TempId(0), TempId(1), TempId(2)],
        temp_debug_locals: vec![None, None, None],
        ..dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Add,
                        lhs: HirExpr::ParamRef(ParamId(0)),
                        rhs: HirExpr::ParamRef(ParamId(1)),
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Mod,
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::Integer(2),
                    }))],
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Unary(Box::new(HirUnaryExpr {
                        op: HirUnaryOpKind::Not,
                        expr: HirExpr::Binary(Box::new(HirBinaryExpr {
                            op: HirBinaryOpKind::Eq,
                            lhs: HirExpr::TempRef(TempId(1)),
                            rhs: HirExpr::Integer(0),
                        })),
                    })),
                    then_block: HirBlock::default(),
                    else_block: None,
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(2))],
                    values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Mul,
                        lhs: HirExpr::ParamRef(ParamId(0)),
                        rhs: HirExpr::Integer(10),
                    }))],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Global(HirGlobalRef {
                        name: "value".to_owned(),
                    })],
                    values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Add,
                        lhs: HirExpr::TempRef(TempId(2)),
                        rhs: HirExpr::ParamRef(ParamId(1)),
                    }))],
                })),
            ],
        })
    };

    assert!(inline_temps_in_proto(
        &mut proto,
        crate::readability::ReadabilityOptions::default()
    ));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::If(if_stmt), HirStmt::Assign(assign)]
            if matches!(
                &if_stmt.cond,
                HirExpr::Unary(unary)
                    if unary.op == HirUnaryOpKind::Not
                        && matches!(
                            &unary.expr,
                            HirExpr::Binary(eq)
                                if eq.op == HirBinaryOpKind::Eq
                                    && matches!(
                                        &eq.lhs,
                                        HirExpr::Binary(mod_expr)
                                            if mod_expr.op == HirBinaryOpKind::Mod
                                                && matches!(
                                                    &mod_expr.lhs,
                                                    HirExpr::Binary(add_expr)
                                                        if add_expr.op == HirBinaryOpKind::Add
                                                            && matches!(add_expr.lhs, HirExpr::ParamRef(ParamId(0)))
                                                            && matches!(add_expr.rhs, HirExpr::ParamRef(ParamId(1)))
                                                )
                                                && matches!(mod_expr.rhs, HirExpr::Integer(2))
                                    )
                                    && matches!(eq.rhs, HirExpr::Integer(0))
                        )
            )
                && matches!(
                    assign.values.as_slice(),
                    [HirExpr::Binary(add_expr)]
                        if add_expr.op == HirBinaryOpKind::Add
                            && matches!(
                                &add_expr.lhs,
                                HirExpr::Binary(mul_expr)
                                    if mul_expr.op == HirBinaryOpKind::Mul
                                        && matches!(mul_expr.lhs, HirExpr::ParamRef(ParamId(0)))
                                        && matches!(mul_expr.rhs, HirExpr::Integer(10))
                            )
                            && matches!(add_expr.rhs, HirExpr::ParamRef(ParamId(1)))
                )
    ));
}
