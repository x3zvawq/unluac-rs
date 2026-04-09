//! 这个文件承载 `locals` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirAssign, HirCapture, HirClosureExpr, HirGlobalRef, HirIf, HirModule, HirProto, HirProtoRef,
    HirReturn,
};
use crate::hir::promotion::ProtoPromotionFacts;

#[test]
fn promotes_temp_alias_chain_into_single_local() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Boolean(true)],
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(1))],
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(1))],
                            values: vec![HirExpr::Integer(41)],
                        }))],
                    },
                    else_block: None,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(1))],
                })),
            ],
        })],
    };

    assert!(super::promote_temps_to_locals_in_proto(
        &mut module.protos[0]
    ));

    assert_eq!(module.protos[0].locals.len(), 1);
    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(local_decl),
            HirStmt::If(if_stmt),
            HirStmt::Return(ret),
        ]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && matches!(local_decl.values.as_slice(), [HirExpr::Boolean(true)])
                && matches!(&if_stmt.cond, HirExpr::LocalRef(LocalId(0)))
                && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
    ));
}

#[test]
fn promotes_if_merge_temp_into_local_decl() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                        name: "cond".to_owned(),
                    }),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(0))],
                            values: vec![HirExpr::Integer(41)],
                        }))],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(0))],
                            values: vec![HirExpr::Integer(7)],
                        }))],
                    }),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        })],
    };

    assert!(super::promote_temps_to_locals_in_proto(
        &mut module.protos[0]
    ));

    assert_eq!(module.protos[0].locals.len(), 1);
    // 后处理把 `local l0; if cond then l0=41 else l0=7 end` 直接折成了值表达式
    assert!(
        matches!(
            module.protos[0].body.stmts.as_slice(),
            [
                HirStmt::LocalDecl(local_decl),
                HirStmt::Return(ret),
            ]
                if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                    && local_decl.values.len() == 1
                    && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
        ),
        "{:#?}",
        module.protos[0].body.stmts
    );
}

#[test]
fn does_not_promote_single_use_numeric_for_header_temps_into_locals() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: crate::parser::ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: crate::parser::ProtoSignature {
                num_params: 1,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![crate::hir::common::ParamId(0)],
            param_debug_hints: Vec::new(),
            locals: vec![LocalId(0)],
            local_debug_hints: Vec::new(),
            upvalues: Vec::new(),
            upvalue_debug_hints: Vec::new(),
            temps: vec![TempId(0), TempId(1), TempId(2)],
            temp_debug_locals: vec![None, None, None],
            body: HirBlock {
                stmts: vec![
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Integer(1)],
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                            op: crate::hir::common::HirUnaryOpKind::Length,
                            expr: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                        }))],
                    })),
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(2))],
                        values: vec![HirExpr::Integer(1)],
                    })),
                    HirStmt::NumericFor(Box::new(crate::hir::common::HirNumericFor {
                        binding: LocalId(0),
                        start: HirExpr::TempRef(TempId(0)),
                        limit: HirExpr::TempRef(TempId(1)),
                        step: HirExpr::TempRef(TempId(2)),
                        body: HirBlock::default(),
                    })),
                ],
            },
            children: Vec::new(),
        }],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert_eq!(module.protos[0].locals.len(), 1);
    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [HirStmt::NumericFor(numeric_for)]
            if matches!(numeric_for.start, HirExpr::Integer(1))
                && matches!(
                    &numeric_for.limit,
                    HirExpr::Unary(unary)
                        if unary.op == crate::hir::common::HirUnaryOpKind::Length
                            && matches!(unary.expr, HirExpr::ParamRef(crate::hir::common::ParamId(0)))
                )
                && matches!(numeric_for.step, HirExpr::Integer(1))
    ));
}

#[test]
fn does_not_promote_self_referential_temp_update_inside_branch() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Temp(TempId(0))],
                    values: vec![HirExpr::Integer(1)],
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(true),
                    then_block: HirBlock {
                        stmts: vec![
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Temp(TempId(0))],
                                values: vec![HirExpr::Binary(Box::new(
                                    crate::hir::common::HirBinaryExpr {
                                        op: crate::hir::common::HirBinaryOpKind::Add,
                                        lhs: HirExpr::TempRef(TempId(0)),
                                        rhs: HirExpr::Integer(1),
                                    },
                                ))],
                            })),
                            HirStmt::Return(Box::new(HirReturn {
                                values: vec![HirExpr::TempRef(TempId(0))],
                            })),
                        ],
                    },
                    else_block: None,
                })),
            ],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [HirStmt::LocalDecl(local_decl), HirStmt::If(if_stmt)]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign), HirStmt::Return(ret)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))])
                        && matches!(assign.values.as_slice(), [HirExpr::Binary(binary)]
                            if matches!(binary.lhs, HirExpr::LocalRef(LocalId(0))))
                        && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))]))
    ));
}

#[test]
fn reuses_existing_local_when_captured_slot_is_rebound_after_capture() {
    let mut proto = proto_with_temps(
        HirProtoRef(0),
        HirBlock {
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
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(2))],
                })),
            ],
        },
        3,
    );

    let facts = ProtoPromotionFacts::for_test(vec![Some(0), Some(1), Some(0)]);
    assert!(super::promote_temps_to_locals_in_proto_with_facts(
        &mut proto, &facts
    ));

    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(local_decl),
            HirStmt::Assign(closure_assign),
            HirStmt::Assign(rebind_assign),
            HirStmt::Return(ret),
        ]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && matches!(local_decl.values.as_slice(), [HirExpr::Integer(1)])
                && matches!(closure_assign.values.as_slice(), [HirExpr::Closure(closure)]
                    if matches!(
                        closure.captures.as_slice(),
                        [HirCapture {
                            value: HirExpr::LocalRef(LocalId(0))
                        }]
                    ))
                && matches!(rebind_assign.targets.as_slice(), [HirLValue::Local(LocalId(0))])
                && matches!(rebind_assign.values.as_slice(), [HirExpr::Integer(2)])
                && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
    ));
}

#[test]
fn reuses_existing_local_for_nested_block_rebind_after_capture() {
    let mut proto = proto_with_temps(
        HirProtoRef(0),
        HirBlock {
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
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::GlobalRef(HirGlobalRef {
                        name: "cond".to_owned(),
                    }),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(TempId(2))],
                            values: vec![HirExpr::Integer(2)],
                        }))],
                    },
                    else_block: None,
                })),
                HirStmt::Return(Box::new(HirReturn {
                    values: vec![HirExpr::TempRef(TempId(0))],
                })),
            ],
        },
        3,
    );

    let facts = ProtoPromotionFacts::for_test(vec![Some(0), Some(1), Some(0)]);
    assert!(super::promote_temps_to_locals_in_proto_with_facts(
        &mut proto, &facts
    ));

    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(local_decl),
            HirStmt::Assign(closure_assign),
            HirStmt::If(if_stmt),
            HirStmt::Return(ret),
        ]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && matches!(closure_assign.values.as_slice(), [HirExpr::Closure(closure)]
                    if matches!(
                        closure.captures.as_slice(),
                        [HirCapture {
                            value: HirExpr::LocalRef(LocalId(0))
                        }]
                    ))
                && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))])
                        && matches!(assign.values.as_slice(), [HirExpr::Integer(2)]))
                && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
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

fn proto_with_temps(id: HirProtoRef, body: HirBlock, temp_count: usize) -> HirProto {
    HirProto {
        id,
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
        temps: (0..temp_count).map(TempId).collect(),
        temp_debug_locals: vec![None; temp_count],
        body,
        children: Vec::new(),
    }
}

// ── branch-value fold 后处理测试 ──────────────────────────────────────

#[test]
fn fold_collapses_branch_assigned_local_into_initializer_expr() {
    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![],
        })),
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
            then_block: HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::String("neg".to_owned())],
                }))],
            },
            else_block: Some(HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::String("pos".to_owned())],
                }))],
            }),
        })),
        HirStmt::Return(Box::new(HirReturn {
            values: vec![HirExpr::LocalRef(LocalId(0))],
        })),
    ];

    assert!(fold_branch_value_locals_in_block(&mut stmts));
    assert!(matches!(
        stmts.as_slice(),
        [HirStmt::LocalDecl(local_decl), HirStmt::Return(_)]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && local_decl.values.len() == 1
    ));
}

#[test]
fn fold_keeps_branch_local_when_cond_reads_binding() {
    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![],
        })),
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
                op: crate::hir::common::HirBinaryOpKind::Eq,
                lhs: HirExpr::LocalRef(LocalId(0)),
                rhs: HirExpr::Nil,
            })),
            then_block: HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::String("neg".to_owned())],
                }))],
            },
            else_block: Some(HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::String("pos".to_owned())],
                }))],
            }),
        })),
    ];

    assert!(!fold_branch_value_locals_in_block(&mut stmts));
    assert_eq!(stmts.len(), 2);
}

#[test]
fn fold_keeps_branch_local_when_decision_cannot_collapse() {
    use crate::hir::common::{HirCallExpr, HirGlobalRef};

    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![],
        })),
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
            then_block: HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::Call(Box::new(HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "truthy_branch".to_owned(),
                        }),
                        args: vec![],
                        multiret: false,
                        method: false,
                        method_name: None,
                    }))],
                }))],
            },
            else_block: Some(HirBlock {
                stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Local(LocalId(0))],
                    values: vec![HirExpr::Call(Box::new(HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "falsy_branch".to_owned(),
                        }),
                        args: vec![],
                        multiret: false,
                        method: false,
                        method_name: None,
                    }))],
                }))],
            }),
        })),
    ];

    assert!(!fold_branch_value_locals_in_block(&mut stmts));
    assert_eq!(stmts.len(), 2);
}

// ── adjacent local-assign merge 后处理测试 ────────────────────────────

#[test]
fn merge_combines_empty_local_decl_with_adjacent_assign() {
    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![],
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(LocalId(0))],
            values: vec![HirExpr::Integer(42)],
        })),
        HirStmt::Return(Box::new(HirReturn {
            values: vec![HirExpr::LocalRef(LocalId(0))],
        })),
    ];

    assert!(merge_adjacent_local_assigns_in_block(&mut stmts));
    assert!(matches!(
        stmts.as_slice(),
        [HirStmt::LocalDecl(local_decl), HirStmt::Return(_)]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && matches!(local_decl.values.as_slice(), [HirExpr::Integer(42)])
    ));
}

#[test]
fn merge_skips_when_assign_target_does_not_match() {
    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![],
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(LocalId(1))],
            values: vec![HirExpr::Integer(42)],
        })),
    ];

    assert!(!merge_adjacent_local_assigns_in_block(&mut stmts));
    assert_eq!(stmts.len(), 2);
}

#[test]
fn merge_skips_already_initialized_local_decl() {
    let mut stmts = vec![
        HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![LocalId(0)],
            values: vec![HirExpr::Nil],
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Local(LocalId(0))],
            values: vec![HirExpr::Integer(42)],
        })),
    ];

    assert!(!merge_adjacent_local_assigns_in_block(&mut stmts));
    assert_eq!(stmts.len(), 2);
}
