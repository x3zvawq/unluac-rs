//! 这个文件承载 `carried_locals` pass 的局部不变量测试。
//!
//! 我们把测试放到实现文件外，避免 pass 本体被构造 proto 的样板淹没。

use crate::hir::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirExpr, HirGoto, HirIf,
    HirLValue, HirLabel, HirLabelId, HirLocalDecl, HirProto, HirProtoRef, HirReturn, HirStmt,
    HirUnaryExpr, HirUnaryOpKind, LocalId, TempId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

use super::collapse_carried_local_handoffs_in_proto;

#[test]
fn collapses_single_temp_handoff_back_into_original_local() {
    let local = LocalId(0);
    let temp = TempId(0);
    let mut proto = empty_proto(
        vec![local],
        vec![temp],
        vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: vec![HirExpr::Integer(1)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: vec![HirExpr::LocalRef(local)],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Lt,
                    lhs: HirExpr::TempRef(temp),
                    rhs: HirExpr::Integer(3),
                })),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(temp)],
                        values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                            op: HirBinaryOpKind::Add,
                            lhs: HirExpr::TempRef(temp),
                            rhs: HirExpr::Integer(1),
                        }))],
                    }))],
                },
                else_block: None,
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(temp)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(_),
            HirStmt::If(if_stmt),
            HirStmt::Return(ret),
        ] if matches!(
            &if_stmt.cond,
            HirExpr::Binary(binary)
                if matches!(binary.lhs, HirExpr::LocalRef(id) if id == local)
        ) && matches!(
            if_stmt.then_block.stmts.as_slice(),
            [HirStmt::Assign(assign)]
                if matches!(assign.targets.as_slice(), [HirLValue::Local(id)] if *id == local)
                    && matches!(
                        assign.values.as_slice(),
                        [HirExpr::Binary(binary)]
                            if matches!(binary.lhs, HirExpr::LocalRef(id) if id == local)
                    )
        ) && matches!(ret.values.as_slice(), [HirExpr::LocalRef(id)] if *id == local)
    ));
}

#[test]
fn keeps_multivalue_call_assignments_intact_when_pruning_self_assigns() {
    let call_result = TempId(0);
    let carried = TempId(1);
    let mut proto = empty_proto(
        Vec::new(),
        vec![call_result, carried],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(call_result), HirLValue::Temp(carried)],
                values: vec![HirExpr::Call(Box::new(HirCallExpr {
                    callee: HirExpr::GlobalRef(crate::hir::common::HirGlobalRef {
                        name: "probe".to_owned(),
                    }),
                    args: vec![HirExpr::String("abc".to_owned())],
                    multiret: true,
                    method: false,
                    method_name: None,
                }))],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(call_result)],
                values: vec![HirExpr::TempRef(call_result)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(call_result), HirExpr::TempRef(carried)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(assign),
            HirStmt::Return(ret),
        ] if matches!(
            assign.targets.as_slice(),
            [HirLValue::Temp(first), HirLValue::Temp(second)]
                if *first == call_result && *second == carried
        ) && matches!(
            assign.values.as_slice(),
            [HirExpr::Call(call)] if call.multiret
        ) && matches!(
            ret.values.as_slice(),
            [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                if *first == call_result && *second == carried
        )
    ));
}

#[test]
fn keeps_handoff_when_original_local_is_still_used_after_seed() {
    let local = LocalId(0);
    let temp = TempId(0);
    let mut proto = empty_proto(
        vec![local],
        vec![temp],
        vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: vec![HirExpr::Integer(1)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: vec![HirExpr::LocalRef(local)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(local)],
                values: vec![HirExpr::Integer(2)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(temp)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(_),
            HirStmt::Assign(seed),
            HirStmt::Assign(_),
            HirStmt::Return(ret),
        ] if matches!(seed.targets.as_slice(), [HirLValue::Temp(id)] if *id == temp)
            && matches!(ret.values.as_slice(), [HirExpr::TempRef(id)] if *id == temp)
    ));
}

#[test]
fn collapses_single_temp_handoff_back_into_original_temp() {
    let seed = TempId(0);
    let carried = TempId(1);
    let mut proto = empty_proto(
        Vec::new(),
        vec![seed, carried],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(seed)],
                values: vec![HirExpr::Integer(1)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::TempRef(seed)],
            })),
            HirStmt::While(Box::new(crate::hir::HirWhile {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Lt,
                    lhs: HirExpr::TempRef(carried),
                    rhs: HirExpr::Integer(3),
                })),
                body: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(carried)],
                        values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                            op: HirBinaryOpKind::Add,
                            lhs: HirExpr::TempRef(carried),
                            rhs: HirExpr::Integer(1),
                        }))],
                    }))],
                },
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(carried)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::While(while_stmt), HirStmt::Return(ret)]
            if matches!(
                &while_stmt.cond,
                HirExpr::Binary(binary)
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == seed)
            ) && matches!(
                while_stmt.body.stmts.as_slice(),
                [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == seed)
                        && matches!(
                            assign.values.as_slice(),
                            [HirExpr::Binary(binary)]
                                if matches!(binary.lhs, HirExpr::TempRef(id) if id == seed)
                        )
            ) && matches!(ret.values.as_slice(), [HirExpr::TempRef(id)] if *id == seed)
    ));
}

#[test]
fn keeps_single_temp_handoff_when_original_temp_is_still_observable() {
    let seed = TempId(0);
    let carried = TempId(1);
    let mut proto = empty_proto(
        Vec::new(),
        vec![seed, carried],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(seed)],
                values: vec![HirExpr::Integer(1)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::TempRef(seed)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(carried), HirExpr::TempRef(seed)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Assign(seed_stmt), HirStmt::Return(ret)]
            if matches!(seed_stmt.targets.as_slice(), [HirLValue::Temp(id)] if *id == carried)
                && matches!(
                    ret.values.as_slice(),
                    [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                        if *first == carried && *second == seed
                )
    ));
}

#[test]
fn collapses_updated_temp_handoff_back_into_carried_temp() {
    let total = TempId(0);
    let carried = TempId(1);
    let next = TempId(2);
    let mut proto = empty_proto(
        Vec::new(),
        vec![total, carried, next],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(total), HirLValue::Temp(carried)],
                values: vec![HirExpr::Int64(0), HirExpr::Int64(0)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(next)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(carried),
                    rhs: HirExpr::Int64(1),
                }))],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Le,
                    lhs: HirExpr::TempRef(next),
                    rhs: HirExpr::Int64(10),
                })),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(total), HirLValue::Temp(carried)],
                        values: vec![
                            HirExpr::Binary(Box::new(HirBinaryExpr {
                                op: HirBinaryOpKind::Add,
                                lhs: HirExpr::TempRef(total),
                                rhs: HirExpr::Binary(Box::new(HirBinaryExpr {
                                    op: HirBinaryOpKind::Mul,
                                    lhs: HirExpr::TempRef(next),
                                    rhs: HirExpr::Int64(2),
                                })),
                            })),
                            HirExpr::TempRef(next),
                        ],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(total), HirLValue::Temp(carried)],
                        values: vec![
                            HirExpr::Binary(Box::new(HirBinaryExpr {
                                op: HirBinaryOpKind::Add,
                                lhs: HirExpr::Binary(Box::new(HirBinaryExpr {
                                    op: HirBinaryOpKind::Add,
                                    lhs: HirExpr::TempRef(total),
                                    rhs: HirExpr::TempRef(next),
                                })),
                                rhs: HirExpr::Int64(5),
                            })),
                            HirExpr::TempRef(next),
                        ],
                    }))],
                }),
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(seed),
            HirStmt::If(if_stmt),
        ] if matches!(seed.targets.as_slice(), [HirLValue::Temp(id)] if *id == carried)
            && matches!(
                seed.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried)
            )
            && matches!(
                if_stmt.cond,
                HirExpr::Binary(ref binary)
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried)
            )
            && matches!(
                if_stmt.then_block.stmts.as_slice(),
                [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == total)
                        && matches!(
                            assign.values.as_slice(),
                            [HirExpr::Binary(binary)]
                                if matches!(
                                    binary.rhs,
                                    HirExpr::Binary(ref rhs)
                                        if matches!(rhs.lhs, HirExpr::TempRef(id) if id == carried)
                                )
                        )
            ) && matches!(
                if_stmt.else_block.as_ref().map(|block| block.stmts.as_slice()),
                Some([HirStmt::Assign(assign)])
                    if matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == total)
                        && matches!(
                            assign.values.as_slice(),
                            [HirExpr::Binary(binary)]
                                if matches!(
                                    binary.lhs,
                                    HirExpr::Binary(ref lhs)
                                        if matches!(lhs.rhs, HirExpr::TempRef(id) if id == carried)
                                )
                        )
            )
    ));
}

#[test]
fn keeps_updated_handoff_when_old_carried_value_stays_observable() {
    let carried = TempId(0);
    let next = TempId(1);
    let mut proto = empty_proto(
        Vec::new(),
        vec![carried, next],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::Int64(0)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(next)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(carried),
                    rhs: HirExpr::Int64(1),
                }))],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(next), HirExpr::TempRef(carried)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(seed),
            HirStmt::Return(ret),
        ] if matches!(seed.targets.as_slice(), [HirLValue::Temp(id)] if *id == next)
            && matches!(
                ret.values.as_slice(),
                [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                    if *first == next && *second == carried
            )
    ));
}

#[test]
fn keeps_updated_handoff_without_direct_writeback() {
    let carried = TempId(0);
    let next = TempId(1);
    let mut proto = empty_proto(
        Vec::new(),
        vec![carried, next],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::Int64(7)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(next)],
                values: vec![HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Neg,
                    expr: HirExpr::TempRef(carried),
                }))],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(next)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(seed),
            HirStmt::Return(ret),
        ] if matches!(seed.targets.as_slice(), [HirLValue::Temp(id)] if *id == next)
            && matches!(ret.values.as_slice(), [HirExpr::TempRef(id)] if *id == next)
    ));
}

#[test]
fn collapses_multi_target_pure_temp_handoff_back_into_original_bindings() {
    let seed_index = TempId(0);
    let seed_total = TempId(1);
    let carried_index = TempId(2);
    let carried_total = TempId(3);
    let mut proto = empty_proto(
        Vec::new(),
        vec![seed_index, seed_total, carried_index, carried_total],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(seed_index), HirLValue::Temp(seed_total)],
                values: vec![HirExpr::Int64(1), HirExpr::Int64(2)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Temp(carried_index),
                    HirLValue::Temp(carried_total),
                ],
                values: vec![HirExpr::TempRef(seed_index), HirExpr::TempRef(seed_total)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Temp(carried_index),
                    HirLValue::Temp(carried_total),
                ],
                values: vec![
                    HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Add,
                        lhs: HirExpr::TempRef(carried_index),
                        rhs: HirExpr::Int64(1),
                    })),
                    HirExpr::TempRef(carried_total),
                ],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![
                    HirExpr::TempRef(carried_index),
                    HirExpr::TempRef(carried_total),
                ],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Assign(assign), HirStmt::Return(ret)]
            if matches!(
                assign.targets.as_slice(),
                [HirLValue::Temp(first)] if *first == seed_index
            ) && matches!(
                assign.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(index) if index == seed_index)
            ) && matches!(
                ret.values.as_slice(),
                [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                    if *first == seed_index && *second == seed_total
            )
    ));
}

#[test]
fn collapses_partial_multi_target_handoff_and_keeps_non_alias_seed_parts() {
    let carried_index = TempId(0);
    let carried_total = TempId(1);
    let next_index = TempId(2);
    let next_total = TempId(3);
    let loop_state = TempId(4);
    let mut proto = empty_proto(
        Vec::new(),
        vec![
            carried_index,
            carried_total,
            next_index,
            next_total,
            loop_state,
        ],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Temp(carried_index),
                    HirLValue::Temp(carried_total),
                ],
                values: vec![HirExpr::Int64(1), HirExpr::Int64(2)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Temp(next_index),
                    HirLValue::Temp(next_total),
                    HirLValue::Temp(loop_state),
                ],
                values: vec![
                    HirExpr::TempRef(carried_index),
                    HirExpr::TempRef(carried_total),
                    HirExpr::Int64(0),
                ],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(loop_state)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(loop_state),
                    rhs: HirExpr::Int64(1),
                }))],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(next_index)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(next_index),
                    rhs: HirExpr::Int64(1),
                }))],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![
                    HirLValue::Temp(carried_index),
                    HirLValue::Temp(carried_total),
                ],
                values: vec![HirExpr::TempRef(next_index), HirExpr::TempRef(next_total)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![
                    HirExpr::TempRef(next_index),
                    HirExpr::TempRef(next_total),
                    HirExpr::TempRef(loop_state),
                ],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(seed),
            HirStmt::Assign(loop_update),
            HirStmt::Assign(index_update),
            HirStmt::Return(ret),
        ] if matches!(
            seed.targets.as_slice(),
            [HirLValue::Temp(id)] if *id == loop_state
        ) && matches!(
            seed.values.as_slice(),
            [HirExpr::Int64(0)]
        ) && matches!(
            loop_update.targets.as_slice(),
            [HirLValue::Temp(id)] if *id == loop_state
        ) && matches!(
            loop_update.values.as_slice(),
            [HirExpr::Binary(binary)]
                if matches!(binary.lhs, HirExpr::TempRef(id) if id == loop_state)
        ) && matches!(
            index_update.targets.as_slice(),
            [HirLValue::Temp(id)] if *id == carried_index
        ) && matches!(
            index_update.values.as_slice(),
            [HirExpr::Binary(binary)]
                if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried_index)
        ) && matches!(
            ret.values.as_slice(),
            [HirExpr::TempRef(first), HirExpr::TempRef(second), HirExpr::TempRef(third)]
                if *first == carried_index && *second == carried_total && *third == loop_state
        )
    ));
}

#[test]
fn keeps_partial_multi_target_handoff_when_original_binding_is_still_read() {
    let carried = TempId(0);
    let next = TempId(1);
    let loop_state = TempId(2);
    let observer = TempId(3);
    let mut proto = empty_proto(
        Vec::new(),
        vec![carried, next, loop_state, observer],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::Int64(7)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(next), HirLValue::Temp(loop_state)],
                values: vec![HirExpr::TempRef(carried), HirExpr::Int64(0)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(observer)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(carried),
                    rhs: HirExpr::TempRef(loop_state),
                }))],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(next), HirExpr::TempRef(observer)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(seed),
            HirStmt::Assign(_),
            HirStmt::Return(ret),
        ] if matches!(
            seed.targets.as_slice(),
            [HirLValue::Temp(first), HirLValue::Temp(second)]
                if *first == next && *second == loop_state
        ) && matches!(
            ret.values.as_slice(),
            [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                if *first == next && *second == observer
        )
    ));
}

#[test]
fn keeps_plain_self_assign_without_handoff_rewrite_context() {
    let temp = TempId(0);
    let mut proto = empty_proto(
        Vec::new(),
        vec![temp],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: vec![HirExpr::Integer(7)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(temp)],
                values: vec![HirExpr::TempRef(temp)],
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(temp)],
            })),
        ],
    );

    assert!(!collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Assign(assign), HirStmt::Return(ret)]
            if matches!(assign.targets.as_slice(), [HirLValue::Temp(id)] if *id == temp)
                && matches!(assign.values.as_slice(), [HirExpr::TempRef(id)] if *id == temp)
                && matches!(ret.values.as_slice(), [HirExpr::TempRef(id)] if *id == temp)
    ));
}

#[test]
fn keeps_preserved_current_value_branch_when_single_handoff_rewrite_creates_self_assign() {
    let local = LocalId(0);
    let carried = TempId(0);
    let mut proto = empty_proto(
        vec![local],
        vec![carried],
        vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: vec![HirExpr::Integer(7)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried)],
                values: vec![HirExpr::LocalRef(local)],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Boolean(true),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(carried)],
                        values: vec![HirExpr::TempRef(carried)],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(carried)],
                        values: vec![HirExpr::Integer(9)],
                    }))],
                }),
            })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(carried)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(local_decl),
            HirStmt::If(if_stmt),
            HirStmt::Return(ret),
        ] if matches!(local_decl.values.as_slice(), [HirExpr::Integer(7)])
            && matches!(
                if_stmt.then_block.stmts.as_slice(),
                [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(id)] if *id == local)
                        && matches!(assign.values.as_slice(), [HirExpr::LocalRef(id)] if *id == local)
            )
            && matches!(
                if_stmt.else_block.as_ref().map(|block| block.stmts.as_slice()),
                Some([HirStmt::Assign(assign)])
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(id)] if *id == local)
                        && matches!(assign.values.as_slice(), [HirExpr::Integer(9)])
            )
            && matches!(ret.values.as_slice(), [HirExpr::LocalRef(id)] if *id == local)
    ));
}

#[test]
fn collapses_goto_mesh_boundary_aliases_back_into_two_carried_slots() {
    let carried_x = TempId(0);
    let carried_y = TempId(1);
    let left_x = TempId(2);
    let left_y = TempId(3);
    let right_x = TempId(4);
    let right_y = TempId(5);
    let mesh_x = TempId(10);
    let mesh_y = TempId(11);
    let l2 = HirLabelId(2);
    let l4 = HirLabelId(4);
    let l5 = HirLabelId(5);

    let mut proto = empty_proto(
        Vec::new(),
        vec![
            carried_x, carried_y, left_x, left_y, right_x, right_y, mesh_x, mesh_y,
        ],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried_x)],
                values: vec![HirExpr::Integer(0)],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried_y)],
                values: vec![HirExpr::Integer(0)],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Eq,
                    lhs: HirExpr::TempRef(carried_x),
                    rhs: HirExpr::Integer(0),
                })),
                then_block: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(mesh_x), HirLValue::Temp(mesh_y)],
                            values: vec![HirExpr::TempRef(carried_x), HirExpr::TempRef(carried_y)],
                        })),
                        HirStmt::Goto(Box::new(HirGoto { target: l2 })),
                    ],
                },
                else_block: None,
            })),
            HirStmt::Goto(Box::new(HirGoto { target: l4 })),
            HirStmt::Label(Box::new(HirLabel { id: l2 })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(left_x)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(mesh_x),
                    rhs: HirExpr::Integer(1),
                }))],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(left_y)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(mesh_y),
                    rhs: HirExpr::Integer(10),
                }))],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Lt,
                    lhs: HirExpr::TempRef(left_x),
                    rhs: HirExpr::Integer(3),
                })),
                then_block: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(carried_x), HirLValue::Temp(carried_y)],
                            values: vec![HirExpr::TempRef(left_x), HirExpr::TempRef(left_y)],
                        })),
                        HirStmt::Goto(Box::new(HirGoto { target: l4 })),
                    ],
                },
                else_block: None,
            })),
            HirStmt::Goto(Box::new(HirGoto { target: l5 })),
            HirStmt::Label(Box::new(HirLabel { id: l4 })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(right_x)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(carried_x),
                    rhs: HirExpr::Integer(2),
                }))],
            })),
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(right_y)],
                values: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Add,
                    lhs: HirExpr::TempRef(carried_y),
                    rhs: HirExpr::Integer(1),
                }))],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Lt,
                    lhs: HirExpr::TempRef(right_y),
                    rhs: HirExpr::Integer(13),
                })),
                then_block: HirBlock {
                    stmts: vec![
                        HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Temp(mesh_x), HirLValue::Temp(mesh_y)],
                            values: vec![HirExpr::TempRef(right_x), HirExpr::TempRef(right_y)],
                        })),
                        HirStmt::Goto(Box::new(HirGoto { target: l2 })),
                    ],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(left_x), HirLValue::Temp(left_y)],
                        values: vec![HirExpr::TempRef(right_x), HirExpr::TempRef(right_y)],
                    }))],
                }),
            })),
            HirStmt::Label(Box::new(HirLabel { id: l5 })),
            HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::TempRef(left_x), HirExpr::TempRef(left_y)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(!proto_mentions_temp(&proto, mesh_x));
    assert!(!proto_mentions_temp(&proto, mesh_y));
    assert!(!proto_mentions_temp(&proto, left_x));
    assert!(!proto_mentions_temp(&proto, left_y));
    assert!(!proto_mentions_temp(&proto, right_x));
    assert!(!proto_mentions_temp(&proto, right_y));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::Assign(_),
            HirStmt::If(first_if),
            HirStmt::Goto(_),
            HirStmt::Label(_),
            HirStmt::Assign(first_update),
            HirStmt::Assign(second_update),
            HirStmt::If(second_if),
            HirStmt::Goto(_),
            HirStmt::Label(_),
            HirStmt::Assign(third_update),
            HirStmt::Assign(fourth_update),
            HirStmt::If(third_if),
            HirStmt::Label(_),
            HirStmt::Return(ret),
        ] if first_if.then_block.stmts.as_slice() == [HirStmt::Goto(Box::new(HirGoto { target: l2 }))]
            && matches!(
                first_update.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried_x)
            ) && matches!(
                second_update.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried_y)
            ) && second_if.then_block.stmts.as_slice() == [HirStmt::Goto(Box::new(HirGoto { target: l4 }))]
            && matches!(
                third_update.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried_x)
            ) && matches!(
                fourth_update.values.as_slice(),
                [HirExpr::Binary(binary)]
                    if matches!(binary.lhs, HirExpr::TempRef(id) if id == carried_y)
            ) && third_if.then_block.stmts.as_slice() == [HirStmt::Goto(Box::new(HirGoto { target: l2 }))]
            && matches!(
                ret.values.as_slice(),
                [HirExpr::TempRef(first), HirExpr::TempRef(second)]
                    if *first == carried_x && *second == carried_y
            )
    ));
}

fn proto_mentions_temp(proto: &HirProto, temp: TempId) -> bool {
    block_mentions_temp(&proto.body, temp)
}

fn block_mentions_temp(block: &HirBlock, temp: TempId) -> bool {
    block
        .stmts
        .iter()
        .any(|stmt| stmt_mentions_temp(stmt, temp))
}

fn stmt_mentions_temp(stmt: &HirStmt, temp: TempId) -> bool {
    match stmt {
        HirStmt::LocalDecl(local_decl) => local_decl
            .values
            .iter()
            .any(|expr| expr_mentions_temp(expr, temp)),
        HirStmt::Assign(assign) => {
            assign
                .targets
                .iter()
                .any(|target| lvalue_mentions_temp(target, temp))
                || assign
                    .values
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::TableSetList(set_list) => {
            expr_mentions_temp(&set_list.base, temp)
                || set_list
                    .values
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
                || set_list
                    .trailing_multivalue
                    .as_ref()
                    .is_some_and(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::ErrNil(err_nil) => expr_mentions_temp(&err_nil.value, temp),
        HirStmt::ToBeClosed(to_be_closed) => expr_mentions_temp(&to_be_closed.value, temp),
        HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
        HirStmt::CallStmt(call_stmt) => {
            expr_mentions_temp(&call_stmt.call.callee, temp)
                || call_stmt
                    .call
                    .args
                    .iter()
                    .any(|expr| expr_mentions_temp(expr, temp))
        }
        HirStmt::Return(ret) => ret.values.iter().any(|expr| expr_mentions_temp(expr, temp)),
        HirStmt::If(if_stmt) => {
            expr_mentions_temp(&if_stmt.cond, temp)
                || block_mentions_temp(&if_stmt.then_block, temp)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(|block| block_mentions_temp(block, temp))
        }
        HirStmt::While(while_stmt) => {
            expr_mentions_temp(&while_stmt.cond, temp)
                || block_mentions_temp(&while_stmt.body, temp)
        }
        HirStmt::Repeat(repeat_stmt) => {
            block_mentions_temp(&repeat_stmt.body, temp)
                || expr_mentions_temp(&repeat_stmt.cond, temp)
        }
        HirStmt::NumericFor(numeric_for) => {
            expr_mentions_temp(&numeric_for.start, temp)
                || expr_mentions_temp(&numeric_for.limit, temp)
                || expr_mentions_temp(&numeric_for.step, temp)
                || block_mentions_temp(&numeric_for.body, temp)
        }
        HirStmt::GenericFor(generic_for) => {
            generic_for
                .iterator
                .iter()
                .any(|expr| expr_mentions_temp(expr, temp))
                || block_mentions_temp(&generic_for.body, temp)
        }
        HirStmt::Block(block) => block_mentions_temp(block, temp),
        HirStmt::Unstructured(unstructured) => block_mentions_temp(&unstructured.body, temp),
    }
}

fn lvalue_mentions_temp(lvalue: &HirLValue, temp: TempId) -> bool {
    match lvalue {
        HirLValue::Temp(id) => *id == temp,
        HirLValue::TableAccess(access) => {
            expr_mentions_temp(&access.base, temp) || expr_mentions_temp(&access.key, temp)
        }
        HirLValue::Local(_) | HirLValue::Upvalue(_) | HirLValue::Global(_) => false,
    }
}

fn expr_mentions_temp(expr: &HirExpr, temp: TempId) -> bool {
    match expr {
        HirExpr::TempRef(id) => *id == temp,
        HirExpr::TableAccess(access) => {
            expr_mentions_temp(&access.base, temp) || expr_mentions_temp(&access.key, temp)
        }
        HirExpr::Unary(unary) => expr_mentions_temp(&unary.expr, temp),
        HirExpr::Binary(binary) => {
            expr_mentions_temp(&binary.lhs, temp) || expr_mentions_temp(&binary.rhs, temp)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_mentions_temp(&logical.lhs, temp) || expr_mentions_temp(&logical.rhs, temp)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_mentions_temp(&node.test, temp)
                || matches!(
                    &node.truthy,
                    crate::hir::common::HirDecisionTarget::Expr(expr)
                        if expr_mentions_temp(expr, temp)
                )
                || matches!(
                    &node.falsy,
                    crate::hir::common::HirDecisionTarget::Expr(expr)
                        if expr_mentions_temp(expr, temp)
                )
        }),
        HirExpr::Call(call) => {
            expr_mentions_temp(&call.callee, temp)
                || call.args.iter().any(|arg| expr_mentions_temp(arg, temp))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::hir::common::HirTableField::Array(expr) => expr_mentions_temp(expr, temp),
                crate::hir::common::HirTableField::Record(field) => {
                    matches!(
                        &field.key,
                        crate::hir::common::HirTableKey::Expr(expr)
                            if expr_mentions_temp(expr, temp)
                    ) || expr_mentions_temp(&field.value, temp)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_mentions_temp(expr, temp))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_mentions_temp(&capture.value, temp)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn empty_proto(locals: Vec<LocalId>, temps: Vec<TempId>, stmts: Vec<HirStmt>) -> HirProto {
    HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 0,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals,
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps,
        temp_debug_locals: Vec::new(),
        body: HirBlock { stmts },
        children: Vec::new(),
    }
}
