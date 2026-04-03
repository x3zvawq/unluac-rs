//! 这个文件承载 `carried_locals` pass 的局部不变量测试。
//!
//! 我们把测试放到实现文件外，避免 pass 本体被构造 proto 的样板淹没。

use crate::hir::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirReturn, HirStmt, HirUnaryExpr, HirUnaryOpKind, LocalId, TempId,
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
        vec![carried_index, carried_total, next_index, next_total, loop_state],
        vec![
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(carried_index), HirLValue::Temp(carried_total)],
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
                targets: vec![HirLValue::Temp(carried_index), HirLValue::Temp(carried_total)],
                values: vec![HirExpr::TempRef(next_index), HirExpr::TempRef(next_total)],
            })),
            HirStmt::Return(Box::new(HirReturn {
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
fn prunes_redundant_self_assign_stmt_without_handoff_rewrite() {
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
                values: vec![HirExpr::TempRef(temp)],
            })),
        ],
    );

    assert!(collapse_carried_local_handoffs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(_), HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::TempRef(id)] if *id == temp)
    ));
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
        locals,
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps,
        temp_debug_locals: Vec::new(),
        body: HirBlock { stmts },
        children: Vec::new(),
    }
}
