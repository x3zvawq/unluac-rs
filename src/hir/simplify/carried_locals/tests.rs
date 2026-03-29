//! 这个文件承载 `carried_locals` pass 的局部不变量测试。
//!
//! 我们把测试放到实现文件外，避免 pass 本体被构造 proto 的样板淹没。

use crate::hir::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl,
    HirProto, HirProtoRef, HirReturn, HirStmt, LocalId, TempId,
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
