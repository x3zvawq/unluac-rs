use crate::hir::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirProto, HirProtoRef, HirReturn, HirStmt,
    HirUnresolvedExpr, TempId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

use super::remove_dead_temp_materializations_in_proto;

#[test]
fn drops_dead_unresolved_temp_assignments() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
                summary: "phi block=#1 reg=r0".into(),
            }))],
        })),
        HirStmt::Return(Box::new(HirReturn { values: Vec::new() })),
    ]);

    assert!(remove_dead_temp_materializations_in_proto(&mut proto));
    assert!(matches!(proto.body.stmts.as_slice(), [HirStmt::Return(_)]));
}

#[test]
fn drops_dead_pure_ref_temp_assignments() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Integer(42)],
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(1))],
            values: vec![HirExpr::LocalRef(crate::hir::LocalId(0))],
        })),
        HirStmt::Return(Box::new(HirReturn { values: Vec::new() })),
    ]);

    assert!(remove_dead_temp_materializations_in_proto(&mut proto));
    assert!(matches!(proto.body.stmts.as_slice(), [HirStmt::Return(_)]));
}

#[test]
fn keeps_dead_temp_assignments_with_side_effects() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Call(Box::new(crate::hir::HirCallExpr {
                callee: HirExpr::GlobalRef(crate::hir::HirGlobalRef {
                    name: "f".into(),
                }),
                args: Vec::new(),
                multiret: false,
                method: false,
                method_name: None,
            }))],
        })),
        HirStmt::Return(Box::new(HirReturn { values: Vec::new() })),
    ]);

    assert!(!remove_dead_temp_materializations_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 2);
}

#[test]
fn keeps_unresolved_temp_assignments_that_are_still_read() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
                summary: "phi block=#1 reg=r0".into(),
            }))],
        })),
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::TempRef(TempId(0)),
            then_block: HirBlock { stmts: Vec::new() },
            else_block: None,
        })),
    ]);

    assert!(!remove_dead_temp_materializations_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 2);
}

fn empty_proto(stmts: Vec<HirStmt>) -> HirProto {
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
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock { stmts },
        children: Vec::new(),
    }
}
