use crate::hir::{
    HirAssign, HirBlock, HirClose, HirExpr, HirIf, HirLValue, HirProto, HirProtoRef, HirReturn,
    HirStmt, HirToBeClosed, TempId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

use super::materialize_tbc_close_scopes_in_proto;

#[test]
fn materializes_simple_tbc_region_into_block() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Integer(1)],
        })),
        HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: 2,
            value: HirExpr::TempRef(TempId(0)),
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(1))],
            values: vec![HirExpr::Integer(2)],
        })),
        HirStmt::Close(Box::new(HirClose { from_reg: 2 })),
        HirStmt::Return(Box::new(crate::hir::HirReturn { values: Vec::new() })),
    ]);

    assert!(materialize_tbc_close_scopes_in_proto(&mut proto));

    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Block(_), HirStmt::Return(_)]
    ));
    let HirStmt::Block(block) = &proto.body.stmts[0] else {
        panic!("expected materialized block");
    };
    assert!(matches!(
        block.stmts.as_slice(),
        [
            HirStmt::Assign(_),
            HirStmt::ToBeClosed(_),
            HirStmt::Assign(_)
        ]
    ));
}

#[test]
fn removes_all_matching_close_markers_inside_nested_tbc_scope() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Integer(1)],
        })),
        HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: 3,
            value: HirExpr::TempRef(TempId(0)),
        })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(1))],
            values: vec![HirExpr::Integer(2)],
        })),
        HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: 4,
            value: HirExpr::TempRef(TempId(1)),
        })),
        HirStmt::Close(Box::new(HirClose { from_reg: 4 })),
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(2))],
            values: vec![HirExpr::Integer(3)],
        })),
        HirStmt::Close(Box::new(HirClose { from_reg: 4 })),
        HirStmt::Close(Box::new(HirClose { from_reg: 3 })),
    ]);

    assert!(materialize_tbc_close_scopes_in_proto(&mut proto));

    let HirStmt::Block(outer) = &proto.body.stmts[0] else {
        panic!("expected outer block");
    };
    assert!(
        outer
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, HirStmt::Close(_))),
        "outer scope should not retain matching close markers"
    );
}

#[test]
fn materializes_scope_when_close_lives_in_child_branch() {
    let mut proto = empty_proto(vec![
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(0))],
            values: vec![HirExpr::Integer(1)],
        })),
        HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: 3,
            value: HirExpr::TempRef(TempId(0)),
        })),
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: HirBlock {
                stmts: vec![
                    HirStmt::Close(Box::new(HirClose { from_reg: 3 })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::TempRef(TempId(0))],
                    })),
                ],
            },
            else_block: Some(HirBlock {
                stmts: vec![HirStmt::Return(Box::new(HirReturn { values: Vec::new() }))],
            }),
        })),
    ]);

    assert!(materialize_tbc_close_scopes_in_proto(&mut proto));

    let [HirStmt::Block(block)] = proto.body.stmts.as_slice() else {
        panic!("expected tbc scope to materialize as a single block");
    };
    let [
        HirStmt::Assign(_),
        HirStmt::ToBeClosed(_),
        HirStmt::If(if_stmt),
    ] = block.stmts.as_slice()
    else {
        panic!("expected block to keep decl/tbc/if shape");
    };
    assert!(
        if_stmt
            .then_block
            .stmts
            .iter()
            .all(|stmt| !matches!(stmt, HirStmt::Close(_))),
        "child branch should not retain matching close marker",
    );
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
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: vec![TempId(0), TempId(1), TempId(2)],
        temp_debug_locals: Vec::new(),
        body: HirBlock { stmts },
        children: Vec::new(),
    }
}
