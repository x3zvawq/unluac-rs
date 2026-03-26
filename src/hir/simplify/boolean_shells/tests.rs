//! 这个文件承载 `boolean_shells` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCallStmt, HirGlobalRef, HirIf,
    HirProtoRef,
};

#[test]
fn removes_dead_boolean_materialization_shell() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Eq,
                    lhs: HirExpr::LocalRef(crate::hir::common::LocalId(0)),
                    rhs: HirExpr::Nil,
                })),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Boolean(true)],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::Boolean(false)],
                    }))],
                }),
            })),
            HirStmt::CallStmt(Box::new(HirCallStmt {
                call: HirCallExpr {
                    callee: HirExpr::GlobalRef(HirGlobalRef {
                        name: "print".to_owned(),
                    }),
                    args: vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Eq,
                        lhs: HirExpr::LocalRef(crate::hir::common::LocalId(0)),
                        rhs: HirExpr::Nil,
                    }))],
                    multiret: false,
                    method: false,
                },
            })),
        ],
    });

    assert!(remove_boolean_materialization_shells_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::CallStmt(_)]
    ));
}

#[test]
fn removes_dead_pure_value_materialization_shell() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::ParamRef(crate::hir::common::ParamId(0))],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(1))],
                        values: vec![HirExpr::Integer(1)],
                    }))],
                }),
            })),
            HirStmt::Return(Box::new(crate::hir::common::HirReturn { values: vec![] })),
        ],
    });

    assert!(remove_boolean_materialization_shells_in_proto(&mut proto));
    assert!(matches!(proto.body.stmts.as_slice(), [HirStmt::Return(_)]));
}

fn dummy_proto(body: HirBlock) -> crate::hir::common::HirProto {
    crate::hir::common::HirProto {
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
        locals: vec![crate::hir::common::LocalId(0)],
        upvalues: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        body,
        children: Vec::new(),
    }
}
