//! 这个文件承载 `boolean_shells` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirCallStmt, HirGlobalRef, HirIf,
    HirLocalDecl, HirProtoRef, HirReturn, HirUnaryExpr, HirUnaryOpKind,
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
                    method_name: None,
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

#[test]
fn collapses_live_boolean_materialization_shell_into_local_initializer() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![crate::hir::common::LocalId(0)],
                values: vec![],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Not,
                    expr: HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Eq,
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::Nil,
                    })),
                })),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Local(crate::hir::common::LocalId(0))],
                        values: vec![HirExpr::Boolean(true)],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Local(crate::hir::common::LocalId(0))],
                        values: vec![HirExpr::Boolean(false)],
                    }))],
                }),
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LocalRef(crate::hir::common::LocalId(0))],
            })),
        ],
    });

    assert!(remove_boolean_materialization_shells_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::LocalDecl(local_decl), HirStmt::Return(_)]
            if matches!(
                (local_decl.bindings.as_slice(), local_decl.values.as_slice()),
                ([crate::hir::common::LocalId(0)], [HirExpr::Unary(unary)])
                    if unary.op == HirUnaryOpKind::Not
            )
    ));
}

#[test]
fn booleanizes_truthiness_shell_for_non_boolean_condition() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Boolean(true)],
                    }))],
                },
                else_block: Some(HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: vec![HirExpr::Boolean(false)],
                    }))],
                }),
            })),
            HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::TempRef(TempId(0))],
            })),
        ],
    });

    assert!(remove_boolean_materialization_shells_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Assign(assign), HirStmt::Return(_)]
            if matches!(
                (assign.targets.as_slice(), assign.values.as_slice()),
                ([HirLValue::Temp(TempId(0))], [HirExpr::LogicalOr(or_expr)])
                    if matches!(
                        (&or_expr.lhs, &or_expr.rhs),
                        (
                            HirExpr::LogicalAnd(and_expr),
                            HirExpr::Boolean(false)
                        ) if matches!(
                            (&and_expr.lhs, &and_expr.rhs),
                            (
                                HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                                HirExpr::Boolean(true)
                            )
                        )
                    )
            )
    ));
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
        param_debug_hints: Vec::new(),
        locals: vec![crate::hir::common::LocalId(0)],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        body,
        children: Vec::new(),
    }
}
