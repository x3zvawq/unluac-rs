//! 这个文件承载 `branch_value_exprs` 模块的局部不变量测试。
//!
//! 这里重点锁两件事：
//! 1. 机械 branch-local 值壳会在 HIR 内部直接收成值表达式；
//! 2. 自引用或值表达式本身不适合参与 HIR `Decision` 综合的形状仍然保留原样。

use super::*;
use crate::hir::common::{
    HirAssign, HirBinaryExpr, HirBinaryOpKind, HirCallExpr, HirGlobalRef, HirProtoRef, HirReturn,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

#[test]
fn collapses_branch_assigned_local_into_initializer_expr() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
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
        ],
    });

    assert!(collapse_branch_value_locals_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::LocalDecl(local_decl), HirStmt::Return(_)]
            if matches!(
                (local_decl.bindings.as_slice(), local_decl.values.as_slice()),
                ([LocalId(0)], [HirExpr::LogicalOr(or_expr)])
                    if matches!(
                        (&or_expr.lhs, &or_expr.rhs),
                        (
                            HirExpr::LogicalAnd(and_expr),
                            HirExpr::String(falsy),
                        ) if matches!(
                            (&and_expr.lhs, &and_expr.rhs),
                            (
                                HirExpr::ParamRef(crate::hir::common::ParamId(0)),
                                HirExpr::String(truthy),
                            ) if truthy == "neg" && falsy == "pos"
                        )
                    )
            )
    ));
}

#[test]
fn keeps_branch_local_when_branch_reads_declared_binding() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(0)],
                values: vec![],
            })),
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::Binary(Box::new(HirBinaryExpr {
                    op: HirBinaryOpKind::Eq,
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
        ],
    });

    assert!(!collapse_branch_value_locals_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 2);
}

#[test]
fn keeps_branch_local_when_branch_value_is_not_synth_safe() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![
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
        ],
    });

    assert!(!collapse_branch_value_locals_in_proto(&mut proto));
    assert_eq!(proto.body.stmts.len(), 2);
}

fn dummy_proto(body: HirBlock) -> crate::hir::common::HirProto {
    crate::hir::common::HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
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
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body,
        children: Vec::new(),
    }
}
