//! 这个文件承载 `logical_simplify` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirAssign, HirLValue, HirLogicalExpr, HirModule, HirProto, HirProtoRef, HirReturn, TempId,
};

#[test]
fn simplifies_safe_lua_logical_absorption() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::TempRef(TempId(1)),
                    })),
                    rhs: HirExpr::TempRef(TempId(1)),
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::TempRef(TempId(1))])
    ));
}

#[test]
fn keeps_non_safe_lua_logical_shape() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(2))],
            values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: HirExpr::TempRef(TempId(0)),
                rhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(1)),
                    rhs: HirExpr::TempRef(TempId(0)),
                })),
            }))],
        }))],
    });

    assert!(!simplify_logical_exprs_in_proto(&mut proto));
}

#[test]
fn keeps_non_safe_lua_and_or_absorption_shape() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(TempId(2))],
            values: vec![HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                lhs: HirExpr::TempRef(TempId(0)),
                rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(1)),
                    rhs: HirExpr::TempRef(TempId(0)),
                })),
            }))],
        }))],
    });

    assert!(!simplify_logical_exprs_in_proto(&mut proto));
}

#[test]
fn folds_constant_short_circuit_when_rhs_is_safe() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![HirStmt::Return(Box::new(HirReturn {
            values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: HirExpr::Boolean(true),
                rhs: HirExpr::Boolean(false),
            }))],
        }))],
    });

    assert!(simplify_logical_exprs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::Boolean(true)])
    ));
}

#[test]
fn folds_shared_fallback_tail_back_into_single_or_expr() {
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![HirStmt::Return(Box::new(HirReturn {
            values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                        op: crate::hir::common::HirUnaryOpKind::Not,
                        expr: HirExpr::TempRef(TempId(0)),
                    })),
                    rhs: HirExpr::String("fallback".into()),
                })),
                rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(0)),
                    rhs: HirExpr::String("fallback".into()),
                })),
            }))],
        }))],
    });

    assert!(simplify_logical_exprs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(
                ret.values.as_slice(),
                [HirExpr::LogicalOr(logical)]
                    if matches!(&logical.lhs, HirExpr::TempRef(TempId(0)))
                        && matches!(&logical.rhs, HirExpr::String(value) if value == "fallback")
            )
    ));
}

#[test]
fn factors_shared_tail_across_or_chain() {
    let shared_tail = HirExpr::TempRef(TempId(3));
    let mut proto = dummy_proto(HirBlock {
        stmts: vec![HirStmt::Return(Box::new(HirReturn {
            values: vec![HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(0)),
                    rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(1)),
                        rhs: shared_tail.clone(),
                    })),
                })),
                rhs: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(2)),
                        rhs: HirExpr::TempRef(TempId(1)),
                    })),
                    rhs: shared_tail,
                })),
            }))],
        }))],
    });

    assert!(simplify_logical_exprs_in_proto(&mut proto));
    assert!(matches!(
        proto.body.stmts.as_slice(),
        [HirStmt::Return(ret)] if matches!(ret.values.as_slice(), [HirExpr::LogicalOr(_)])
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
        temps: vec![TempId(0), TempId(1), TempId(2), TempId(3)],
        temp_debug_locals: vec![None, None, None, None],
        body,
        children: Vec::new(),
    }
}
