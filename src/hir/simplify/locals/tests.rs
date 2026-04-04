//! 这个文件承载 `locals` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{HirAssign, HirIf, HirModule, HirProto, HirProtoRef, HirReturn};

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

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
    );

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
                    cond: HirExpr::Boolean(true),
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

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
    );

    assert_eq!(module.protos[0].locals.len(), 1);
    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [
            HirStmt::LocalDecl(local_decl),
            HirStmt::If(if_stmt),
            HirStmt::Return(ret),
        ]
            if matches!(local_decl.bindings.as_slice(), [LocalId(0)])
                && local_decl.values.is_empty()
                && matches!(if_stmt.then_block.stmts.as_slice(), [HirStmt::Assign(assign)]
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                && matches!(if_stmt.else_block.as_ref().map(|block| block.stmts.as_slice()), Some([HirStmt::Assign(assign)])
                    if matches!(assign.targets.as_slice(), [HirLValue::Local(LocalId(0))]))
                && matches!(ret.values.as_slice(), [HirExpr::LocalRef(LocalId(0))])
    ));
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
            locals: vec![LocalId(0)],
            local_debug_hints: Vec::new(),
            upvalues: Vec::new(),
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
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        body,
        children: Vec::new(),
    }
}
