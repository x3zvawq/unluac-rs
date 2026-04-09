//! 这个文件承载 `decision` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::*;
use crate::hir::common::{
    HirIf, HirLogicalExpr, HirModule, HirProto, HirProtoRef, HirReturn, HirUnaryExpr,
    HirUnaryOpKind, TempId,
};

#[test]
fn collapses_repeated_same_test_in_decision_chain() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::Decision(Box::new(HirDecisionExpr {
                    entry: HirDecisionNodeRef(0),
                    nodes: vec![
                        HirDecisionNode {
                            id: HirDecisionNodeRef(0),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::Node(HirDecisionNodeRef(1)),
                            falsy: HirDecisionTarget::Expr(HirExpr::String("false".into())),
                        },
                        HirDecisionNode {
                            id: HirDecisionNodeRef(1),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::CurrentValue,
                            falsy: HirDecisionTarget::Expr(HirExpr::String("false".into())),
                        },
                    ],
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(
                ret.values.as_slice(),
                [HirExpr::LogicalOr(logical)]
                    if matches!(&logical.lhs, HirExpr::TempRef(TempId(0)))
                        && matches!(&logical.rhs, HirExpr::String(value) if value == "false")
            )
    ));
}

#[test]
fn folds_constant_truthy_decision_to_leaf_expr() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::Decision(Box::new(HirDecisionExpr {
                    entry: HirDecisionNodeRef(0),
                    nodes: vec![HirDecisionNode {
                        id: HirDecisionNodeRef(0),
                        test: HirExpr::String("yes".into()),
                        truthy: HirDecisionTarget::CurrentValue,
                        falsy: HirDecisionTarget::Expr(HirExpr::String("no".into())),
                    }],
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::String(value)] if value == "yes")
    ));
}

#[test]
fn specializes_descendant_when_stable_test_truthiness_is_already_known() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::Decision(Box::new(HirDecisionExpr {
                    entry: HirDecisionNodeRef(0),
                    nodes: vec![
                        HirDecisionNode {
                            id: HirDecisionNodeRef(0),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::Node(HirDecisionNodeRef(1)),
                            falsy: HirDecisionTarget::Expr(HirExpr::String("fallback".into())),
                        },
                        HirDecisionNode {
                            id: HirDecisionNodeRef(1),
                            test: HirExpr::TempRef(TempId(1)),
                            truthy: HirDecisionTarget::Expr(HirExpr::String("yes".into())),
                            falsy: HirDecisionTarget::Node(HirDecisionNodeRef(2)),
                        },
                        HirDecisionNode {
                            id: HirDecisionNodeRef(2),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::Expr(HirExpr::String("still-true".into())),
                            falsy: HirDecisionTarget::Expr(HirExpr::String("nope".into())),
                        },
                    ],
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [expr]
                if !expr_contains_string(expr, "nope"))
    ));
}

#[test]
fn canonicalizes_truth_fact_sets_independent_of_path_order() {
    let a = HirExpr::TempRef(TempId(0));
    let not_b = HirExpr::Unary(Box::new(HirUnaryExpr {
        op: HirUnaryOpKind::Not,
        expr: HirExpr::TempRef(TempId(1)),
    }));

    let left = super::extend_truth_facts(
        &super::extend_truth_facts(&TruthFacts::default(), &a, true),
        &not_b,
        false,
    );
    let right = super::extend_truth_facts(
        &super::extend_truth_facts(&TruthFacts::default(), &not_b, false),
        &a,
        true,
    );

    assert_eq!(left, right);
    assert_eq!(super::known_truthiness_from_facts(&a, &left), Some(true));
    assert_eq!(
        super::known_truthiness_from_facts(&not_b, &left),
        Some(false)
    );
}

#[test]
fn collapses_value_decision_when_then_branch_is_definitely_truthy() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::Decision(Box::new(HirDecisionExpr {
                    entry: HirDecisionNodeRef(0),
                    nodes: vec![
                        HirDecisionNode {
                            id: HirDecisionNodeRef(0),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::Expr(HirExpr::String("yes".into())),
                            falsy: HirDecisionTarget::Node(HirDecisionNodeRef(1)),
                        },
                        HirDecisionNode {
                            id: HirDecisionNodeRef(1),
                            test: HirExpr::TempRef(TempId(1)),
                            truthy: HirDecisionTarget::Expr(HirExpr::String("maybe".into())),
                            falsy: HirDecisionTarget::Expr(HirExpr::String("no".into())),
                        },
                    ],
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::LogicalOr(_)])
    ));
}

#[test]
fn keeps_collapsible_decision_inside_short_circuit_expr_as_value_expr() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                    lhs: HirExpr::TempRef(TempId(1)),
                    rhs: HirExpr::Decision(Box::new(HirDecisionExpr {
                        entry: HirDecisionNodeRef(0),
                        nodes: vec![HirDecisionNode {
                            id: HirDecisionNodeRef(0),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::CurrentValue,
                            falsy: HirDecisionTarget::Expr(HirExpr::String("no".into())),
                        }],
                    })),
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::LogicalAnd(_)])
    ));
    assert!(!dump_contains_if(&module));
}

#[test]
fn refuses_to_collapse_cyclic_value_decision_expr() {
    let decision = HirDecisionExpr {
        entry: HirDecisionNodeRef(0),
        nodes: vec![
            HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: HirExpr::TempRef(TempId(0)),
                truthy: HirDecisionTarget::Node(HirDecisionNodeRef(1)),
                falsy: HirDecisionTarget::Expr(HirExpr::String("stop".into())),
            },
            HirDecisionNode {
                id: HirDecisionNodeRef(1),
                test: HirExpr::TempRef(TempId(1)),
                truthy: HirDecisionTarget::Expr(HirExpr::String("done".into())),
                falsy: HirDecisionTarget::Node(HirDecisionNodeRef(0)),
            },
        ],
    };

    assert!(super::decision_has_cycles(&decision));
    assert!(super::collapse_value_decision_expr(&decision).is_none());
    assert!(super::collapse_condition_decision_expr(&decision).is_none());
}

#[test]
fn keeps_cyclic_value_decision_stable_during_simplify() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                values: vec![HirExpr::Decision(Box::new(HirDecisionExpr {
                    entry: HirDecisionNodeRef(0),
                    nodes: vec![
                        HirDecisionNode {
                            id: HirDecisionNodeRef(0),
                            test: HirExpr::TempRef(TempId(0)),
                            truthy: HirDecisionTarget::Node(HirDecisionNodeRef(1)),
                            falsy: HirDecisionTarget::Expr(HirExpr::String("stop".into())),
                        },
                        HirDecisionNode {
                            id: HirDecisionNodeRef(1),
                            test: HirExpr::TempRef(TempId(1)),
                            truthy: HirDecisionTarget::Expr(HirExpr::String("done".into())),
                            falsy: HirDecisionTarget::Node(HirDecisionNodeRef(0)),
                        },
                    ],
                }))],
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        &module.protos[0].body.stmts.as_slice(),
        [HirStmt::Return(ret)]
            if matches!(ret.values.as_slice(), [HirExpr::Decision(_)])
    ));
}

#[test]
fn removes_boolean_shells_in_condition_context() {
    let mut module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![dummy_proto(HirBlock {
            stmts: vec![HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: HirExpr::TempRef(TempId(0)),
                        rhs: HirExpr::Boolean(true),
                    })),
                    rhs: HirExpr::Boolean(false),
                })),
                then_block: HirBlock { stmts: Vec::new() },
                else_block: None,
            }))],
        })],
    };

    super::super::simplify_hir(
        &mut module,
        crate::readability::ReadabilityOptions::default(),
        &crate::timing::TimingCollector::disabled(),
        &[],
    );

    assert!(matches!(
        module.protos[0].body.stmts.as_slice(),
        [HirStmt::If(if_stmt)] if matches!(if_stmt.cond, HirExpr::TempRef(TempId(0)))
    ));
}

#[test]
fn prefers_guarded_disjunction_shape_over_factored_conjunction() {
    let guarded = super::logical_or(
        super::logical_and(
            HirExpr::TempRef(TempId(0)),
            super::logical_and(
                super::logical_or(HirExpr::TempRef(TempId(1)), HirExpr::TempRef(TempId(2))),
                HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Not,
                    expr: HirExpr::TempRef(TempId(3)),
                })),
            ),
        ),
        super::logical_and(
            super::logical_or(HirExpr::TempRef(TempId(0)), HirExpr::TempRef(TempId(3))),
            super::logical_and(HirExpr::TempRef(TempId(1)), HirExpr::TempRef(TempId(2))),
        ),
    );

    let factored = super::logical_and(
        super::logical_or(
            HirExpr::TempRef(TempId(0)),
            super::logical_and(
                HirExpr::TempRef(TempId(3)),
                super::logical_and(HirExpr::TempRef(TempId(1)), HirExpr::TempRef(TempId(2))),
            ),
        ),
        super::logical_and(
            super::logical_or(
                HirExpr::TempRef(TempId(1)),
                super::logical_or(
                    super::logical_and(
                        HirExpr::TempRef(TempId(2)),
                        super::logical_or(
                            HirExpr::Unary(Box::new(HirUnaryExpr {
                                op: HirUnaryOpKind::Not,
                                expr: HirExpr::TempRef(TempId(3)),
                            })),
                            HirExpr::TempRef(TempId(1)),
                        ),
                    ),
                    HirExpr::TempRef(TempId(1)),
                ),
            ),
            super::logical_or(
                HirExpr::Unary(Box::new(HirUnaryExpr {
                    op: HirUnaryOpKind::Not,
                    expr: HirExpr::TempRef(TempId(3)),
                })),
                HirExpr::TempRef(TempId(2)),
            ),
        ),
    );

    assert!(
        super::synthesize::expr_cost(&guarded) < super::synthesize::expr_cost(&factored),
        "guarded short-circuit should stay cheaper than mechanically factored conjunction"
    );
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
        temps: vec![TempId(0)],
        temp_debug_locals: vec![None],
        body,
        children: Vec::new(),
    }
}

fn expr_contains_string(expr: &HirExpr, needle: &str) -> bool {
    match expr {
        HirExpr::String(value) => value == needle,
        HirExpr::TableAccess(access) => {
            expr_contains_string(&access.base, needle) || expr_contains_string(&access.key, needle)
        }
        HirExpr::Unary(unary) => expr_contains_string(&unary.expr, needle),
        HirExpr::Binary(binary) => {
            expr_contains_string(&binary.lhs, needle) || expr_contains_string(&binary.rhs, needle)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_contains_string(&logical.lhs, needle) || expr_contains_string(&logical.rhs, needle)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_contains_string(&node.test, needle)
                || target_contains_string(&node.truthy, needle)
                || target_contains_string(&node.falsy, needle)
        }),
        HirExpr::Call(call) => {
            expr_contains_string(&call.callee, needle)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_string(arg, needle))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_contains_string(expr, needle),
                HirTableField::Record(field) => {
                    matches!(
                        &field.key,
                        HirTableKey::Expr(expr) if expr_contains_string(expr, needle)
                    ) || expr_contains_string(&field.value, needle)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_contains_string(expr, needle))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_contains_string(&capture.value, needle)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Number(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn target_contains_string(target: &HirDecisionTarget, needle: &str) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_contains_string(expr, needle),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn dump_contains_if(module: &HirModule) -> bool {
    module
        .protos
        .iter()
        .any(|proto| block_contains_if(&proto.body))
}

fn block_contains_if(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_contains_if)
}

fn stmt_contains_if(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::If(_) => true,
        HirStmt::While(while_stmt) => block_contains_if(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => block_contains_if(&repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => block_contains_if(&numeric_for.body),
        HirStmt::GenericFor(generic_for) => block_contains_if(&generic_for.body),
        HirStmt::Block(block) => block_contains_if(block),
        HirStmt::Unstructured(unstructured) => block_contains_if(&unstructured.body),
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Close(_)
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}
