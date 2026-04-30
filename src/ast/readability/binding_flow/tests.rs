//! 这个文件承载 `binding_flow` 模块的局部索引测试。

use super::{BindingUseIndex, count_binding_uses_in_stmts};
use crate::ast::common::{AstCallExpr, AstCallKind, AstFunctionExpr, AstIf, AstLocalBinding};
use crate::ast::{
    AstBlock, AstExpr, AstLocalAttr, AstLocalDecl, AstLocalOrigin, AstNameRef, AstStmt,
};
use crate::hir::LocalId;

fn local_binding(id: LocalId) -> AstLocalBinding {
    AstLocalBinding {
        id: crate::ast::AstBindingRef::Local(id),
        attr: AstLocalAttr::None,
        origin: AstLocalOrigin::Recovered,
    }
}

#[test]
fn suffix_index_counts_function_expr_captures_as_current_function_uses() {
    let captured = LocalId(0);
    let closure = LocalId(1);
    let stmts = vec![
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![local_binding(captured)],
            values: vec![AstExpr::TableConstructor(Box::new(
                crate::ast::AstTableConstructor { fields: Vec::new() },
            ))],
        })),
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![local_binding(closure)],
            values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                function: crate::hir::HirProtoRef(1),
                params: Vec::new(),
                is_vararg: false,
                named_vararg: None,
                body: AstBlock { stmts: Vec::new() },
                captured_bindings: [crate::ast::AstBindingRef::Local(captured)]
                    .into_iter()
                    .collect(),
            }))],
        })),
        AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Local(closure)),
                args: vec![AstExpr::Var(AstNameRef::Local(captured))],
            })),
        })),
    ];

    let index = BindingUseIndex::for_stmts(&stmts);
    assert_eq!(
        index.count_uses_in_suffix(1, crate::ast::AstBindingRef::Local(captured)),
        2
    );
}

#[test]
fn suffix_index_matches_recursive_use_counter_for_top_level_suffixes() {
    let a = LocalId(0);
    let b = LocalId(1);
    let c = LocalId(2);
    let callee = LocalId(3);
    let cond = LocalId(4);

    let stmts = vec![
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![local_binding(a)],
            values: vec![AstExpr::Integer(1)],
        })),
        AstStmt::If(Box::new(AstIf {
            cond: AstExpr::Var(AstNameRef::Local(cond)),
            then_block: AstBlock {
                stmts: vec![AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(callee)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(a)),
                            AstExpr::Var(AstNameRef::Local(b)),
                        ],
                    })),
                }))],
            },
            else_block: Some(AstBlock {
                stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(c))],
                }))],
            }),
        })),
        AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
            call: AstCallKind::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Local(callee)),
                args: vec![
                    AstExpr::Var(AstNameRef::Local(a)),
                    AstExpr::Var(AstNameRef::Local(a)),
                    AstExpr::Var(AstNameRef::Local(c)),
                ],
            })),
        })),
    ];

    let index = BindingUseIndex::for_stmts(&stmts);
    for start in 0..=stmts.len() {
        for binding in [
            crate::ast::AstBindingRef::Local(a),
            crate::ast::AstBindingRef::Local(b),
            crate::ast::AstBindingRef::Local(c),
        ] {
            assert_eq!(
                index.count_uses_in_suffix(start, binding),
                count_binding_uses_in_stmts(&stmts[start..], binding),
                "suffix start={start} binding={binding:?}",
            );
        }
    }
}
