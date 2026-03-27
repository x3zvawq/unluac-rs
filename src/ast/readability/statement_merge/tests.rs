//! 这个文件承载 `statement_merge` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use super::ReadabilityContext;
use crate::ast::common::{AstCallExpr, AstCallKind, AstIndexAccess, AstLocalBinding};
use crate::ast::{
    AstExpr, AstLValue, AstLocalAttr, AstLocalDecl, AstModule, AstNameRef, AstStmt,
    AstTargetDialect, make_readable_with_options,
};
use crate::hir::{LocalId, TempId};

fn apply_statement_merge(module: &AstModule) -> AstModule {
    let mut module = module.clone();
    super::apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        },
    );
    module
}

#[test]
fn merges_empty_local_decl_followed_by_matching_assign() {
    let temp = TempId(0);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Temp(temp),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Temp(temp))],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        args: vec![AstExpr::Integer(1)],
                    }))],
                })),
            ],
        },
    };

    let module = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        Default::default(),
    );
    assert_eq!(
        module.body.stmts,
        vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: crate::ast::AstBindingRef::SyntheticLocal(crate::ast::AstSyntheticLocalId(
                    temp,
                )),
                attr: AstLocalAttr::None,
                origin: crate::ast::AstLocalOrigin::Recovered,
            }],
            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                args: vec![AstExpr::Integer(1)],
            }))],
        }))]
    );
}

#[test]
fn does_not_merge_when_assign_targets_do_not_match_decl_bindings() {
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        args: vec![AstExpr::Integer(1)],
                    })),
                })),
            ],
        },
    };

    let module = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        Default::default(),
    );
    assert_eq!(module.body.stmts.len(), 2);
}

#[test]
fn merges_adjacent_single_value_local_decls_into_multi_local_decl() {
    let index = LocalId(0);
    let value = LocalId(1);
    let a = LocalId(2);
    let b = LocalId(3);
    let c = LocalId(4);
    let printer = LocalId(5);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(a),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(index))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(b),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(value))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(c),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(10))),
                        index: AstExpr::Var(AstNameRef::Local(index)),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(printer)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(a)),
                            AstExpr::Var(AstNameRef::Local(b)),
                            AstExpr::Var(AstNameRef::Local(c)),
                        ],
                    })),
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![
                        AstExpr::Var(AstNameRef::Local(a)),
                        AstExpr::Var(AstNameRef::Local(b)),
                        AstExpr::Var(AstNameRef::Local(c)),
                    ],
                })),
            ],
        },
    };

    let module = apply_statement_merge(&module);
    assert_eq!(
        module.body.stmts[0],
        AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![
                AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(a),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                },
                AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(b),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                },
                AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(c),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                },
            ],
            values: vec![
                AstExpr::Var(AstNameRef::Local(index)),
                AstExpr::Var(AstNameRef::Local(value)),
                AstExpr::IndexAccess(Box::new(AstIndexAccess {
                    base: AstExpr::Var(AstNameRef::Local(LocalId(10))),
                    index: AstExpr::Var(AstNameRef::Local(index)),
                })),
            ],
        }))
    );
    assert_eq!(module.body.stmts.len(), 3);
}

#[test]
fn does_not_merge_adjacent_local_decls_when_later_initializer_reads_earlier_binding() {
    let a = LocalId(0);
    let b = LocalId(1);
    let table = LocalId(2);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(a),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Integer(1)],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(b),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Var(AstNameRef::Local(a)),
                    }))],
                })),
            ],
        },
    };

    let module = apply_statement_merge(&module);
    assert_eq!(module.body.stmts.len(), 2);
}

#[test]
fn merges_adjacent_single_value_local_decls_inside_nested_function_expr_bodies() {
    let fn_binding = LocalId(0);
    let index = LocalId(1);
    let value = LocalId(2);
    let a = LocalId(3);
    let b = LocalId(4);
    let c = LocalId(5);
    let printer = LocalId(6);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(fn_binding),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::FunctionExpr(Box::new(
                    crate::ast::AstFunctionExpr {
                        function: Default::default(),
                        params: Vec::new(),
                        is_vararg: false,
                        named_vararg: None,
                        body: crate::ast::AstBlock {
                            stmts: vec![
                                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(a),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::Var(AstNameRef::Local(index))],
                                })),
                                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(b),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::Var(AstNameRef::Local(value))],
                                })),
                                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: crate::ast::AstBindingRef::Local(c),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                                        base: AstExpr::Var(AstNameRef::Local(LocalId(10))),
                                        index: AstExpr::Var(AstNameRef::Local(index)),
                                    }))],
                                })),
                                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                                    call: AstCallKind::Call(Box::new(AstCallExpr {
                                        callee: AstExpr::Var(AstNameRef::Local(printer)),
                                        args: vec![
                                            AstExpr::Var(AstNameRef::Local(a)),
                                            AstExpr::Var(AstNameRef::Local(b)),
                                            AstExpr::Var(AstNameRef::Local(c)),
                                        ],
                                    })),
                                })),
                                AstStmt::Return(Box::new(crate::ast::AstReturn {
                                    values: vec![
                                        AstExpr::Var(AstNameRef::Local(a)),
                                        AstExpr::Var(AstNameRef::Local(b)),
                                        AstExpr::Var(AstNameRef::Local(c)),
                                    ],
                                })),
                            ],
                        },
                        captured_bindings: Default::default(),
                    },
                ))],
            }))],
        },
    };

    let module = apply_statement_merge(&module);
    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected top-level local decl");
    };
    let [AstExpr::FunctionExpr(function)] = local_decl.values.as_slice() else {
        panic!("expected local decl with function expr value");
    };
    assert_eq!(function.body.stmts.len(), 3);
    let AstStmt::LocalDecl(merged) = &function.body.stmts[0] else {
        panic!("expected merged local decl inside nested function body");
    };
    assert_eq!(merged.bindings.len(), 3);
    assert_eq!(merged.values.len(), 3);
}

#[test]
fn does_not_merge_one_shot_call_prep_alias_run() {
    let printer = LocalId(0);
    let label = LocalId(1);
    let item = LocalId(2);
    let table = LocalId(3);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(printer),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Global(
                        crate::ast::AstGlobalName {
                            text: "print".to_string(),
                        },
                    ))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(label),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("tag".to_string())],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(item),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::Var(AstNameRef::Local(table)),
                        index: AstExpr::Integer(1),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(printer)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(label)),
                            AstExpr::Var(AstNameRef::Local(item)),
                        ],
                    })),
                })),
            ],
        },
    };

    let module = apply_statement_merge(&module);
    assert_eq!(module.body.stmts.len(), 4);
}

#[test]
fn sinks_hoisted_temp_decl_into_generic_for_body_assignment() {
    let iter_fn = LocalId(0);
    let temp_a = TempId(0);
    let temp_b = TempId(1);
    let module = AstModule {
        entry_function: Default::default(),
        body: crate::ast::AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![
                        AstLocalBinding {
                            id: crate::ast::AstBindingRef::Temp(temp_a),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                        AstLocalBinding {
                            id: crate::ast::AstBindingRef::Temp(temp_b),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                    ],
                    values: Vec::new(),
                })),
                AstStmt::GenericFor(Box::new(crate::ast::AstGenericFor {
                    bindings: vec![crate::ast::AstBindingRef::Local(LocalId(10))],
                    iterator: vec![AstExpr::Var(AstNameRef::Local(iter_fn))],
                    body: crate::ast::AstBlock {
                        stmts: vec![
                            AstStmt::Assign(Box::new(crate::ast::AstAssign {
                                targets: vec![
                                    AstLValue::Name(AstNameRef::Temp(temp_a)),
                                    AstLValue::Name(AstNameRef::Temp(temp_b)),
                                ],
                                values: vec![AstExpr::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(LocalId(11))),
                                    args: vec![AstExpr::Var(AstNameRef::Local(LocalId(10)))],
                                }))],
                            })),
                            AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                                call: AstCallKind::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(LocalId(12))),
                                    args: vec![
                                        AstExpr::Var(AstNameRef::Temp(temp_a)),
                                        AstExpr::Var(AstNameRef::Temp(temp_b)),
                                    ],
                                })),
                            })),
                        ],
                    },
                })),
            ],
        },
    };

    let module = apply_statement_merge(&module);
    assert_eq!(module.body.stmts.len(), 1);
    let AstStmt::GenericFor(generic_for) = &module.body.stmts[0] else {
        panic!("expected generic-for after sinking hoisted temps");
    };
    let AstStmt::LocalDecl(local_decl) = &generic_for.body.stmts[0] else {
        panic!("expected first loop stmt to become local decl");
    };
    assert_eq!(local_decl.bindings.len(), 2);
    assert_eq!(local_decl.values.len(), 1);
}
