use super::super::ReadabilityContext;
use super::apply;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstLocalFunctionDecl, AstLocalOrigin, AstModule, AstNamePath, AstNameRef,
    AstStmt, AstSyntheticLocalId, AstTableConstructor, AstTargetDialect,
    make_readable,
};
use crate::hir::{HirProtoRef, ParamId, TempId};
use crate::timing::TimingCollector;
use crate::readability::ReadabilityOptions;

fn installer_function() -> AstFunctionExpr {
    AstFunctionExpr {
        function: HirProtoRef(1),
        params: vec![ParamId(0)],
        is_vararg: false,
        named_vararg: None,
        body: AstBlock {
            stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(AstNameRef::Global(
                    crate::ast::AstGlobalName {
                        text: "emit".to_owned(),
                    },
                ))],
                values: vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))],
            }))],
        },
        captured_bindings: Default::default(),
    }
}

fn installer_function_with_local_prep() -> AstFunctionExpr {
    AstFunctionExpr {
        function: HirProtoRef(1),
        params: vec![ParamId(0)],
        is_vararg: false,
        named_vararg: None,
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(crate::hir::LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("seed".to_owned())],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(crate::hir::LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(2),
                        params: vec![ParamId(1)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                                values: vec![
                                    AstExpr::Var(AstNameRef::Local(crate::hir::LocalId(0))),
                                    AstExpr::Var(AstNameRef::Param(ParamId(1))),
                                ],
                            }))],
                        },
                        captured_bindings: [AstBindingRef::Local(crate::hir::LocalId(0))]
                            .into_iter()
                            .collect(),
                    }))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Global(
                        crate::ast::AstGlobalName {
                            text: "emit".to_owned(),
                        },
                    ))],
                    values: vec![AstExpr::Var(AstNameRef::Local(crate::hir::LocalId(1)))],
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn { values: Vec::new() })),
            ],
        },
        captured_bindings: Default::default(),
    }
}

fn installer_function_with_method_export() -> AstFunctionExpr {
    AstFunctionExpr {
        function: HirProtoRef(1),
        params: vec![ParamId(0)],
        is_vararg: false,
        named_vararg: None,
        body: AstBlock {
            stmts: vec![AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                target: AstFunctionName::Method(
                    AstNamePath {
                        root: AstNameRef::Param(ParamId(0)),
                        fields: Vec::new(),
                    },
                    "emit".to_owned(),
                ),
                func: AstFunctionExpr {
                    function: HirProtoRef(3),
                    params: vec![ParamId(1)],
                    is_vararg: false,
                    named_vararg: None,
                    body: AstBlock {
                        stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                            values: vec![AstExpr::Var(AstNameRef::Param(ParamId(1)))],
                        }))],
                    },
                    captured_bindings: Default::default(),
                },
            }))],
        },
        captured_bindings: Default::default(),
    }
}

fn make_lua55_readable(module: &AstModule) -> AstModule {
    make_readable(
        module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
        &TimingCollector::disabled(),
    )
}

fn expect_installer_rewrite(module: &AstModule) -> (&AstLocalFunctionDecl, &AstCallStmt) {
    let [
        AstStmt::LocalFunctionDecl(local_function),
        AstStmt::CallStmt(call_stmt),
    ] = module.body.stmts.as_slice()
    else {
        panic!("expected installer iife to become local function decl plus call");
    };
    (local_function, call_stmt)
}

#[test]
fn names_installer_iife_before_function_sugar_consumes_it() {
    let module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FunctionExpr(Box::new(installer_function())),
                    args: vec![AstExpr::String("ax".to_owned())],
                })),
            }))],
        },
    };

    let readable = make_lua55_readable(&module);
    let (local_function, call_stmt) = expect_installer_rewrite(&readable);

    assert!(matches!(
        local_function,
        AstLocalFunctionDecl {
            name: AstBindingRef::SyntheticLocal(_),
            ..
        }
    ));
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(
                (&call.callee, local_function.name),
                (
                    AstExpr::Var(AstNameRef::SyntheticLocal(name)),
                    AstBindingRef::SyntheticLocal(binding),
                ) if *name == binding
            ) && matches!(call.args.as_slice(), [AstExpr::String(tag)] if tag == "ax")
    ));
}

#[test]
fn keeps_non_installer_iife_as_direct_function_call() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: vec![ParamId(0)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                                values: vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))],
                            }))],
                        },
                        captured_bindings: Default::default(),
                    })),
                    args: vec![AstExpr::Integer(7)],
                })),
            }))],
        },
    };

    let changed = apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: ReadabilityOptions::default(),
        },
    );

    assert!(!changed);
    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::CallStmt(call_stmt)]
            if matches!(&call_stmt.call, AstCallKind::Call(call) if matches!(&call.callee, AstExpr::FunctionExpr(_)))
    ));
}

#[test]
fn allocates_fresh_synthetic_local_after_existing_ids() {
    let module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))),
                        attr: AstLocalAttr::None,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Integer(1)],
                })),
                AstStmt::CallStmt(Box::new(AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::FunctionExpr(Box::new(installer_function())),
                        args: vec![AstExpr::String("ax".to_owned())],
                    })),
                })),
                AstStmt::Return(Box::new(crate::ast::AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::SyntheticLocal(
                        AstSyntheticLocalId(TempId(0)),
                    ))],
                })),
            ],
        },
    };

    let readable = make_lua55_readable(&module);
    let local_function = readable
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            AstStmt::LocalFunctionDecl(local_function) => Some(local_function.as_ref()),
            _ => None,
        })
        .expect("expected installer iife rewrite to produce a local function decl");
    let call_stmt = readable
        .body
        .stmts
        .iter()
        .find_map(|stmt| match stmt {
            AstStmt::CallStmt(call_stmt) => Some(call_stmt.as_ref()),
            _ => None,
        })
        .expect("expected installer iife rewrite to produce a call stmt");

    let AstBindingRef::SyntheticLocal(binding) = local_function.name else {
        panic!("expected rewritten installer iife to use a synthetic local binding");
    };
    assert_eq!(binding, AstSyntheticLocalId(TempId(1)));
    assert!(matches!(
        readable.body.stmts.as_slice(),
        body if body.iter().any(|stmt| matches!(
            stmt,
            AstStmt::Return(ret)
                if matches!(
                    ret.values.as_slice(),
                    [AstExpr::Var(AstNameRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))))]
                )
        ))
    ));
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(
                &call.callee,
                AstExpr::Var(AstNameRef::SyntheticLocal(name)) if *name == binding
            )
    ));
}

#[test]
fn names_installer_iife_when_export_uses_local_function_prep() {
    let module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FunctionExpr(Box::new(installer_function_with_local_prep())),
                    args: vec![AstExpr::String("ax".to_owned())],
                })),
            }))],
        },
    };

    let readable = make_lua55_readable(&module);
    let (local_function, call_stmt) = expect_installer_rewrite(&readable);

    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(
                (&call.callee, local_function.name),
                (
                    AstExpr::Var(AstNameRef::SyntheticLocal(name)),
                    AstBindingRef::SyntheticLocal(binding),
                ) if *name == binding
            )
    ));

    assert!(matches!(
        local_function.func.body.stmts.as_slice(),
        body if body.iter().any(|stmt| matches!(
            stmt,
            AstStmt::LocalDecl(local_decl)
                if matches!(
                    (local_decl.bindings.as_slice(), local_decl.values.as_slice()),
                    (
                        [AstLocalBinding {
                            id: AstBindingRef::Local(crate::hir::LocalId(0)),
                            ..
                        }],
                        [AstExpr::String(seed)],
                    ) if seed == "seed"
                )
        ))
    ));
    assert!(matches!(
        local_function.func.body.stmts.as_slice(),
        body if body.iter().any(|stmt| matches!(
            stmt,
            AstStmt::FunctionDecl(function_decl)
                if matches!(
                    function_decl.target,
                    AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Global(_),
                        ..
                    }) | AstFunctionName::Method(AstNamePath {
                        root: AstNameRef::Global(_),
                        ..
                    }, _)
                )
        ))
    ));
}

#[test]
fn names_installer_iife_when_export_uses_method_decl_on_receiver() {
    let module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::CallStmt(Box::new(AstCallStmt {
                call: AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FunctionExpr(
                        Box::new(installer_function_with_method_export()),
                    ),
                    args: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
            }))],
        },
    };

    let readable = make_lua55_readable(&module);
    let (local_function, call_stmt) = expect_installer_rewrite(&readable);

    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(
                (&call.callee, local_function.name),
                (
                    AstExpr::Var(AstNameRef::SyntheticLocal(name)),
                    AstBindingRef::SyntheticLocal(binding),
                ) if *name == binding
            )
    ));
    assert!(matches!(
        local_function.func.body.stmts.as_slice(),
        [AstStmt::FunctionDecl(function_decl)]
            if matches!(
                &function_decl.target,
                AstFunctionName::Method(AstNamePath {
                    root: AstNameRef::Param(ParamId(0)),
                    fields,
                }, method)
                    if fields.is_empty() && method == "emit"
            )
    ));
}
