//! 这个文件承载 `global_decl_pretty` 模块的局部不变量测试。

use crate::ast::{
    AstBindingRef, AstBlock, AstCallExpr, AstExpr, AstFunctionExpr, AstGlobalAttr,
    AstGlobalBindingTarget, AstGlobalDecl, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstModule,
    AstNameRef, AstReturn, AstStmt, AstTargetDialect,
};
use crate::hir::{HirProtoRef, LocalId, ParamId};

use super::super::ReadabilityContext;
use super::apply;

#[test]
fn merges_seed_locals_into_single_multi_global_decl_in_seed_order() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Integer(9)],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("seed".to_owned())],
                })),
                AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                    bindings: vec![crate::ast::AstGlobalBinding {
                        target: AstGlobalBindingTarget::Name(crate::ast::AstGlobalName {
                            text: "label".to_owned(),
                        }),
                        attr: AstGlobalAttr::None,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(LocalId(1)))],
                })),
                AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                    bindings: vec![crate::ast::AstGlobalBinding {
                        target: AstGlobalBindingTarget::Name(crate::ast::AstGlobalName {
                            text: "counter".to_owned(),
                        }),
                        attr: AstGlobalAttr::None,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(LocalId(0)))],
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let [AstStmt::GlobalDecl(global_decl)] = module.body.stmts.as_slice() else {
        panic!("expected merged global declaration");
    };
    assert_eq!(global_decl.bindings.len(), 2);
    assert!(matches!(
        &global_decl.bindings[0].target,
        AstGlobalBindingTarget::Name(name) if name.text == "counter"
    ));
    assert!(matches!(
        &global_decl.bindings[1].target,
        AstGlobalBindingTarget::Name(name) if name.text == "label"
    ));
    assert!(
        matches!(global_decl.values.as_slice(), [AstExpr::Integer(9), AstExpr::String(seed)] if seed == "seed")
    );
}

#[test]
fn lua55_does_not_infer_const_global_decl_for_missing_readonly_globals_inside_nested_functions() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Local(LocalId(0)),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                    function: HirProtoRef(1),
                    params: vec![ParamId(0)],
                    is_vararg: false,
                    named_vararg: None,
                    body: AstBlock {
                        stmts: vec![AstStmt::Return(Box::new(AstReturn {
                            values: vec![AstExpr::Call(Box::new(AstCallExpr {
                                callee: AstExpr::FieldAccess(Box::new(
                                    crate::ast::AstFieldAccess {
                                        base: AstExpr::Var(AstNameRef::Global(
                                            crate::ast::AstGlobalName {
                                                text: "math".to_owned(),
                                            },
                                        )),
                                        field: "max".to_owned(),
                                    },
                                )),
                                args: vec![
                                    AstExpr::Var(AstNameRef::Param(ParamId(0))),
                                    AstExpr::Integer(1),
                                ],
                            }))],
                        }))],
                    },
                    captured_bindings: Default::default(),
                }))],
            }))],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let [AstStmt::LocalDecl(local_decl)] = module.body.stmts.as_slice() else {
        panic!("expected outer local decl to remain");
    };
    let [AstExpr::FunctionExpr(function)] = local_decl.values.as_slice() else {
        panic!("expected nested function expression");
    };
    assert!(matches!(
        function.body.stmts.as_slice(),
        [AstStmt::Return(_)]
    ));
}

#[test]
fn lua55_does_not_infer_mutable_global_prelude_when_outer_block_reads_name_written_in_nested_function()
 {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: vec![],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::FunctionDecl(Box::new(
                                crate::ast::AstFunctionDecl {
                                    target: crate::ast::AstFunctionName::Plain(
                                        crate::ast::AstNamePath {
                                            root: AstNameRef::Global(crate::ast::AstGlobalName {
                                                text: "emit".to_owned(),
                                            }),
                                            fields: vec![],
                                        },
                                    ),
                                    func: AstFunctionExpr {
                                        function: HirProtoRef(2),
                                        params: vec![],
                                        is_vararg: false,
                                        named_vararg: None,
                                        body: AstBlock { stmts: vec![] },
                                        captured_bindings: Default::default(),
                                    },
                                },
                            ))],
                        },
                        captured_bindings: Default::default(),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: crate::ast::common::AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "emit".to_owned(),
                        })),
                        args: vec![],
                    })),
                })),
            ],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::LocalDecl(_), AstStmt::CallStmt(_)]
    ));
}

#[test]
fn lua55_does_not_add_global_decl_without_explicit_global_evidence() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                call: crate::ast::common::AstCallKind::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                        text: "print".to_owned(),
                    })),
                    args: vec![AstExpr::String("tag".to_owned())],
                })),
            }))],
        },
    };

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::CallStmt(_)]
    ));
}

#[test]
fn lua55_infers_missing_globals_after_existing_leading_global_decl_run() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                    bindings: vec![crate::ast::AstGlobalBinding {
                        target: AstGlobalBindingTarget::Name(crate::ast::AstGlobalName {
                            text: "outer_prefix".to_owned(),
                        }),
                        attr: AstGlobalAttr::None,
                    }],
                    values: vec![AstExpr::String("G".to_owned())],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: crate::ast::common::AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "print".to_owned(),
                        })),
                        args: vec![AstExpr::String("tag".to_owned())],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    let [
        AstStmt::GlobalDecl(explicit),
        AstStmt::GlobalDecl(inferred),
        AstStmt::CallStmt(_),
    ] = module.body.stmts.as_slice()
    else {
        panic!("expected explicit global decl followed by inferred prelude");
    };
    assert!(matches!(
        &explicit.bindings[0].target,
        AstGlobalBindingTarget::Name(name) if name.text == "outer_prefix"
    ));
    assert!(matches!(
        &inferred.bindings[0].target,
        AstGlobalBindingTarget::Name(name) if name.text == "print"
    ));
    assert_eq!(inferred.bindings[0].attr, AstGlobalAttr::Const);
}
