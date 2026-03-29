//! 这个文件承载 `cleanup` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBlock, AstExpr, AstFieldAccess, AstFunctionExpr, AstIf, AstLocalAttr, AstLocalBinding,
    AstLocalFunctionDecl, AstModule, AstNameRef, AstReturn, AstStmt, AstTargetDialect,
};
use crate::hir::{LocalId, ParamId, TempId};

use super::{ReadabilityContext, apply};

#[test]
fn removes_trailing_empty_return_from_module_and_function_bodies() {
    let local = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalFunctionDecl(Box::new(AstLocalFunctionDecl {
                    name: crate::ast::AstBindingRef::Local(local),
                    func: AstFunctionExpr {
                        function: Default::default(),
                        params: vec![ParamId(0)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                        },
                        captured_bindings: Default::default(),
                    },
                })),
                AstStmt::Return(Box::new(AstReturn { values: vec![] })),
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

    let AstStmt::LocalFunctionDecl(local_fn) = &module.body.stmts[0] else {
        panic!("expected local function decl");
    };
    assert!(local_fn.func.body.stmts.is_empty(), "{module:#?}");
    assert_eq!(module.body.stmts.len(), 1, "{module:#?}");
}

#[test]
fn keeps_empty_return_inside_nested_control_flow_blocks() {
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Boolean(true),
                then_block: AstBlock {
                    stmts: vec![AstStmt::Return(Box::new(AstReturn { values: vec![] }))],
                },
                else_block: None,
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

    let AstStmt::If(ast_if) = &module.body.stmts[0] else {
        panic!("expected if statement");
    };
    assert!(matches!(
        ast_if.then_block.stmts.as_slice(),
        [AstStmt::Return(ret)] if ret.values.is_empty()
    ));
}

#[test]
fn drops_unused_synthetic_locals_but_keeps_bindings_assigned_later() {
    let unused = crate::ast::AstSyntheticLocalId(TempId(0));
    let assigned = crate::ast::AstSyntheticLocalId(TempId(1));
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![
                        crate::ast::AstLocalBinding {
                            id: crate::ast::AstBindingRef::SyntheticLocal(unused),
                            attr: crate::ast::AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                        crate::ast::AstLocalBinding {
                            id: crate::ast::AstBindingRef::SyntheticLocal(assigned),
                            attr: crate::ast::AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                    ],
                    values: Vec::new(),
                })),
                AstStmt::Assign(Box::new(crate::ast::AstAssign {
                    targets: vec![crate::ast::AstLValue::Name(
                        crate::ast::AstNameRef::SyntheticLocal(assigned),
                    )],
                    values: vec![AstExpr::Integer(1)],
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

    let AstStmt::LocalDecl(local_decl) = &module.body.stmts[0] else {
        panic!("expected trimmed local decl");
    };
    assert_eq!(local_decl.bindings.len(), 1);
    assert_eq!(
        local_decl.bindings[0].id,
        crate::ast::AstBindingRef::SyntheticLocal(assigned)
    );
}

#[test]
fn flattens_single_return_do_block_after_inner_locals_disappear() {
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::DoBlock(Box::new(AstBlock {
                stmts: vec![AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Integer(1)],
                }))],
            }))],
        },
    };

    assert!(apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::Return(ret)] if ret.values == vec![AstExpr::Integer(1)]
    ));
}

#[test]
fn removes_unused_recovered_lookup_local_with_initializer() {
    let alias = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::Local(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "result".to_owned(),
                        })),
                        field: "pick".to_owned(),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::String("ok".to_owned())],
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

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::Return(ret)] if ret.values == vec![AstExpr::String("ok".to_owned())]
    ));
}

#[test]
fn keeps_recovered_lookup_local_when_nested_function_captures_it() {
    let alias = LocalId(0);
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: crate::ast::AstBindingRef::Local(alias),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                    base: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                        text: "state".to_owned(),
                    })),
                    field: "value".to_owned(),
                }))],
            }))],
        },
    };

    module.body.stmts.push(AstStmt::Return(Box::new(AstReturn {
        values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
            function: Default::default(),
            params: vec![],
            is_vararg: false,
            named_vararg: None,
            body: AstBlock {
                stmts: vec![AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Upvalue(crate::hir::UpvalueId(0)))],
                }))],
            },
            captured_bindings: [crate::ast::AstBindingRef::Local(alias)]
                .into_iter()
                .collect(),
        }))],
    })));

    assert!(!apply(
        &mut module,
        ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
            options: Default::default(),
        }
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::LocalDecl(_), AstStmt::Return(_)]
    ));
}

#[test]
fn keeps_empty_synthetic_local_when_nested_function_captures_it() {
    let alias = crate::ast::AstSyntheticLocalId(TempId(0));
    let mut module = AstModule {
        entry_function: Default::default(),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(crate::ast::AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: crate::ast::AstBindingRef::SyntheticLocal(alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: Vec::new(),
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: Default::default(),
                        params: vec![],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(AstReturn {
                                values: vec![AstExpr::Var(AstNameRef::Upvalue(
                                    crate::hir::UpvalueId(0),
                                ))],
                            }))],
                        },
                        captured_bindings: [crate::ast::AstBindingRef::SyntheticLocal(alias)]
                            .into_iter()
                            .collect(),
                    }))],
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
        [AstStmt::LocalDecl(_), AstStmt::Return(_)]
    ));
}
