use super::super::ReadabilityContext;
use super::apply;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstCallStmt, AstExpr,
    AstFunctionExpr, AstLValue, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstLocalFunctionDecl,
    AstLocalOrigin, AstModule, AstNameRef, AstStmt, AstSyntheticLocalId, AstTargetDialect,
    make_readable_with_options,
};
use crate::hir::{HirProtoRef, ParamId, TempId};
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

    let readable = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );

    let [
        AstStmt::LocalFunctionDecl(local_function),
        AstStmt::CallStmt(call_stmt),
    ] = readable.body.stmts.as_slice()
    else {
        panic!("expected installer iife to become local function decl plus call");
    };

    assert!(matches!(
        local_function.as_ref(),
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
            ],
        },
    };

    let readable = make_readable_with_options(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        ReadabilityOptions::default(),
    );

    let [
        AstStmt::LocalDecl(_),
        AstStmt::LocalFunctionDecl(local_function),
        AstStmt::CallStmt(call_stmt),
    ] = readable.body.stmts.as_slice()
    else {
        panic!("expected original synthetic local plus rewritten installer iife");
    };

    assert_eq!(
        local_function.name,
        AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(1)))
    );
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(
                &call.callee,
                AstExpr::Var(AstNameRef::SyntheticLocal(AstSyntheticLocalId(TempId(1))))
            )
    ));
}
