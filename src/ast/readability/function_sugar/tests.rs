//! 这个文件承载 `function_sugar` 模块的局部不变量测试。
//!
//! 这里主要验证两件事：
//! 1. 方法调用恢复出来之后，后续的 `obj.field = function(...)` 能正确降成方法声明；
//! 2. 没有 method-call 证据的字段函数仍然保留普通 `function obj.field(...)` 形状。

use super::apply;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstExpr, AstFieldAccess,
    AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding,
    AstLocalDecl, AstMethodCallExpr, AstModule, AstNamePath, AstNameRef, AstReturn, AstStmt,
    AstTableConstructor, AstTargetDialect,
};
use crate::hir::{HirProtoRef, LocalId, ParamId};
use crate::readability::ReadabilityOptions;

fn method_function(params: &[ParamId]) -> AstExpr {
    AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
        function: HirProtoRef(1),
        params: params.to_vec(),
        is_vararg: false,
        named_vararg: None,
        body: AstBlock {
            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                values: vec![AstExpr::Var(AstNameRef::Param(params[0]))],
            }))],
        },
        captured_bindings: Default::default(),
    }))
}

fn run_function_sugar_to_fixed_point(module: &mut AstModule, target: AstTargetDialect) -> bool {
    let context = super::ReadabilityContext {
        target,
        options: ReadabilityOptions::default(),
    };
    let mut changed = false;
    while apply(module, context) {
        changed = true;
    }
    changed
}

#[test]
fn lowers_field_function_assignment_into_method_decl_when_method_call_evidence_exists() {
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
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "method1".to_owned(),
                    }))],
                    values: vec![method_function(&[ParamId(0), ParamId(1)])],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        receiver: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        method: "method1".to_owned(),
                        args: vec![AstExpr::Integer(1)],
                    })),
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "method3".to_owned(),
                    }))],
                    values: vec![method_function(&[ParamId(0)])],
                })),
            ],
        },
    };

    let changed = run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
    );
    assert!(changed);

    assert!(matches!(
        &module.body.stmts[1],
        AstStmt::FunctionDecl(function_decl)
            if matches!(
                &function_decl.target,
                crate::ast::AstFunctionName::Method(
                    AstNamePath {
                        root: AstNameRef::Local(LocalId(0)),
                        fields,
                    },
                    method,
                ) if fields.is_empty() && method == "method1"
            )
    ));
    assert!(matches!(
        &module.body.stmts[3],
        AstStmt::FunctionDecl(function_decl)
            if matches!(
                &function_decl.target,
                crate::ast::AstFunctionName::Plain(AstNamePath {
                    root: AstNameRef::Local(LocalId(0)),
                    fields,
                }) if fields == &vec!["method3".to_owned()]
            )
    ));
}

#[test]
fn keeps_recursive_local_function_binding_before_table_slot_forwarding() {
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
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Integer(1)],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(2)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: vec![ParamId(0)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                                values: vec![AstExpr::Call(Box::new(crate::ast::AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                                    args: vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))],
                                }))],
                            }))],
                        },
                        captured_bindings: [AstBindingRef::Local(LocalId(2))].into_iter().collect(),
                    }))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::IndexAccess(Box::new(
                        crate::ast::AstIndexAccess {
                            base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                            index: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        },
                    ))],
                    values: vec![AstExpr::Var(AstNameRef::Local(LocalId(2)))],
                })),
            ],
        },
    };

    let changed = run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
    );
    assert!(changed);

    assert!(matches!(
        &module.body.stmts[2],
        AstStmt::LocalFunctionDecl(local_function_decl)
            if local_function_decl.name == AstBindingRef::Local(LocalId(2))
    ));
    assert!(matches!(
        &module.body.stmts[3],
        AstStmt::Assign(assign)
            if matches!(
                assign.values.as_slice(),
                [AstExpr::Var(AstNameRef::Local(LocalId(2)))]
            )
    ));
}

#[test]
fn inlines_constructor_locals_and_function_field_into_terminal_return_call() {
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
                    values: vec![AstExpr::Var(AstNameRef::Global(
                        crate::ast::AstGlobalName {
                            text: "setmetatable".to_owned(),
                        },
                    ))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: vec![crate::ast::AstTableField::Record(
                            crate::ast::AstRecordField {
                                key: crate::ast::AstTableKey::Name("name".to_owned()),
                                value: AstExpr::Var(AstNameRef::Param(ParamId(0))),
                            },
                        )],
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(2)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
                AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Local(LocalId(2)),
                        fields: vec!["__close".to_owned()],
                    }),
                    func: AstFunctionExpr {
                        function: HirProtoRef(2),
                        params: vec![ParamId(0), ParamId(1)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock { stmts: Vec::new() },
                        captured_bindings: Default::default(),
                    },
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(LocalId(1))),
                            AstExpr::Var(AstNameRef::Local(LocalId(2))),
                        ],
                    }))],
                })),
            ],
        },
    };

    let changed = run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua54),
    );
    assert!(changed);

    let [AstStmt::Return(ret)] = module.body.stmts.as_slice() else {
        panic!("expected terminal return call to absorb constructor prep locals");
    };
    let [AstExpr::Call(call)] = ret.values.as_slice() else {
        panic!("expected return call to remain a call expression");
    };
    assert!(matches!(
        &call.callee,
        AstExpr::Var(AstNameRef::Global(name)) if name.text == "setmetatable"
    ));
    assert!(matches!(
        &call.args[0],
        AstExpr::TableConstructor(table)
            if table.fields.len() == 1
    ));
    assert!(matches!(
        &call.args[1],
        AstExpr::TableConstructor(table)
            if matches!(
                table.fields.as_slice(),
                [crate::ast::AstTableField::Record(field)]
                    if matches!(&field.key, crate::ast::AstTableKey::Name(name) if name == "__close")
                        && matches!(field.value, AstExpr::FunctionExpr(_))
            )
    ));
}

#[test]
fn inlines_trailing_table_function_assignment_back_into_terminal_constructor_local() {
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
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: vec![crate::ast::AstTableField::Record(
                            crate::ast::AstRecordField {
                                key: crate::ast::AstTableKey::Name("branch".to_owned()),
                                value: AstExpr::TableConstructor(Box::new(AstTableConstructor {
                                    fields: Vec::new(),
                                })),
                            },
                        )],
                    }))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "pick".to_owned(),
                    }))],
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: vec![ParamId(0), ParamId(1)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock { stmts: Vec::new() },
                        captured_bindings: Default::default(),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(AstNameRef::Local(LocalId(0)))],
                })),
            ],
        },
    };

    let changed = run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
    );
    assert!(changed);

    let [AstStmt::LocalDecl(local_decl), AstStmt::Return(_)] = module.body.stmts.as_slice() else {
        panic!("expected constructor local and terminal return to remain");
    };
    let [AstExpr::TableConstructor(table)] = local_decl.values.as_slice() else {
        panic!("expected constructor local to stay a table literal");
    };
    assert!(matches!(
        table.fields.as_slice(),
        [crate::ast::AstTableField::Record(branch), crate::ast::AstTableField::Record(pick)]
            if matches!(&branch.key, crate::ast::AstTableKey::Name(name) if name == "branch")
                && matches!(&pick.key, crate::ast::AstTableKey::Name(name) if name == "pick")
                && matches!(pick.value, AstExpr::FunctionExpr(_))
    ));
}

#[test]
fn recovers_method_call_from_direct_field_alias_call_stmt() {
    let receiver = LocalId(0);
    let field_alias = LocalId(1);
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(field_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(receiver)),
                        field: "push".to_owned(),
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(field_alias)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(receiver)),
                            AstExpr::Integer(1),
                        ],
                    })),
                })),
            ],
        },
    };

    assert!(apply(
        &mut module,
        super::ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        },
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::CallStmt(call_stmt)]
            if matches!(
                &call_stmt.call,
                AstCallKind::MethodCall(call)
                    if matches!(call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(0))))
                        && call.method == "push"
                        && matches!(call.args.as_slice(), [AstExpr::Integer(1)])
            )
    ));
}

#[test]
fn chains_method_calls_after_recovering_alias_scaffolding() {
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
                    values: vec![AstExpr::Var(AstNameRef::Param(ParamId(0)))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "method1".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(2)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                        args: vec![AstExpr::Var(AstNameRef::Local(LocalId(0)))],
                    }))],
                })),
                AstStmt::CallStmt(Box::new(crate::ast::AstCallStmt {
                    call: AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                        receiver: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                        method: "method2".to_owned(),
                        args: vec![AstExpr::Integer(7)],
                    })),
                })),
            ],
        },
    };

    let changed = run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
    );
    assert!(changed);

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::CallStmt(call_stmt)]
            if matches!(
                &call_stmt.call,
                AstCallKind::MethodCall(call)
                    if matches!(
                        &call.receiver,
                        AstExpr::MethodCall(inner)
                            if matches!(inner.receiver, AstExpr::Var(AstNameRef::Param(ParamId(0))))
                                && inner.method == "method1"
                                && inner.args.is_empty()
                    ) && call.method == "method2"
                        && matches!(call.args.as_slice(), [AstExpr::Integer(7)])
            )
    ));
}
