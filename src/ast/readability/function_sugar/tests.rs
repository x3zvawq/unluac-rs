//! 这个文件承载 `function_sugar` 模块的局部不变量测试。
//!
//! 这里主要验证两件事：
//! 1. 方法调用恢复出来之后，后续的 `obj.field = function(...)` 能正确降成方法声明；
//! 2. 没有 method-call 证据的字段函数仍然保留普通 `function obj.field(...)` 形状。

use super::apply;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallExpr, AstCallKind, AstExpr, AstFieldAccess,
    AstFunctionDecl, AstFunctionExpr, AstFunctionName, AstIf, AstLValue, AstLocalAttr,
    AstLocalBinding, AstLocalDecl, AstMethodCallExpr, AstModule, AstNamePath, AstNameRef,
    AstReturn, AstStmt, AstTableConstructor, AstTargetDialect,
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
fn inlines_nested_constructor_locals_into_terminal_local_call_initializer() {
    let result = LocalId(4);
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
                    values: vec![AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "ffi".to_owned(),
                        })),
                        field: "metatype".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::String("counter_t".to_owned())],
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
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(3)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
                AstStmt::FunctionDecl(Box::new(AstFunctionDecl {
                    target: AstFunctionName::Plain(AstNamePath {
                        root: AstNameRef::Local(LocalId(3)),
                        fields: vec!["bump".to_owned()],
                    }),
                    func: AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: vec![ParamId(0), ParamId(1)],
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock { stmts: Vec::new() },
                        captured_bindings: Default::default(),
                    },
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(2))),
                        field: "__index".to_owned(),
                    }))],
                    values: vec![AstExpr::Var(AstNameRef::Local(LocalId(3)))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(result),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
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
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    );
    assert!(changed);

    let [AstStmt::LocalDecl(local_decl)] = module.body.stmts.as_slice() else {
        panic!("expected terminal local call initializer to absorb constructor prep locals");
    };
    let [AstExpr::Call(call)] = local_decl.values.as_slice() else {
        panic!("expected local initializer to remain a call expression");
    };
    assert!(matches!(
        &call.callee,
        AstExpr::FieldAccess(access)
            if matches!(
                &access.base,
                AstExpr::Var(AstNameRef::Global(name)) if name.text == "ffi"
            ) && access.field == "metatype"
    ));
    assert!(matches!(
        call.args.as_slice(),
        [AstExpr::String(name), AstExpr::TableConstructor(meta)]
            if name == "counter_t"
                && matches!(
                    meta.fields.as_slice(),
                    [crate::ast::AstTableField::Record(index_field)]
                        if matches!(
                            &index_field.key,
                            crate::ast::AstTableKey::Name(field) if field == "__index"
                        ) && matches!(
                            &index_field.value,
                            AstExpr::TableConstructor(methods)
                                if matches!(
                                    methods.fields.as_slice(),
                                    [crate::ast::AstTableField::Record(method_field)]
                                        if matches!(
                                            &method_field.key,
                                            crate::ast::AstTableKey::Name(field) if field == "bump"
                                        ) && matches!(method_field.value, AstExpr::FunctionExpr(_))
                                )
                        )
                )
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

#[test]
fn recovers_method_alias_inside_truthy_ternary_local_initializer() {
    let receiver = LocalId(0);
    let field_alias = LocalId(1);
    let result = LocalId(2);
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
                        field: "find".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(result),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::LogicalAnd(Box::new(crate::ast::AstLogicalExpr {
                            lhs: AstExpr::Call(Box::new(AstCallExpr {
                                callee: AstExpr::Var(AstNameRef::Local(field_alias)),
                                args: vec![
                                    AstExpr::Var(AstNameRef::Local(receiver)),
                                    AstExpr::String("%-".to_owned()),
                                ],
                            })),
                            rhs: AstExpr::String("neg".to_owned()),
                        })),
                        rhs: AstExpr::String("pos".to_owned()),
                    }))],
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
        [AstStmt::LocalDecl(local_decl)]
            if matches!(
                local_decl.values.as_slice(),
                [AstExpr::LogicalOr(or_expr)]
                    if matches!(
                        &or_expr.lhs,
                        AstExpr::LogicalAnd(and_expr)
                            if matches!(
                                &and_expr.lhs,
                                AstExpr::MethodCall(call)
                                    if matches!(call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(0))))
                                        && call.method == "find"
                                        && matches!(call.args.as_slice(), [AstExpr::String(pattern)] if pattern == "%-")
                            ) && matches!(&and_expr.rhs, AstExpr::String(value) if value == "neg")
                    ) && matches!(&or_expr.rhs, AstExpr::String(value) if value == "pos")
            )
    ));
}

#[test]
fn recovers_direct_method_call_inside_truthy_ternary_local_initializer() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Local(LocalId(0)),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                    lhs: AstExpr::LogicalAnd(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                base: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                                field: "find".to_owned(),
                            })),
                            args: vec![
                                AstExpr::Var(AstNameRef::Local(LocalId(1))),
                                AstExpr::String("%-".to_owned()),
                            ],
                        })),
                        rhs: AstExpr::String("neg".to_owned()),
                    })),
                    rhs: AstExpr::String("pos".to_owned()),
                }))],
            }))],
        },
    };

    assert!(run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::LocalDecl(local_decl)]
            if matches!(
                local_decl.values.as_slice(),
                [AstExpr::LogicalOr(or_expr)]
                    if matches!(
                        &or_expr.lhs,
                        AstExpr::LogicalAnd(and_expr)
                            if matches!(
                                &and_expr.lhs,
                                AstExpr::MethodCall(call)
                                    if matches!(call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(1))))
                                        && call.method == "find"
                                        && matches!(call.args.as_slice(), [AstExpr::String(pattern)] if pattern == "%-")
                            ) && matches!(&and_expr.rhs, AstExpr::String(value) if value == "neg")
                    ) && matches!(&or_expr.rhs, AstExpr::String(value) if value == "pos")
            )
    ));
}

#[test]
fn recovers_direct_method_call_in_if_condition() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::If(Box::new(AstIf {
                cond: AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "find".to_owned(),
                    })),
                    args: vec![
                        AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        AstExpr::String("%-".to_owned()),
                    ],
                })),
                then_block: AstBlock { stmts: vec![] },
                else_block: None,
            }))],
        },
    };

    assert!(run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::If(if_stmt)]
            if matches!(
                &if_stmt.cond,
                AstExpr::MethodCall(call)
                    if matches!(call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(0))))
                        && call.method == "find"
                        && matches!(call.args.as_slice(), [AstExpr::String(pattern)] if pattern == "%-")
            )
    ));
}

#[test]
fn recovers_method_alias_in_if_condition() {
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
                        field: "find".to_owned(),
                    }))],
                })),
                AstStmt::If(Box::new(AstIf {
                    cond: AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(field_alias)),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(receiver)),
                            AstExpr::String("%-".to_owned()),
                        ],
                    })),
                    then_block: AstBlock { stmts: vec![] },
                    else_block: None,
                })),
            ],
        },
    };

    assert!(run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::If(if_stmt)]
            if matches!(
                &if_stmt.cond,
                AstExpr::MethodCall(call)
                    if matches!(call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(0))))
                        && call.method == "find"
                        && matches!(call.args.as_slice(), [AstExpr::String(pattern)] if pattern == "%-")
            )
    ));
}

#[test]
fn keeps_direct_call_in_truthy_ternary_when_receiver_is_not_a_simple_name() {
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Local(LocalId(0)),
                    attr: AstLocalAttr::None,
                    origin: crate::ast::AstLocalOrigin::Recovered,
                }],
                values: vec![AstExpr::LogicalOr(Box::new(crate::ast::AstLogicalExpr {
                    lhs: AstExpr::LogicalAnd(Box::new(crate::ast::AstLogicalExpr {
                        lhs: AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                base: AstExpr::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                                    args: vec![],
                                })),
                                field: "find".to_owned(),
                            })),
                            args: vec![
                                AstExpr::Call(Box::new(AstCallExpr {
                                    callee: AstExpr::Var(AstNameRef::Local(LocalId(1))),
                                    args: vec![],
                                })),
                                AstExpr::String("%-".to_owned()),
                            ],
                        })),
                        rhs: AstExpr::String("neg".to_owned()),
                    })),
                    rhs: AstExpr::String("pos".to_owned()),
                }))],
            }))],
        },
    };

    assert!(!run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));
    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::LocalDecl(local_decl)]
            if matches!(local_decl.values.as_slice(), [AstExpr::LogicalOr(_)])
    ));
}

#[test]
fn recovers_method_alias_inside_nested_call_argument() {
    let receiver = LocalId(0);
    let field_alias = LocalId(1);
    let result = LocalId(2);
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
                        field: "match".to_owned(),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(result),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(crate::ast::AstGlobalName {
                            text: "tonumber".to_owned(),
                        })),
                        args: vec![AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::Var(AstNameRef::Local(field_alias)),
                            args: vec![
                                AstExpr::Var(AstNameRef::Local(receiver)),
                                AstExpr::String("(%d+)i$".to_owned()),
                            ],
                        }))],
                    }))],
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
        [AstStmt::LocalDecl(local_decl)]
            if matches!(
                local_decl.values.as_slice(),
                [AstExpr::Call(call)]
                    if matches!(
                        call.args.as_slice(),
                        [AstExpr::MethodCall(method_call)]
                            if matches!(
                                &method_call.receiver,
                                AstExpr::Var(AstNameRef::Local(LocalId(0)))
                            ) && method_call.method == "match"
                                && matches!(
                                    method_call.args.as_slice(),
                                    [AstExpr::String(pattern)] if pattern == "(%d+)i$"
                                )
                    )
            )
    ));
}

#[test]
fn recovers_direct_method_call_with_receiver_alias_local() {
    let receiver = LocalId(0);
    let receiver_alias = LocalId(1);
    let result = LocalId(2);
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(receiver_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(receiver))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(result),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(AstNameRef::Local(receiver)),
                            field: "bump".to_owned(),
                        })),
                        args: vec![
                            AstExpr::Var(AstNameRef::Local(receiver_alias)),
                            AstExpr::Integer(7),
                        ],
                    }))],
                })),
            ],
        },
    };

    assert!(run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::LocalDecl(local_decl)]
            if matches!(
                local_decl.values.as_slice(),
                [AstExpr::MethodCall(call)]
                    if matches!(&call.receiver, AstExpr::Var(AstNameRef::Local(LocalId(0))))
                        && call.method == "bump"
                        && matches!(call.args.as_slice(), [AstExpr::Integer(7)])
            )
    ));
}

#[test]
fn recovers_nested_direct_method_call_with_receiver_alias_local_in_assign_value() {
    let receiver = LocalId(0);
    let receiver_alias = LocalId(1);
    let acc = LocalId(2);
    let mut module = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(receiver_alias),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(AstNameRef::Local(receiver))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(AstNameRef::Local(acc))],
                    values: vec![AstExpr::Binary(Box::new(crate::ast::AstBinaryExpr {
                        op: crate::ast::AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(AstNameRef::Local(acc)),
                        rhs: AstExpr::Call(Box::new(AstCallExpr {
                            callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                                base: AstExpr::Var(AstNameRef::Local(receiver)),
                                field: "bump".to_owned(),
                            })),
                            args: vec![
                                AstExpr::Var(AstNameRef::Local(receiver_alias)),
                                AstExpr::Integer(7),
                            ],
                        })),
                    }))],
                })),
            ],
        },
    };

    assert!(run_function_sugar_to_fixed_point(
        &mut module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::LuaJit),
    ));

    assert!(matches!(
        module.body.stmts.as_slice(),
        [AstStmt::Assign(assign)]
            if matches!(
                assign.values.as_slice(),
                [AstExpr::Binary(binary)]
                    if matches!(&binary.lhs, AstExpr::Var(AstNameRef::Local(LocalId(2))))
                        && matches!(
                            &binary.rhs,
                            AstExpr::MethodCall(call)
                                if matches!(
                                    &call.receiver,
                                    AstExpr::Var(AstNameRef::Local(LocalId(0)))
                                ) && call.method == "bump"
                                    && matches!(call.args.as_slice(), [AstExpr::Integer(7)])
                        )
            )
    ));
}
