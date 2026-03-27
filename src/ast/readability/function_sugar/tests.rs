//! 这个文件承载 `function_sugar` 模块的局部不变量测试。
//!
//! 这里主要验证两件事：
//! 1. 方法调用恢复出来之后，后续的 `obj.field = function(...)` 能正确降成方法声明；
//! 2. 没有 method-call 证据的字段函数仍然保留普通 `function obj.field(...)` 形状。

use super::apply;
use crate::ast::{
    AstAssign, AstBindingRef, AstBlock, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr,
    AstLValue, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstMethodCallExpr, AstModule,
    AstNamePath, AstNameRef, AstStmt, AstTableConstructor, AstTargetDialect,
};
use crate::hir::{HirProtoRef, LocalId, ParamId};
use crate::readability::ReadabilityOptions;

fn method_function(params: &[ParamId]) -> AstExpr {
    AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
        function: HirProtoRef(1),
        params: params.to_vec(),
        is_vararg: false,
        body: AstBlock {
            stmts: vec![AstStmt::Return(Box::new(crate::ast::AstReturn {
                values: vec![AstExpr::Var(AstNameRef::Param(params[0]))],
            }))],
        },
        captured_bindings: Default::default(),
    }))
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

    let changed = apply(
        &mut module,
        super::ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        },
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

    let changed = apply(
        &mut module,
        super::ReadabilityContext {
            target: AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
            options: ReadabilityOptions::default(),
        },
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
