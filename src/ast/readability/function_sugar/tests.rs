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
