//! 这个文件承载 `ast::build::patterns` 模块的局部不变量测试。
//!
//! 我们在这里直接构造 HIR 片段，验证 AST build 是否把 method-call 相关的机械别名
//! 收回成更接近源码的 AST 形状。

use crate::ast::{AstCallKind, AstExpr, AstStmt, AstTargetDialect, lower_ast};
use crate::hir::{
    HirBlock, HirCallExpr, HirCallStmt, HirExpr, HirLocalDecl, HirModule, HirProto, HirProtoRef,
    HirReturn, HirStmt, HirTableAccess, LocalId, ParamId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

#[test]
fn lower_ast_recovers_method_call_from_field_alias_before_call() {
    let module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![HirProto {
            id: HirProtoRef(0),
            source: None,
            line_range: ProtoLineRange {
                defined_start: 0,
                defined_end: 0,
            },
            signature: ProtoSignature {
                num_params: 1,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![ParamId(0)],
            locals: vec![LocalId(0), LocalId(1), LocalId(2)],
            upvalues: Vec::new(),
            temps: Vec::new(),
            temp_debug_locals: Vec::new(),
            local_debug_hints: Vec::new(),
            body: HirBlock {
                stmts: vec![
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![LocalId(0)],
                        values: vec![HirExpr::ParamRef(ParamId(0))],
                    })),
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![LocalId(1)],
                        values: vec![HirExpr::TableAccess(Box::new(HirTableAccess {
                            base: HirExpr::ParamRef(ParamId(0)),
                            key: HirExpr::String("method1".to_owned()),
                        }))],
                    })),
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![LocalId(2)],
                        values: vec![HirExpr::Call(Box::new(HirCallExpr {
                            callee: HirExpr::LocalRef(LocalId(1)),
                            args: vec![HirExpr::LocalRef(LocalId(0))],
                            multiret: false,
                            method: true,
                        }))],
                    })),
                    HirStmt::CallStmt(Box::new(HirCallStmt {
                        call: HirCallExpr {
                            callee: HirExpr::TableAccess(Box::new(HirTableAccess {
                                base: HirExpr::LocalRef(LocalId(2)),
                                key: HirExpr::String("method2".to_owned()),
                            })),
                            args: vec![HirExpr::LocalRef(LocalId(2)), HirExpr::Integer(7)],
                            multiret: false,
                            method: true,
                        },
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        values: vec![HirExpr::ParamRef(ParamId(0))],
                    })),
                ],
            },
            children: Vec::new(),
        }],
    };

    let ast = lower_ast(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua51),
    )
    .expect("ast lowering should succeed");

    let [
        AstStmt::LocalDecl(alias),
        AstStmt::LocalDecl(method_result),
        AstStmt::CallStmt(call_stmt),
        AstStmt::Return(_),
    ] = ast.body.stmts.as_slice()
    else {
        panic!("expected alias + method-result + method-call + return layout");
    };

    assert!(matches!(
        alias.values.as_slice(),
        [AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0)))]
    ));
    assert!(matches!(
        method_result.values.as_slice(),
        [AstExpr::MethodCall(call)]
            if matches!(call.receiver, AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0))))
                && call.method == "method1"
                && call.args.is_empty()
    ));
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::MethodCall(call)
            if matches!(call.receiver, AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(2))))
                && call.method == "method2"
                && matches!(call.args.as_slice(), [AstExpr::Integer(7)])
    ));
}
