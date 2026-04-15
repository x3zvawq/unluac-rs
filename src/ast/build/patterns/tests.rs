//! 这个文件承载 `ast::build::patterns` 模块的局部不变量测试。
//!
//! 我们在这里直接构造 HIR 片段，验证 AST build 只负责“合法 AST 化”，
//! 不再提前替 Readability 收回 method-call / installer-iife 这类源码 sugar。

use crate::ast::{AstCallKind, AstExpr, AstStmt, AstTargetDialect, lower_ast};
use crate::generate::GenerateMode;
use crate::hir::{
    HirBlock, HirCallExpr, HirCallStmt, HirClosureExpr, HirExpr, HirGlobalRef, HirLocalDecl,
    HirModule, HirProto, HirProtoRef, HirReturn, HirStmt, HirTableAccess, LocalId, ParamId,
};
use crate::parser::{ProtoLineRange, ProtoSignature};

#[test]
fn lower_ast_preserves_method_call_alias_scaffolding_for_readability() {
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
            param_debug_hints: Vec::new(),
            locals: vec![LocalId(0), LocalId(1), LocalId(2)],
            upvalues: Vec::new(),
            upvalue_debug_hints: Vec::new(),
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
                            method_name: None,
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
                            method_name: Some("method2".to_owned()),
                        },
                    })),
                    HirStmt::Return(Box::new(HirReturn {
                        trailing_multiret: false,
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
        GenerateMode::Strict,
    )
    .expect("ast lowering should succeed");

    let [
        AstStmt::LocalDecl(receiver_alias),
        AstStmt::LocalDecl(field_alias),
        AstStmt::LocalDecl(method_result),
        AstStmt::CallStmt(call_stmt),
        AstStmt::Return(_),
    ] = ast.body.stmts.as_slice()
    else {
        panic!(
            "expected receiver alias + field alias + call carrier + method-call + return layout"
        );
    };

    assert!(matches!(
        receiver_alias.values.as_slice(),
        [AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0)))]
    ));
    assert!(matches!(
        field_alias.values.as_slice(),
        [AstExpr::FieldAccess(access)]
            if matches!(access.base, AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0))))
                && access.field == "method1"
    ));
    assert!(matches!(
        method_result.values.as_slice(),
        [AstExpr::Call(call)]
            if matches!(&call.callee, AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(1))))
                && matches!(
                    call.args.as_slice(),
                    [AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(0)))]
                )
    ));
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::MethodCall(call)
            if matches!(call.receiver, AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(2))))
                && call.method == "method2"
                && matches!(call.args.as_slice(), [AstExpr::Integer(7)])
    ));
}

#[test]
fn lower_ast_forwards_multiret_call_carrier_into_final_call_arg() {
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
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![],
            param_debug_hints: Vec::new(),
            locals: vec![LocalId(0)],
            upvalues: Vec::new(),
            upvalue_debug_hints: Vec::new(),
            temps: Vec::new(),
            temp_debug_locals: Vec::new(),
            local_debug_hints: Vec::new(),
            body: HirBlock {
                stmts: vec![
                    HirStmt::LocalDecl(Box::new(HirLocalDecl {
                        bindings: vec![LocalId(0)],
                        values: vec![HirExpr::Call(Box::new(HirCallExpr {
                            callee: HirExpr::GlobalRef(HirGlobalRef {
                                name: "probe".to_owned(),
                            }),
                            args: vec![HirExpr::Integer(2), HirExpr::Integer(4)],
                            multiret: true,
                            method: false,
                            method_name: None,
                        }))],
                    })),
                    HirStmt::CallStmt(Box::new(HirCallStmt {
                        call: HirCallExpr {
                            callee: HirExpr::GlobalRef(HirGlobalRef {
                                name: "print".to_owned(),
                            }),
                            args: vec![
                                HirExpr::String("var55-getvarg".to_owned()),
                                HirExpr::LocalRef(LocalId(0)),
                            ],
                            multiret: false,
                            method: false,
                            method_name: None,
                        },
                    })),
                ],
            },
            children: Vec::new(),
        }],
    };

    let ast = lower_ast(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        GenerateMode::Strict,
    )
    .expect("ast lowering should forward multiret call carrier");

    let [AstStmt::CallStmt(call_stmt)] = ast.body.stmts.as_slice() else {
        panic!("expected direct call statement without forwarding local");
    };

    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(&call.callee, AstExpr::Var(crate::ast::AstNameRef::Global(global)) if global.text == "print")
                && matches!(call.args.as_slice(),
                    [
                        AstExpr::String(tag),
                        AstExpr::Call(inner_call)
                    ] if tag == "var55-getvarg"
                        && matches!(&inner_call.callee, AstExpr::Var(crate::ast::AstNameRef::Global(global)) if global.text == "probe")
                        && matches!(inner_call.args.as_slice(), [AstExpr::Integer(2), AstExpr::Integer(4)])
                )
    ));
}

#[test]
fn lower_ast_preserves_installer_iife_scaffolding_for_readability() {
    let module = HirModule {
        entry: HirProtoRef(0),
        protos: vec![
            HirProto {
                id: HirProtoRef(0),
                source: None,
                line_range: ProtoLineRange {
                    defined_start: 0,
                    defined_end: 0,
                },
                signature: ProtoSignature {
                    num_params: 0,
                    is_vararg: false,
                    has_vararg_param_reg: false,
                    named_vararg_table: false,
                },
                params: vec![],
                param_debug_hints: Vec::new(),
                locals: vec![],
                upvalues: Vec::new(),
                upvalue_debug_hints: Vec::new(),
                temps: Vec::new(),
                temp_debug_locals: Vec::new(),
                local_debug_hints: Vec::new(),
                body: HirBlock {
                    stmts: vec![HirStmt::CallStmt(Box::new(HirCallStmt {
                        call: HirCallExpr {
                            callee: HirExpr::Closure(Box::new(HirClosureExpr {
                                proto: HirProtoRef(1),
                                captures: Vec::new(),
                            })),
                            args: vec![HirExpr::String("ax".to_owned())],
                            multiret: false,
                            method: false,
                            method_name: None,
                        },
                    }))],
                },
                children: vec![HirProtoRef(1)],
            },
            HirProto {
                id: HirProtoRef(1),
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
                param_debug_hints: Vec::new(),
                locals: vec![LocalId(0)],
                upvalues: Vec::new(),
                upvalue_debug_hints: Vec::new(),
                temps: Vec::new(),
                temp_debug_locals: Vec::new(),
                local_debug_hints: Vec::new(),
                body: HirBlock {
                    stmts: vec![
                        HirStmt::LocalDecl(Box::new(HirLocalDecl {
                            bindings: vec![LocalId(0)],
                            values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                                proto: HirProtoRef(2),
                                captures: Vec::new(),
                            }))],
                        })),
                        HirStmt::Assign(Box::new(crate::hir::HirAssign {
                            targets: vec![crate::hir::HirLValue::Global(HirGlobalRef {
                                name: "emit".to_owned(),
                            })],
                            values: vec![HirExpr::LocalRef(LocalId(0))],
                        })),
                        HirStmt::Return(Box::new(HirReturn { trailing_multiret: false, values: vec![] })),
                    ],
                },
                children: vec![HirProtoRef(2)],
            },
            HirProto {
                id: HirProtoRef(2),
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
                param_debug_hints: Vec::new(),
                locals: vec![],
                upvalues: Vec::new(),
                upvalue_debug_hints: Vec::new(),
                temps: Vec::new(),
                temp_debug_locals: Vec::new(),
                local_debug_hints: Vec::new(),
                body: HirBlock {
                    stmts: vec![HirStmt::Return(Box::new(HirReturn {
                        trailing_multiret: false,
                        values: vec![HirExpr::ParamRef(ParamId(0))],
                    }))],
                },
                children: Vec::new(),
            },
        ],
    };

    let ast = lower_ast(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Lua55),
        GenerateMode::Strict,
    )
    .expect("ast lowering should preserve installer iife for readability");

    let [AstStmt::CallStmt(call_stmt)] = ast.body.stmts.as_slice() else {
        panic!("expected direct iife call to stay in ast build output");
    };
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(&call.callee, AstExpr::FunctionExpr(_))
                && matches!(call.args.as_slice(), [AstExpr::String(tag)] if tag == "ax")
    ));
}

#[test]
fn lower_ast_marks_single_value_final_call_arg_explicitly() {
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
                num_params: 0,
                is_vararg: false,
                has_vararg_param_reg: false,
                named_vararg_table: false,
            },
            params: vec![],
            param_debug_hints: Vec::new(),
            locals: vec![],
            upvalues: Vec::new(),
            upvalue_debug_hints: Vec::new(),
            temps: vec![],
            temp_debug_locals: Vec::new(),
            local_debug_hints: Vec::new(),
            body: HirBlock {
                stmts: vec![HirStmt::CallStmt(Box::new(HirCallStmt {
                    call: HirCallExpr {
                        callee: HirExpr::GlobalRef(HirGlobalRef {
                            name: "print".to_owned(),
                        }),
                        args: vec![
                            HirExpr::String("assign-rot".to_owned()),
                            HirExpr::Call(Box::new(HirCallExpr {
                                callee: HirExpr::GlobalRef(HirGlobalRef {
                                    name: "values".to_owned(),
                                }),
                                args: vec![],
                                multiret: false,
                                method: false,
                                method_name: None,
                            })),
                        ],
                        multiret: false,
                        method: false,
                        method_name: None,
                    },
                }))],
            },
            children: Vec::new(),
        }],
    };

    let ast = lower_ast(
        &module,
        AstTargetDialect::new(crate::ast::AstDialectVersion::Luau),
        GenerateMode::Strict,
    )
    .expect("ast lowering should preserve final single-value call args");

    let [AstStmt::CallStmt(call_stmt)] = ast.body.stmts.as_slice() else {
        panic!("expected direct call statement with explicit single-value final arg");
    };
    assert!(matches!(
        &call_stmt.call,
        AstCallKind::Call(call)
            if matches!(&call.callee, AstExpr::Var(crate::ast::AstNameRef::Global(global)) if global.text == "print")
                && matches!(call.args.as_slice(),
                    [
                        AstExpr::String(tag),
                        AstExpr::SingleValue(inner)
                    ] if tag == "assign-rot"
                        && matches!(
                            inner.as_ref(),
                            AstExpr::Call(inner_call)
                                if matches!(&inner_call.callee, AstExpr::Var(crate::ast::AstNameRef::Global(global)) if global.text == "values")
                                    && inner_call.args.is_empty()
                        ))
    ));
}
