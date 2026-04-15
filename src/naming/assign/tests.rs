//! 这个文件承载 `assign` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBindingRef, AstBlock, AstExpr, AstFieldAccess, AstFunctionExpr, AstIndexAccess,
    AstLocalAttr, AstLocalBinding, AstLocalDecl, AstModule, AstReturn, AstStmt,
    AstSyntheticLocalId,
};
use crate::hir::{
    HirBlock, HirCapture, HirClosureExpr, HirExpr, HirLocalDecl, HirModule, HirProto, HirProtoRef,
    HirReturn, HirStmt, LocalId, ParamId, TempId, UpvalueId,
};
use crate::naming::{NameSource, NamingMode, NamingOptions, assign_names};
use crate::parser::{ProtoLineRange, ProtoSignature};

#[test]
fn heuristic_mode_prefers_field_shape_for_local_chain() {
    let proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 4,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![ParamId(0), ParamId(1), ParamId(2), ParamId(3)],
        param_debug_hints: Vec::new(),
        locals: vec![LocalId(0), LocalId(1)],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
    };
    let hir = HirModule {
        entry: HirProtoRef(0),
        protos: vec![proto],
    };
    let ast = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(0))),
                            field: "branches".to_owned(),
                        })),
                        index: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(1))),
                    }))],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(1)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::IndexAccess(Box::new(AstIndexAccess {
                        base: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                            base: AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(0))),
                            field: "items".to_owned(),
                        })),
                        index: AstExpr::Var(crate::ast::AstNameRef::Param(ParamId(2))),
                    }))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(1)))],
                })),
            ],
        },
    };

    let names = assign_names(
        &ast,
        &hir,
        NamingOptions {
            mode: NamingMode::Heuristic,
            ..NamingOptions::default()
        },
    )
    .expect("naming should succeed");

    let function = names.function(HirProtoRef(0)).expect("function names");
    assert_eq!(function.locals[0].text, "branch");
    assert_eq!(function.locals[0].source, NameSource::FieldName);
    assert_eq!(function.locals[1].text, "item");
    assert_eq!(function.locals[1].source, NameSource::FieldName);
}

#[test]
fn debug_like_mode_uses_function_qualified_binding_ids() {
    let proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 2,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![ParamId(0), ParamId(1)],
        param_debug_hints: Vec::new(),
        locals: vec![LocalId(0), LocalId(1), LocalId(2)],
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: vec![TempId(0)],
        temp_debug_locals: vec![None],
        local_debug_hints: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
    };
    let hir = HirModule {
        entry: HirProtoRef(0),
        protos: vec![proto],
    };
    let ast = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(2)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Nil],
                })),
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Var(crate::ast::AstNameRef::Local(LocalId(2)))],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(crate::ast::AstNameRef::SyntheticLocal(
                        AstSyntheticLocalId(TempId(0)),
                    ))],
                })),
            ],
        },
    };

    let names = assign_names(
        &ast,
        &hir,
        NamingOptions {
            mode: NamingMode::DebugLike,
            debug_like_include_function: true,
        },
    )
    .expect("naming should succeed");

    let function = names.function(HirProtoRef(0)).expect("function names");
    assert_eq!(function.params[0].text, "p0_0");
    assert_eq!(function.locals[0].text, "r0_2");
    assert_eq!(function.locals[1].text, "r0_3");
    assert_eq!(function.locals[2].text, "r0_0");
    assert_eq!(
        function
            .synthetic_locals
            .get(&AstSyntheticLocalId(TempId(0)))
            .expect("synthetic local names")
            .text,
        "r0_1"
    );
}

#[test]
fn simple_mode_uses_underscore_for_unused_synthetic_local() {
    let proto = HirProto {
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
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: vec![TempId(0), TempId(1)],
        temp_debug_locals: vec![None, None],
        body: HirBlock::default(),
        children: Vec::new(),
    };
    let hir = HirModule {
        entry: HirProtoRef(0),
        protos: vec![proto],
    };
    let ast = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![
                        AstLocalBinding {
                            id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                        AstLocalBinding {
                            id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(1))),
                            attr: AstLocalAttr::None,
                            origin: crate::ast::AstLocalOrigin::Recovered,
                        },
                    ],
                    values: vec![AstExpr::Nil, AstExpr::Integer(1)],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::Var(crate::ast::AstNameRef::SyntheticLocal(
                        AstSyntheticLocalId(TempId(1)),
                    ))],
                })),
            ],
        },
    };

    let names = assign_names(&ast, &hir, NamingOptions::default())
        .expect("naming should succeed");

    let function = names.function(HirProtoRef(0)).expect("function names");
    assert_eq!(
        function
            .synthetic_locals
            .get(&AstSyntheticLocalId(TempId(0)))
            .expect("unused synthetic local")
            .text,
        "_"
    );
    assert_eq!(
        function
            .synthetic_locals
            .get(&AstSyntheticLocalId(TempId(1)))
            .expect("used synthetic local")
            .text,
        "value"
    );
}

#[test]
fn debug_like_mode_still_uses_self_for_method_receiver_param() {
    let proto = HirProto {
        id: HirProtoRef(0),
        source: None,
        line_range: ProtoLineRange {
            defined_start: 0,
            defined_end: 0,
        },
        signature: ProtoSignature {
            num_params: 2,
            is_vararg: false,
            has_vararg_param_reg: false,
            named_vararg_table: false,
        },
        params: vec![ParamId(0), ParamId(1)],
        param_debug_hints: Vec::new(),
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock::default(),
        children: Vec::new(),
    };

    let candidate = super::super::strategy::choose_param_candidate(
        &proto,
        ParamId(0),
        0,
        &super::super::common::FunctionNamingEvidence::default(),
        &super::super::common::FunctionHints {
            param_hints: std::iter::once((
                ParamId(0),
                super::super::common::CandidateHint {
                    text: "self".to_owned(),
                    source: NameSource::SelfParam,
                },
            ))
            .collect(),
            ..Default::default()
        },
        NamingOptions {
            mode: NamingMode::DebugLike,
            debug_like_include_function: true,
        },
    );

    assert_eq!(candidate.text, "self");
    assert_eq!(candidate.source, NameSource::SelfParam);
}

#[test]
fn capture_provenance_upvalue_keeps_parent_name_when_child_local_conflicts() {
    let parent = HirProto {
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
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: vec![LocalId(0)],
        local_debug_hints: Vec::new(),
        upvalues: Vec::new(),
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: vec![HirExpr::Nil],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    trailing_multiret: false,
                    values: vec![HirExpr::Closure(Box::new(HirClosureExpr {
                        proto: HirProtoRef(1),
                        captures: vec![HirCapture {
                            value: HirExpr::LocalRef(LocalId(0)),
                        }],
                    }))],
                })),
            ],
        },
        children: vec![HirProtoRef(1)],
    };
    let child = HirProto {
        id: HirProtoRef(1),
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
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: vec![LocalId(0)],
        local_debug_hints: Vec::new(),
        upvalues: vec![UpvalueId(0)],
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: vec![HirExpr::UpvalueRef(UpvalueId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
                    trailing_multiret: false,
                    values: vec![HirExpr::LocalRef(LocalId(0))],
                })),
            ],
        },
        children: Vec::new(),
    };
    let hir = HirModule {
        entry: HirProtoRef(0),
        protos: vec![parent, child],
    };
    let ast = AstModule {
        entry_function: HirProtoRef(0),
        body: AstBlock {
            stmts: vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: AstBindingRef::Local(LocalId(0)),
                        attr: AstLocalAttr::None,
                        origin: crate::ast::AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::Nil],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: Vec::new(),
                        is_vararg: false,
                        named_vararg: None,
                        body: AstBlock {
                            stmts: vec![
                                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: AstBindingRef::Local(LocalId(0)),
                                        attr: AstLocalAttr::None,
                                        origin: crate::ast::AstLocalOrigin::Recovered,
                                    }],
                                    values: vec![AstExpr::Var(crate::ast::AstNameRef::Upvalue(
                                        UpvalueId(0),
                                    ))],
                                })),
                                AstStmt::Return(Box::new(AstReturn {
                                    values: vec![AstExpr::Var(crate::ast::AstNameRef::Local(
                                        LocalId(0),
                                    ))],
                                })),
                            ],
                        },
                        captured_bindings: Default::default(),
                    }))],
                })),
            ],
        },
    };

    let names = assign_names(
        &ast,
        &hir,
        NamingOptions {
            mode: NamingMode::DebugLike,
            debug_like_include_function: true,
        },
    )
    .expect("naming should succeed");

    let parent_names = names.function(HirProtoRef(0)).expect("parent names");
    let child_names = names.function(HirProtoRef(1)).expect("child names");
    assert_eq!(parent_names.locals[0].text, "value");
    assert_eq!(child_names.upvalues[0].text, "value");
    assert_ne!(child_names.locals[0].text, "value");
}

#[test]
fn capture_provenance_temp_uses_parent_synthetic_local_name() {
    let child = HirProto {
        id: HirProtoRef(1),
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
        params: Vec::new(),
        param_debug_hints: Vec::new(),
        locals: Vec::new(),
        local_debug_hints: Vec::new(),
        upvalues: vec![UpvalueId(0)],
        upvalue_debug_hints: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![HirStmt::Return(Box::new(HirReturn {
                trailing_multiret: false,
                values: vec![HirExpr::UpvalueRef(UpvalueId(0))],
            }))],
        },
        children: Vec::new(),
    };

    let evidence = super::super::common::FunctionNamingEvidence {
        upvalue_capture_sources: vec![Some(super::super::common::CapturedBinding::Temp {
            parent: HirProtoRef(0),
            temp: TempId(0),
        })],
        ..Default::default()
    };
    let assigned_functions = vec![
        super::super::common::FunctionNameMap {
            synthetic_locals: std::iter::once((
                AstSyntheticLocalId(TempId(0)),
                super::super::common::NameInfo {
                    text: "outer_state".to_owned(),
                    source: NameSource::DebugLike,
                    renamed: false,
                },
            ))
            .collect(),
            ..Default::default()
        },
        super::super::common::FunctionNameMap::default(),
    ];

    let candidate = super::super::strategy::choose_upvalue_candidate(
        &child,
        0,
        &evidence,
        NamingOptions::default(),
        &assigned_functions,
    )
    .expect("upvalue candidate should resolve synthetic-local provenance");

    assert_eq!(candidate.text, "outer_state");
    assert_eq!(candidate.source, NameSource::CaptureProvenance);
}
