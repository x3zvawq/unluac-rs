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
use crate::parser::{
    ChunkHeader, Dialect, DialectConstPoolExtra, DialectDebugExtra, DialectHeaderExtra,
    DialectProtoExtra, DialectUpvalueExtra, DialectVersion, Endianness, Origin, ProtoFrameInfo,
    ProtoLineRange, ProtoSignature, RawChunk, RawConstPool, RawConstPoolCommon, RawDebugInfo,
    RawDebugInfoCommon, RawProto, RawProtoCommon, RawUpvalueInfo, RawUpvalueInfoCommon, Span,
};
use crate::parser::{
    Lua51ConstPoolExtra, Lua51DebugExtra, Lua51HeaderExtra, Lua51ProtoExtra, Lua51UpvalueExtra,
};

fn empty_raw_chunk() -> RawChunk {
    let origin = Origin {
        span: Span { offset: 0, size: 0 },
        raw_word: None,
    };
    RawChunk {
        header: ChunkHeader {
            dialect: Dialect::PucLua,
            version: DialectVersion::Lua51,
            format: 0,
            endianness: Endianness::Little,
            integer_size: 4,
            lua_integer_size: None,
            size_t_size: 4,
            instruction_size: 4,
            number_size: 8,
            integral_number: false,
            extra: DialectHeaderExtra::Lua51(Lua51HeaderExtra),
            origin,
        },
        main: RawProto {
            common: RawProtoCommon {
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
                frame: ProtoFrameInfo { max_stack_size: 4 },
                instructions: Vec::new(),
                constants: RawConstPool {
                    common: RawConstPoolCommon {
                        literals: Vec::new(),
                    },
                    extra: DialectConstPoolExtra::Lua51(Lua51ConstPoolExtra),
                },
                upvalues: RawUpvalueInfo {
                    common: RawUpvalueInfoCommon {
                        count: 0,
                        descriptors: Vec::new(),
                    },
                    extra: DialectUpvalueExtra::Lua51(Lua51UpvalueExtra),
                },
                debug_info: RawDebugInfo {
                    common: RawDebugInfoCommon {
                        line_info: Vec::new(),
                        local_vars: Vec::new(),
                        upvalue_names: Vec::new(),
                    },
                    extra: DialectDebugExtra::Lua51(Lua51DebugExtra),
                },
                children: Vec::new(),
            },
            extra: DialectProtoExtra::Lua51(Lua51ProtoExtra { raw_is_vararg: 0 }),
            origin,
        },
        origin,
    }
}

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
        locals: vec![LocalId(0), LocalId(1)],
        upvalues: Vec::new(),
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
        &empty_raw_chunk(),
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
        locals: vec![LocalId(0)],
        upvalues: Vec::new(),
        temps: vec![TempId(0)],
        temp_debug_locals: vec![None],
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
                        id: AstBindingRef::SyntheticLocal(AstSyntheticLocalId(TempId(0))),
                        attr: AstLocalAttr::None,
                    }],
                    values: vec![AstExpr::Nil],
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
        &empty_raw_chunk(),
        NamingOptions {
            mode: NamingMode::DebugLike,
            debug_like_include_function: true,
        },
    )
    .expect("naming should succeed");

    let function = names.function(HirProtoRef(0)).expect("function names");
    assert_eq!(function.params[0].text, "p0_0");
    assert_eq!(function.locals[0].text, "r0_0");
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
fn capture_provenance_upvalue_keeps_parent_name_when_child_local_conflicts() {
    let mut raw = empty_raw_chunk();
    raw.main.common.children.push(raw.main.clone());

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
        locals: vec![LocalId(0)],
        upvalues: Vec::new(),
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: vec![HirExpr::Nil],
                })),
                HirStmt::Return(Box::new(HirReturn {
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
        locals: vec![LocalId(0)],
        upvalues: vec![UpvalueId(0)],
        temps: Vec::new(),
        temp_debug_locals: Vec::new(),
        body: HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: vec![HirExpr::UpvalueRef(UpvalueId(0))],
                })),
                HirStmt::Return(Box::new(HirReturn {
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
                    }],
                    values: vec![AstExpr::Nil],
                })),
                AstStmt::Return(Box::new(AstReturn {
                    values: vec![AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
                        function: HirProtoRef(1),
                        params: Vec::new(),
                        is_vararg: false,
                        body: AstBlock {
                            stmts: vec![
                                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                    bindings: vec![AstLocalBinding {
                                        id: AstBindingRef::Local(LocalId(0)),
                                        attr: AstLocalAttr::None,
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
                    }))],
                })),
            ],
        },
    };

    let names =
        assign_names(&ast, &hir, &raw, NamingOptions::default()).expect("naming should succeed");

    let parent_names = names.function(HirProtoRef(0)).expect("parent names");
    let child_names = names.function(HirProtoRef(1)).expect("child names");
    assert_eq!(parent_names.locals[0].text, "value");
    assert_eq!(child_names.upvalues[0].text, "value");
    assert_ne!(child_names.locals[0].text, "value");
}
