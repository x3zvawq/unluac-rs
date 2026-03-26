//! 这个文件承载 `assign` 模块的局部不变量测试。
//!
//! 我们把测试和实现分开存放，避免主实现文件被大段 `#[cfg(test)]` 代码淹没。

use crate::ast::{
    AstBindingRef, AstBlock, AstExpr, AstFieldAccess, AstIndexAccess, AstLocalAttr,
    AstLocalBinding, AstLocalDecl, AstModule, AstReturn, AstStmt, AstSyntheticLocalId,
};
use crate::hir::{HirBlock, HirModule, HirProto, HirProtoRef, LocalId, ParamId, TempId};
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
