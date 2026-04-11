//! 这些测试固定 Lua 5.5 已经修好的回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::naming::NamingOptions;

mod decompile_pipeline {
    use super::*;

    #[test]
    fn lua55_transform_stage_reports_errnnil() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/01_global_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Transform,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Transform],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 transform stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Transform)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("lir dialect=lua5.5"), "{dump}");
        assert!(dump.contains("err-nnil"), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_models_named_vararg_table_as_entry_local() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/03_named_vararg_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for named vararg fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local [\"l1\"] = l0[1]"), "{dump}");
        assert!(dump.contains("local [\"l3\"] = l0[l0[\"n\"]]"), "{dump}");
        assert!(dump.contains("assign l0[l5] = (l6 + p0)"), "{dump}");
        assert!(dump.contains("return l4, l0[\"n\"],"), "{dump}");
        assert!(!dump.contains("entry-reg"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_handles_named_vararg_return_without_unresolved_entry_reg() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/07_named_vararg_return.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for named vararg return fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("return l0"), "{dump}");
        assert!(!dump.contains("entry-reg"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_keeps_global_errnnil_explicit() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/06_global_named_vararg_pipeline.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for global pipeline fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("err-nnil") && dump.contains("name=registry"),
            "{dump}"
        );
        assert!(
            dump.contains("err-nnil") && dump.contains("name=install"),
            "{dump}"
        );
        assert!(!dump.contains("entry-reg"), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_models_hidden_vararg_parameter_for_getvarg_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/08_named_vararg_index_only.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for getvarg fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("return l0[p0], l0[(p0 - 1)], l0[\"n\"], ..."),
            "{dump}"
        );
        assert!(!dump.contains("entry-reg"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_preserves_add_negative_named_vararg_index_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/09_named_vararg_index_addneg.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should keep add-negative fixture shape");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("return l0[p0], l0[(p0 + -1)], l0[\"n\"], ..."),
            "{dump}"
        );
        assert!(!dump.contains("entry-reg"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
    }

    #[test]
    fn lua55_hir_stage_keeps_fixed_multiresult_call_as_multivalue_carrier() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/05_global_const_gate.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should preserve fixed multiresult call carrier");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("assign t5, t6 = call(normal) l3(\"abc\") multiret=true"),
            "{dump}"
        );
        assert!(
            !dump.contains("call(normal) l3(\"abc\") multiret=false"),
            "{dump}"
        );
        assert!(
            !dump.contains("local [\"l4\"] = call(normal) l3(\"abc\")"),
            "{dump}"
        );
    }

    #[test]
    fn lua55_ast_stage_recovers_global_decl_from_errnnil_pattern() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/01_global_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Ast,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Ast],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 ast stage should succeed for global fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("global label ="), "{dump}");
        assert!(dump.contains("global counter ="), "{dump}");
        assert!(dump.contains("local l5 = function(p0)"), "{dump}");
        assert!(dump.contains("counter = ((counter * 2) + p0)"), "{dump}");
        assert!(dump.contains("global step = l5"), "{dump}");
        assert!(!dump.contains("local t"), "{dump}");
        assert!(!dump.contains("err-nnil"), "{dump}");
    }

    #[test]
    fn lua55_readability_stage_sugars_global_function_declaration() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/01_global_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should succeed for global fixture");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Readability ====="), "{dump}");
        assert!(dump.contains("global function step(p0)"), "{dump}");
        assert!(!dump.contains("local l5 = function"), "{dump}");
        assert!(!dump.contains("global step = l5"), "{dump}");
    }

    #[test]
    fn lua55_readability_stage_sugars_local_function_declaration() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/07_named_vararg_return.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should succeed for local function fixture");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("global<const> print"), "{dump}");
        assert!(dump.contains("local function l1(p0, ...l0)"), "{dump}");
        assert!(dump.contains("if p0"), "{dump}");
        assert!(
            dump.contains("return {first = l0[1], last = l0[l0.n], n = l0.n}"),
            "{dump}"
        );
        assert!(!dump.contains("if (not p0)"), "{dump}");
        assert!(!dump.contains("do\n"), "{dump}");
        assert!(
            !dump.contains("local l1 = {first = l0[1], last = l0[l0.n], n = l0.n}"),
            "{dump}"
        );
        assert!(!dump.contains("local l1 = function(p0)"), "{dump}");
    }

    #[test]
    fn lua55_ast_stage_dumps_child_function_body_for_local_function_expr_value() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/07_named_vararg_return.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Ast,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Ast],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 ast stage should dump nested function body");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local l1 = function(p0, ...l0)"), "{dump}");
        assert!(dump.contains("if not p0 then"), "{dump}");
        assert!(!dump.contains("local l1 = function(p0) ... end"), "{dump}");
    }

    #[test]
    fn lua55_readability_stage_dumps_inline_function_expr_body_for_closure_mesh() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/04_named_vararg_closure_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should dump inline function body");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("global<const> print"), "{dump}");
        assert!(dump.contains("local function l1(p0, ...l0)"), "{dump}");
        assert!(dump.contains("local function l1(p0, p1)"), "{dump}");
        assert!(dump.contains("local function l6()"), "{dump}");
        assert!(dump.contains("local l7 = l6()"), "{dump}");
        assert!(
            dump.contains("print(\"var55-closure\", l1(2, 4, 7, 5))"),
            "{dump}"
        );
        assert!(!dump.contains("function(p0) ... end"), "{dump}");
        assert!(!dump.contains("end(-)"), "{dump}");
    }

    #[test]
    fn lua55_generate_stage_emits_final_source_for_global_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/01_global_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Generate],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for global fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated
                .source
                .contains("global counter, label = 9, \"seed\""),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("global function step(a)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("print(\"g55-basic\""),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local value"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("up."), "{}", generated.source);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Generate ====="), "{dump}");
        assert!(dump.contains("global function step(a)"), "{dump}");
    }

    #[test]
    fn lua55_generate_stage_emits_named_vararg_parameter_for_basic_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/03_named_vararg_basic.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for named vararg fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local function fn(a, ...value)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("return ")
                && generated.source.contains(", value.n,")
                && !generated.source.contains("return ok2, value.n"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("= value[1] * 10 + value[value.n]"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("value.n = value.n + 1"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("value[value.n] = value[1] + value[2] + a"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local function fn(a, ...)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_does_not_infer_const_global_prelude_for_const_gate_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/05_global_const_gate.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for global const fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            !generated.source.contains("global<const> math, tostring"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("do\n        global<const> *"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local function fn(a)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("local result, value4 = fn(\"abc\")"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("\nlocal value4\n"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_recovers_installer_iife_as_local_function_plus_call() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/02_global_function_capture.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should recover installer iife fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local function"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("global function emit"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("(\"ax\")"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("(function("),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("end)(\"ax\")"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_keeps_named_vararg_parameter_for_getvarg_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/08_named_vararg_index_only.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for getvarg fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local function fn(a, ...value)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("return value[a], value[a - 1], value.n, ..."),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"var55-getvarg\", fn(2, 4, 7, 5, 9))"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local result ="),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_preserves_add_negative_named_vararg_index_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/09_named_vararg_index_addneg.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should preserve add-negative fixture shape");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local function fn(a, ...value)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("return value[a], value[a + -1], value.n, ..."),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"var55-getvarg-addneg\", fn(2, 4, 7, 5, 9))"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local result ="),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_predeclares_outer_global_for_nested_global_function_capture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.5/02_global_function_capture.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for nested global function capture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("global emit"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("global function emit(b)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local function ")
                && generated.source.contains("(\"ax\")")
                && !generated.source.contains("(function("),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_recovers_generic_for_bindings_without_tbc_slot_shift() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/common/control_flow/04_generic_for.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should recover generic-for bindings");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("[#") && generated.source.contains(" .. \":\" .. "),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("value5"), "{}", generated.source);
    }

    #[test]
    fn lua55_generate_stage_recovers_generic_for_mutator_locals() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/common/tricky/11_generic_for_mutator.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should recover generic-for mutator locals");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated
                .source
                .contains("local value, value2, item = k, v, a[k]"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("value3"), "{}", generated.source);
    }

    #[test]
    fn lua55_generate_stage_keeps_self_field_for_impure_closure_counter() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/common/functions/07_closure_counter_impure_step.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for impure closure counter fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("function tbl:next()"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("(tbl:next() or 1)"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains(".next("), "{}", generated.source);
        assert!(
            generated.source.contains("value = value2 + (tbl:next() or 1)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_recovers_nested_table_method_index_case_without_spurious_globals() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/common/tricky/23_nested_table_call_index.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should succeed for nested table call/index fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("branch = {"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("pick = function("),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains(":pick(4)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("return b.branch[b2]"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local pick = result.pick"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local branch = b.branch"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("global<const>"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua55_generate_stage_canonicalizes_shift_immediates_in_loop_bitwise_dispatch_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.5",
            "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua55,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 generate stage should canonicalize loop_bitwise_dispatch shifts");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(!generated.source.contains(">> -"), "{}", generated.source);
        assert!(!generated.source.contains("<< -"), "{}", generated.source);
        assert!(generated.source.contains("while "), "{}", generated.source);
    }
}
