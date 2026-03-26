//! 这些测试固定 Lua 5.5 已经修好的回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};

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
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for getvarg fixture");

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
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should succeed for local function fixture");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local function l1(p0)"), "{dump}");
        assert!(dump.contains("if p0"), "{dump}");
        assert!(!dump.contains("if (not p0)"), "{dump}");
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
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 ast stage should dump nested function body");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local l1 = function(p0)"), "{dump}");
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
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should dump inline function body");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local function l1(p0)"), "{dump}");
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
            generated.source.contains("global label = value3"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("function step(a)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("print(\"g55-basic\""),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("up."), "{}", generated.source);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Generate ====="), "{dump}");
        assert!(dump.contains("function step(a)"), "{dump}");
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
            generated
                .source
                .contains("local result = value3.next(value3)"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local item = value3[value2]"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("value = value2 + (result or 1)"),
            "{}",
            generated.source
        );
    }
}
