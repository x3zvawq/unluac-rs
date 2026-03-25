//! 这些测试固定 Lua 5.5 主 pipeline 的 smoke 契约。

use unluac::decompile::{
    DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage, decompile,
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
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for named vararg fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local [\"l1\"] = ((l0[1] * 10) + l0[l0[\"n\"]])"), "{dump}");
        assert!(dump.contains("assign l0[2] = (l0[2] + p0)"), "{dump}");
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
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for global pipeline fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("err-nnil") && dump.contains("name=registry"), "{dump}");
        assert!(dump.contains("err-nnil") && dump.contains("name=install"), "{dump}");
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
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 hir stage should succeed for getvarg fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("return l0[p0], l0[(p0 + -1)], l0[\"n\"], ..."), "{dump}");
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
        assert!(dump.contains("assign u0.counter = ((u0.counter Mul 2) Add p0)"), "{dump}");
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
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should succeed for global fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Readability));
        let dump = &result.debug_output[0].content;
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
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should succeed for local function fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Readability));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local function l1(p0)"), "{dump}");
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
        assert!(dump.contains("if (Not p0)"), "{dump}");
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
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.5 readability stage should dump inline function body");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Readability));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("call u0.print(\"var55-closure\", function(p0)"), "{dump}");
        assert!(dump.contains("local function l1(p0, p1)"), "{dump}");
        assert!(!dump.contains("function(p0) ... end"), "{dump}");
    }
}
