//! 这些测试固定 Lua 5.4 已经修好的回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::naming::NamingOptions;

mod decompile_pipeline {
    use super::*;

    #[test]
    fn lua54_transform_stage_reports_tbc_close_and_loadi() {
        let chunk =
            crate::support::compile_lua_case("lua5.4", "tests/lua_cases/lua5.4/01_tbc_close.lua");
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 transform stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Transform)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("lir dialect=lua5.4"), "{dump}");
        assert!(dump.contains("tbc "), "{dump}");
        assert!(dump.contains("close from"), "{dump}");
        assert!(dump.contains("get-table"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_runs_for_const_local_fixture() {
        let chunk =
            crate::support::compile_lua_case("lua5.4", "tests/lua_cases/lua5.4/02_const_local.lua");
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump HIR ====="), "{dump}");
        assert!(dump.contains("proto#0"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_models_tbc_as_structured_stmt() {
        let chunk =
            crate::support::compile_lua_case("lua5.4", "tests/lua_cases/lua5.4/01_tbc_close.lua");
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 hir stage should succeed for tbc fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("to-be-closed l"), "{dump}");
        assert!(!dump.contains("unstructured summary=tbc"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_materializes_goto_close_scopes_as_blocks() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 hir stage should succeed for goto close fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("block"), "{dump}");
        assert!(dump.contains("to-be-closed t10"), "{dump}");
        assert!(dump.contains("goto L1"), "{dump}");
        assert!(!dump.contains("close from r4"), "{dump}");
        assert!(!dump.contains("unstructured summary=close"), "{dump}");
    }

    #[test]
    fn lua54_ast_stage_absorbs_simple_tbc_into_local_close_decl() {
        let chunk =
            crate::support::compile_lua_case("lua5.4", "tests/lua_cases/lua5.4/01_tbc_close.lua");
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 ast stage should succeed for simple tbc fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("<close> ="), "{dump}");
        assert!(!dump.contains("to-be-closed"), "{dump}");
        assert!(!dump.contains("close from"), "{dump}");
    }

    #[test]
    fn lua54_ast_stage_absorbs_goto_close_fixture_once_close_scopes_are_recovered() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 ast stage should now succeed for goto close fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("do"), "{dump}");
        assert!(dump.contains("<close>"), "{dump}");
        assert!(dump.contains("goto"), "{dump}");
        // AST 阶段条件方向可能尚未优化，readability/generate 会把多余的 goto/label 收回。
        // 这里放宽到 ≤2，确保 AST 至少不做出无限退化。
        let goto_count = dump.matches("goto L").count();
        assert!(goto_count >= 1 && goto_count <= 2, "goto count={goto_count}\n{dump}");
        let label_count = dump.matches("::L").count();
        assert!(label_count >= 1 && label_count <= 2, "label count={label_count}\n{dump}");
        assert!(!dump.contains("close from"), "{dump}");
    }

    #[test]
    fn lua54_hir_stage_materializes_multi_exit_close_scopes_as_blocks() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/04_tbc_multi_exit.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 hir stage should succeed for multi-exit close fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("to-be-closed l1"), "{dump}");
        assert!(dump.contains("to-be-closed l2"), "{dump}");
        assert!(dump.contains("block"), "{dump}");
        assert!(!dump.contains("close from r2"), "{dump}");
        assert!(!dump.contains("close from r3"), "{dump}");
    }

    #[test]
    fn lua54_generate_stage_recovers_multi_exit_close_source_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/04_tbc_multi_exit.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 generate stage should succeed for multi-exit close fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("<close>"), "{}", generated.source);
        assert!(generated.source.contains("after:"), "{}", generated.source);
        assert!(
            generated.source.contains("return tbl"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("second:"), "{}", generated.source);
        assert!(
            generated
                .source
                .contains("return setmetatable({ name = a }, {")
                || generated
                    .source
                    .contains("return setmetatable({ name = mode }, {"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("__close = function("),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains(".. \"+\""),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("\"after:\" .."),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("close from"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua54_generate_stage_names_goto_close_capture_from_outer_local() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/05_tbc_goto_reenter.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 generate stage should succeed for goto close fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("local tbl = {}"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("#tbl + 1"),
            "{}",
            generated.source
        );
        assert_eq!(
            generated.source.matches("goto L").count(),
            1,
            "{}",
            generated.source
        );
        assert_eq!(
            generated.source.matches("::L").count(),
            1,
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("up2"), "{}", generated.source);
    }

    #[test]
    fn lua54_generate_stage_recovers_loop_closure_break_return_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/common/tricky/29_loop_closure_break_return.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 generate stage should succeed for loop closure break fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("while ")
                && generated.source.contains(" do")
                && generated.source.contains("break"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("return ok2 + b, ok")
                || generated.source.contains("return captured + extra, i"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("[#tbl + 1] = function(")
                || generated.source.contains("[#ok + 1] = function("),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua54_readability_stage_absorbs_generic_for_hidden_close_state_into_source_like_for_loop() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/07_generic_for_const_close.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
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
        .expect("lua5.4 readability stage should succeed for generic-for close fixture");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("for l0, l1, l2 in l5({\"aa\", \"bbb\", \"c\"}) do"),
            "{dump}"
        );
        assert!(dump.contains("<close> = l4("), "{dump}");
        assert!(!dump.contains("to-be-closed"), "{dump}");
        assert!(!dump.contains("local t9"), "{dump}");
    }

    #[test]
    fn lua54_generate_stage_recovers_vararg_const_pipeline_source_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.4/08_vararg_const_pipeline.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 generate stage should succeed for vararg const pipeline fixture");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(
            generated.source.contains("for i = 1, #tbl do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("if i % 2 == 0 then"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("\n        else\n"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains(".. \":\" .."),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("goto L"), "{}", generated.source);
        assert!(!generated.source.contains(", 1 do"), "{}", generated.source);
    }

    #[test]
    fn lua54_generate_stage_canonicalizes_shift_immediates_in_loop_bitwise_dispatch_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.4",
            "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua54,
                target_stage: DecompileStage::Generate,
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.4 generate stage should canonicalize loop_bitwise_dispatch shifts");

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
