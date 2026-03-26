//! 这些测试固定 Lua 5.3 已经修好的回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};

mod decompile_pipeline {
    use super::*;

    #[test]
    fn lua53_transform_stage_reports_lir_with_bitwise_ops() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.3/07_bnot_mask_pipeline.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua53,
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
        .expect("lua5.3 transform stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Transform)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("lir dialect=lua5.3"), "{dump}");
        assert!(dump.contains("bit-not"), "{dump}");
        assert!(dump.contains("floor-div"), "{dump}");
    }

    #[test]
    fn lua53_hir_stage_runs_for_loop_bitwise_dispatch_fixture() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua53,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.3 hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump HIR ====="), "{dump}");
        assert!(dump.contains("proto#0"), "{dump}");
    }

    #[test]
    fn lua53_hir_stage_keeps_idiv_float_branching_fixture_structured() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.3/03_idiv_float_branching.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua53,
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Hir],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.3 hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("numeric-for"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
    }

    #[test]
    fn lua53_readability_stage_merges_adjacent_local_decl_and_uses_lua_like_dump_syntax() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.3/03_idiv_float_branching.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua53,
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
        .expect("lua5.3 readability stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Readability)
        );
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("local l1, l2, l3, l4"), "{dump}");
        assert!(dump.contains("local function l0(p0)"), "{dump}");
        assert!(
            dump.contains("l1, l2, l3, l4 = l0({5, 8, 13, 21, 34})"),
            "{dump}"
        );
        assert!(dump.contains("for l0 = l3, l4, l5 do"), "{dump}");
        assert!(dump.contains("::L1::"), "{dump}");
        assert!(!dump.contains("assign "), "{dump}");
        assert!(!dump.contains("numeric-for "), "{dump}");
    }
}
