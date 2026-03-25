//! 这些测试固定 Lua 5.3 主 pipeline 的 smoke 契约。
//!
//! 这里不尝试锁 HIR 的最终形状，只先确认：`lua5.3` 已经接进 decompile/CLI dialect
//! 选择，并且能稳定跑到 transform 和 HIR。

use unluac::decompile::{
    DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage, decompile,
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
}
