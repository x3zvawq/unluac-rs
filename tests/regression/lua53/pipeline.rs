//! 这些测试固定 Lua 5.3 已经修好的回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::naming::NamingOptions;

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
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
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
    fn lua53_generate_stage_keeps_cross_loop_goto_break_like_case_structured_with_single_escape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua53,
                target_stage: DecompileStage::Generate,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Generate],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.3 generate stage should succeed for goto-break-like fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert_eq!(
            generated.source.matches("while ").count(),
            2,
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
        assert!(generated.source.contains("> 2"), "{}", generated.source);
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(
            !contains_plain_self_assign(&generated.source),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua53_goto_break_like_case_preserves_runtime_output() {
        let spec = crate::support::find_unit_case_spec(
            crate::support::UnitSuite::DecompilePipelineHealth,
            "lua5.3",
            "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        )
        .expect("lua5.3 goto-break-like fixture should be in pipeline health suite");

        if let Err(failure) = crate::support::run_unit_case(spec) {
            panic!(
                "{}",
                crate::support::format_case_failure(spec.entry.path, &failure)
            );
        }
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
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
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
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
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
    fn lua53_hir_stage_keeps_branch_merge_inside_numeric_for_on_loop_state() {
        let chunk = crate::support::compile_lua_case(
            "lua5.3",
            "tests/lua_cases/lua5.3/02_bitwise_closure_mesh.lua",
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
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.3 bitwise_closure_mesh hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("assign u3[((# u3) + 1)] = (l1 ~ l0)"),
            "{dump}"
        );
        assert!(!dump.contains("local [\"l5\"] = -"), "{dump}");
        assert!(!dump.contains("local [\"l6\"] = -"), "{dump}");
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
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
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
        assert!(dump.contains("for l0 = 1, (# p0) do"), "{dump}");
        assert!(dump.contains("> 0.4"), "{dump}");
        assert!(!dump.contains("assign "), "{dump}");
        assert!(!dump.contains("numeric-for "), "{dump}");
        assert!(!dump.contains("for l0 = l3, l4, l5 do"), "{dump}");
        assert!(!dump.contains("0.4 <"), "{dump}");
    }

    #[test]
    fn lua53_hir_stage_recovers_while_state_flow_for_loop_bitwise_dispatch_fixture() {
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
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                    dump_passes: Vec::new(),
                },
                naming: NamingOptions::default(),
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.3 loop_bitwise_dispatch hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("while (l4 <= (# l3))"), "{dump}");
        assert!(dump.contains("assign l1 = l8"), "{dump}");
        assert!(!dump.contains("goto L"), "{dump}");
    }

    #[test]
    fn lua53_loop_bitwise_dispatch_fixture_preserves_runtime_output() {
        let spec = crate::support::find_unit_case_spec(
            crate::support::UnitSuite::DecompilePipelineHealth,
            "lua5.3",
            "tests/lua_cases/lua5.3/06_loop_bitwise_dispatch.lua",
        )
        .expect("lua5.3 loop_bitwise_dispatch fixture should be in pipeline health suite");

        if let Err(failure) = crate::support::run_unit_case(spec) {
            panic!(
                "{}",
                crate::support::format_case_failure(spec.entry.path, &failure)
            );
        }
    }
}

fn contains_plain_self_assign(source: &str) -> bool {
    source.lines().any(|line| {
        let line = line.trim();
        let Some((lhs, rhs)) = line.split_once('=') else {
            return false;
        };
        let lhs = lhs.trim();
        let rhs = rhs.trim();
        !lhs.is_empty()
            && lhs == rhs
            && lhs
                .chars()
                .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    })
}
