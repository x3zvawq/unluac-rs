//! 这些测试固定 Lua 5.2 已经修好的 AST 回归点。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
    decompile,
};
use unluac::naming::NamingOptions;

mod decompile_pipeline {
    use super::*;

    #[test]
    fn lua52_ast_stage_rewrites_continue_like_hir_into_goto_label_form() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/lua5.2/05_goto_continue_like.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 ast stage should succeed for continue-like fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump AST ====="), "{dump}");
        assert!(!dump.contains("goto "), "{dump}");
        assert!(dump.contains("if (l0 % 2) ~= 0 then"), "{dump}");
        assert!(!dump.contains("\ncontinue\n"), "{dump}");
    }

    #[test]
    fn lua52_generate_stage_keeps_cross_loop_goto_break_like_case_structured_with_single_escape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 generate stage should succeed for goto-break-like fixture");

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
    fn lua52_generate_stage_coalesces_irreducible_goto_mesh_back_into_single_state_local_decl() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/lua5.2/06_goto_irreducible_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 generate stage should succeed for irreducible goto mesh fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert_eq!(
            generated.source.matches("local ").count(),
            1,
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local r0_0, r0_1,"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("\nlocal r0_"),
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
    fn lua52_goto_break_like_case_preserves_runtime_output() {
        let spec = crate::support::find_unit_case_spec(
            crate::support::UnitSuite::DecompilePipelineHealth,
            "lua5.2",
            "tests/lua_cases/lua5.2/04_goto_break_like.lua",
        )
        .expect("lua5.2 goto-break-like fixture should be in pipeline health suite");

        if let Err(failure) = crate::support::run_unit_case(spec) {
            panic!(
                "{}",
                crate::support::format_case_failure(spec.entry.path, &failure)
            );
        }
    }

    #[test]
    fn lua52_hir_stage_recovers_globals_from_env_upvalue_chain_for_nested_closure_factory() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/tricky/16_nested_closure_factory.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 hir stage should recover globals for nested closure factory");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("global(print)"), "{dump}");
        assert!(dump.contains("local [\"l0\"] = p0"), "{dump}");
        assert!(dump.contains("local [\"l0\"] = (u0 + p0)"), "{dump}");
        assert!(
            dump.contains("return closure(proto#2 captures=l0)"),
            "{dump}"
        );
        assert!(
            dump.contains("return closure(proto#3 captures=u0, l0)"),
            "{dump}"
        );
        assert!(!dump.contains("u0[\"print\"]"), "{dump}");
        assert!(!dump.contains("u0.print"), "{dump}");
        assert!(!dump.contains("captures=p0"), "{dump}");
        assert!(!dump.contains("captures=u0, (u0 + p0)"), "{dump}");
    }

    #[test]
    fn lua52_generate_stage_emits_global_print_for_nested_closure_factory() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/tricky/16_nested_closure_factory.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 generate stage should recover globals for nested closure factory");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local result = fn(2)"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local result2 = result(3)"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"nested-closure\", result2(4))"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("print(\"nested-closure\", result(1)(2))"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local value = a"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("local ok = value + b"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("up.print("),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("u0.print("),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("local print = print"),
            "{}",
            generated.source
        );
        assert!(
            !generated
                .source
                .contains("print(\"nested-closure\", fn(2)(3)(4))"),
            "{}",
            generated.source
        );
        assert!(
            !generated
                .source
                .contains("print(\"nested-closure\", value(1)(2))"),
            "{}",
            generated.source
        );
        assert!(
            !generated
                .source
                .contains("return function(b)\n        return function(c)"),
            "{}",
            generated.source
        );
    }

    #[test]
    fn lua52_hir_stage_recovers_nested_loop_mesh_without_residual_numeric_for() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 hir stage should recover nested loop mesh");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("numeric-for l0 = 1, p0, 1"), "{dump}");
        assert!(dump.contains("while (l3 < 4)"), "{dump}");
        assert!(dump.contains("break"), "{dump}");
        assert!(!dump.contains("unresolved(numeric-for-init"), "{dump}");
        assert!(!dump.contains("unresolved(numeric-for-loop"), "{dump}");
    }

    #[test]
    fn lua52_generate_stage_emits_nested_loop_mesh_structure() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/control_flow/06_nested_loop_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 generate stage should recover nested loop mesh");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("for i = 1, a do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("while ok < 4 do"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("if (i + ok) % 2 == 0 then"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("if ok == i then"),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("goto "), "{}", generated.source);
    }

    #[test]
    fn lua52_hir_stage_recovers_nested_control_flow_without_residual_numeric_for() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 hir stage should recover nested control flow");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("repeat"), "{dump}");
        assert!(dump.contains("numeric-for l0 = t6, t7, t8"), "{dump}");
        assert!(
            dump.contains("return l2, (((not (0 < p0)) and \"negative\") or \"positive\")"),
            "{dump}"
        );
        assert!(!dump.contains("unresolved(numeric-for-init"), "{dump}");
        assert!(!dump.contains("unresolved(numeric-for-loop"), "{dump}");
    }

    #[test]
    fn lua52_generate_stage_emits_nested_control_flow_shape() {
        let chunk = crate::support::compile_lua_case(
            "lua5.2",
            "tests/lua_cases/common/tricky/04_nested_control_flow.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Lua52,
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
        .expect("lua5.2 generate stage should recover nested control flow");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Generate));
        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        assert!(
            generated.source.contains("local ok = 0"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("if a > 10 then"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("elseif a > 5 then"),
            "{}",
            generated.source
        );
        assert!(generated.source.contains("repeat"), "{}", generated.source);
        assert!(
            generated.source.contains("until ok > 10"),
            "{}",
            generated.source
        );
        assert!(
            generated.source.contains("for i = 1, 5 do"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("return ok, a > 0 and \"positive\" or \"negative\""),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.contains("continue"),
            "{}",
            generated.source
        );
        assert!(!generated.source.contains("goto "), "{}", generated.source);
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
