//! 这些测试固定 Lua 5.1 主 pipeline 的对外契约。
//!
//! 它们不关心某一层内部怎么实现，而是验证主入口停阶段、dump 输出和错误语义
//! 是否稳定，因此归类为 regression。

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileOptions, DecompileStage,
    ReadabilityOptions, TimingNode, TimingReport, decompile,
};
use unluac::naming::{NamingMode, NamingOptions};

const SETFENV_CHUNK_HEX: &str = "
1b4c7561510001040804080023000000000000004074657374732f6361736573
2f6c7561352e312f30315f73657466656e762e6c756100000000000000000000
0002050d000000240000004a4000004940408085800000c0000000000180009c
40800185c00000c1800000000100001c0180009c4000001e0080000400000004
060000000000000076616c75650004090000000000000066726f6d2d656e7600
04080000000000000073657466656e76000406000000000000007072696e7400
0100000000000000000000000100000003000000000000020300000005000000
1e0000011e0080000100000004060000000000000076616c7565000000000003
00000002000000020000000300000000000000000000000d0000000300000005
00000006000000090000000900000009000000090000000a0000000a0000000a
0000000a0000000a0000000a000000020000000b00000000000000726561645f
76616c756500010000000c0000000400000000000000656e7600030000000c00
00000000000000
";

mod decompile_pipeline {
    use super::*;

    #[test]
    fn returns_parse_state_and_parser_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Parse],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("parse stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Parse));
        assert!(result.state.raw_chunk.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Parser ====="));
        assert!(dump.contains("header"));
        assert!(dump.contains("proto tree"));
        assert!(dump.contains("constants"));
        assert!(dump.contains("raw instructions"));
        assert!(dump.contains("opcode=GETGLOBAL"));
    }

    #[test]
    fn summary_dump_keeps_only_high_value_sections() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Parse],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("summary parse dump should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("header"));
        assert!(dump.contains("proto tree"));
        assert!(!dump.contains("\nconstants\n"));
        assert!(!dump.contains("\nraw instructions\n"));
    }

    #[test]
    fn always_color_mode_emits_ansi_sequences_in_dump_output() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Parse],
                    timing: false,
                    color: DebugColorMode::Always,
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("colored parse dump should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("\u{1b}["), "dump should include ANSI escapes");
        assert!(dump.contains("===== Dump Parser ====="));
    }

    #[test]
    fn ignores_unreached_dump_stage_when_target_stage_stops_earlier() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Parse,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Parse, DecompileStage::Transform],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("unreached dump stage should not force pipeline to continue");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Parse));
        assert_eq!(result.debug_output.len(), 1);
        assert_eq!(result.debug_output[0].stage, DecompileStage::Parse);
    }

    #[test]
    fn returns_transform_state_and_transform_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
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
        .expect("transform stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::Transform)
        );
        assert!(result.state.raw_chunk.is_some());
        assert!(result.state.lowered.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump LIR ====="));
        assert!(dump.contains("low-ir listing"));
        assert!(dump.contains("get-table"));
        assert!(dump.contains("closure"));
    }

    #[test]
    fn returns_cfg_state_and_cfg_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Cfg,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Cfg],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("cfg stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Cfg));
        assert!(result.state.cfg.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump CFG ====="));
        assert!(dump.contains("block listing"));
        assert!(dump.contains("edge listing"));
    }

    #[test]
    fn returns_graph_facts_state_and_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::GraphFacts,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::GraphFacts],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("graph facts stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::GraphFacts)
        );
        assert!(result.state.graph_facts.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump GraphFacts ====="));
        assert!(dump.contains("dominator tree"));
        assert!(dump.contains("post-dominator tree"));
        assert!(dump.contains("natural loops"));
    }

    #[test]
    fn returns_dataflow_state_and_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Dataflow,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Dataflow],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("dataflow stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Dataflow));
        assert!(result.state.dataflow.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Dataflow ====="));
        assert!(dump.contains("instr effects"));
        assert!(dump.contains("liveness"));
        assert!(dump.contains("phi candidates"));
    }

    #[test]
    fn returns_structure_state_and_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::StructureFacts,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::StructureFacts],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("structure stage should succeed");

        assert_eq!(
            result.state.completed_stage,
            Some(DecompileStage::StructureFacts)
        );
        assert!(result.state.structure_facts.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Structure ====="));
        assert!(dump.contains("branch candidates"));
        assert!(dump.contains("branch value merges"));
        assert!(dump.contains("loop candidates"));
        assert!(dump.contains("short-circuit candidates"));
        assert!(dump.contains("region facts"));
        assert!(dump.contains("scope candidates"));
    }

    #[test]
    fn returns_hir_state_and_dump() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
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
        .expect("hir stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Hir));
        assert!(result.state.hir.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump HIR ====="));
        assert!(dump.contains("proto#0"));
        assert!(dump.contains("temp"));
    }

    #[test]
    fn reaches_naming_stage_and_reports_binding_name_sources() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Naming,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Naming],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("naming stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Naming));
        assert!(result.state.naming.is_some());
        assert_eq!(result.debug_output.len(), 1);

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump Naming ====="), "{dump}");
        assert!(dump.contains("proto#0"), "{dump}");
        assert!(dump.contains("params"), "{dump}");
        assert!(dump.contains("source="), "{dump}");
    }

    #[test]
    fn boolean_hell_hir_prefers_guarded_or_shape_for_initial_short_circuit_value() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/01_boolean_hell.lua",
            ),
            DecompileOptions {
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
        .expect("boolean_hell hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("decision("), "{dump}");
        assert!(
            !dump.contains("local [\"l0\"] = ((p0 or (p3 and (p1 and p2))) and"),
            "{dump}"
        );
        assert!(
            dump.contains("local [\"l0\"] = ((p0 and")
                || dump.contains("local [\"l0\"] = (((p0 and"),
            "{dump}"
        );
    }

    #[test]
    fn ultimate_mess_hir_folds_single_access_segments_without_collapsing_the_whole_chain() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                readability: ReadabilityOptions {
                    return_inline_max_complexity: usize::MAX,
                    index_inline_max_complexity: usize::MAX,
                    args_inline_max_complexity: usize::MAX,
                    access_base_inline_max_complexity: usize::MAX,
                },
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
        .expect("ultimate_mess hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("local [\"l1\"] = p0[\"branches\"]["),
            "{dump}"
        );
        assert!(dump.contains("local [\"l2\"] = l1[\"items\"]["), "{dump}");
        assert!(dump.contains("return "), "{dump}");
        assert!(dump.contains("l2[\"value\"]"), "{dump}");
    }

    #[test]
    fn ultimate_mess_debug_chunk_still_keeps_two_access_chain_locals() {
        let result = decompile(
            &crate::support::compile_lua_case_with_debug(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                readability: ReadabilityOptions {
                    return_inline_max_complexity: usize::MAX,
                    index_inline_max_complexity: usize::MAX,
                    args_inline_max_complexity: usize::MAX,
                    access_base_inline_max_complexity: usize::MAX,
                },
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
        .expect("ultimate_mess hir stage with debug chunk should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains("local [\"l1\"] = p0[\"branches\"]["),
            "{dump}"
        );
        assert!(dump.contains("local [\"l2\"] = l1[\"items\"]["), "{dump}");
        assert!(dump.contains("return "), "{dump}");
        assert!(dump.contains("l2[\"value\"]"), "{dump}");
    }

    #[test]
    fn ultimate_mess_readability_recovers_guarded_short_circuit_shape() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("ultimate_mess readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(
            dump.contains(
                "local l0 = ((((p1 and p2) or p3) and (p2 or (p3 and p1))) or ((not p1) and (not p2)))"
            ),
            "{dump}"
        );
        assert!(
            dump.contains("local l1 = p0.branches[((p1 and \"t\") or \"f\")]"),
            "{dump}"
        );
        assert!(
            dump.contains("local l2 = l1.items[((p2 and 1) or 2)]"),
            "{dump}"
        );
        assert!(
            dump.contains("return ((l0 and \"T\") or \"F\"), l2.value"),
            "{dump}"
        );
    }

    #[test]
    fn short_circuit_side_effects_readability_sinks_hoisted_multi_return_locals() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Readability],
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Verbose,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects readability stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(!dump.contains("local l1, l2, l3, l4"), "{dump}");
        assert!(dump.contains("local l1, l2 = l0(false, true)"), "{dump}");
        assert!(dump.contains("local l3, l4 = l0(true, 0)"), "{dump}");
    }

    #[test]
    fn short_circuit_side_effects_generate_uses_register_like_names_in_debug_like_mode() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                naming: NamingOptions {
                    mode: NamingMode::DebugLike,
                    debug_like_include_function: true,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert!(generated.source.contains("local function r0_0("), "{}", generated.source);
        assert!(generated.source.contains("local function r1_1("), "{}", generated.source);
        assert!(generated.source.contains("local r0_1, r0_2 = r0_0(false, true)"), "{}", generated.source);
        assert!(!generated.source.contains("local function fn("), "{}", generated.source);
    }

    #[test]
    fn short_circuit_side_effects_generate_numbers_function_shape_names_in_simple_mode() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("short_circuit_side_effects generate stage should succeed");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should provide source");
        assert_eq!(
            generated.source.matches("local function fn(").count(),
            1,
            "{}",
            generated.source
        );
        assert!(generated.source.contains("local function fn2("), "{}", generated.source);
    }

    #[test]
    fn short_circuit_side_effects_hir_collapses_index_temps_before_locals() {
        let result = decompile(
            &compile_lua_case(
                "lua5.1",
                "tests/lua_cases/common/tricky/15_short_circuit_side_effects.lua",
            ),
            DecompileOptions {
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
        .expect("short_circuit_side_effects hir stage should succeed");

        let dump = &result.debug_output[0].content;
        assert!(dump.contains("assign u0[((# u0) + 1)] = p0"), "{dump}");
        assert!(!dump.contains("local [\"l0\"] = u0"), "{dump}");
        assert!(!dump.contains("local [\"l1\"] = (# u0)"), "{dump}");
    }

    #[test]
    fn all_supported_lua_cases_reach_clean_hir_exit() {
        let mut failures = Vec::new();

        for case in crate::support::case_manifest::hir_exit_regression_cases() {
            let Some(dialect) = case.dialect.decompile_dialect() else {
                failures.push(format!(
                    "{} is marked for HIR exit regression but has no supported decompile dialect",
                    case.path
                ));
                continue;
            };

            let chunk = compile_lua_case(case.dialect.luac_label(), case.path);
            let result = decompile(
                &chunk,
                DecompileOptions {
                    dialect,
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
            );

            match result {
                Ok(result) => {
                    let dump = &result.debug_output[0].content;
                    let mut residuals = Vec::new();
                    if dump.contains("decision(") {
                        residuals.push("decision");
                    }
                    if dump.contains("unresolved(") {
                        residuals.push("unresolved");
                    }
                    if dump.contains("unstructured summary=fallback") {
                        residuals.push("fallback");
                    }

                    if !residuals.is_empty() {
                        failures.push(format!(
                            "{} leaked HIR residuals [{}]\n{}",
                            case.path,
                            residuals.join(", "),
                            dump
                        ));
                    }
                }
                Err(error) => {
                    failures.push(format!("{} failed to reach HIR: {error}", case.path));
                }
            }
        }

        assert!(
            failures.is_empty(),
            "supported HIR cases should exit cleanly:\n\n{}",
            failures.join("\n\n")
        );
    }

    #[test]
    fn reaches_ast_stage_for_basic_lua51_fixture() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Ast,
                ..DecompileOptions::default()
            },
        )
        .expect("ast stage should now succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
    }

    #[test]
    fn leaves_timing_disabled_by_default() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Hir,
                debug: DebugOptions {
                    enable: true,
                    output_stages: Vec::new(),
                    timing: false,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Summary,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("hir stage should succeed without timing");

        assert!(result.timing_report.is_none());
    }

    #[test]
    fn collects_pipeline_and_pass_timings_when_enabled() {
        let chunk = crate::support::compile_lua_case(
            "lua5.1",
            "tests/lua_cases/common/tricky/02_ultimate_mess.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: unluac::decompile::DecompileDialect::Lua51,
                target_stage: DecompileStage::Readability,
                debug: DebugOptions {
                    enable: true,
                    output_stages: Vec::new(),
                    timing: true,
                    color: DebugColorMode::Never,
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                readability: ReadabilityOptions {
                    return_inline_max_complexity: 999,
                    index_inline_max_complexity: 999,
                    args_inline_max_complexity: 6,
                    access_base_inline_max_complexity: 999,
                },
                ..DecompileOptions::default()
            },
        )
        .expect("readability stage should succeed with timing enabled");

        let report = result
            .timing_report
            .as_ref()
            .expect("timing should be collected when explicitly enabled");
        assert!(find_timing_node(report, &["parse"]).is_some());
        assert!(find_timing_node(report, &["hir", "lower"]).is_some());
        assert!(
            find_timing_node(
                report,
                &["hir", "simplify", "fixed-point-round", "temp-inline"]
            )
            .is_some()
        );
        assert!(find_timing_node(report, &["readability", "statement-merge"]).is_some());
        assert!(
            find_timing_node(
                report,
                &[
                    "readability",
                    "short-circuit-pretty",
                    "fixed-point-round",
                    "short-circuit-pretty"
                ],
            )
            .is_some()
        );
    }

    fn find_timing_node<'a>(report: &'a TimingReport, path: &[&str]) -> Option<&'a TimingNode> {
        find_timing_node_in_children(&report.nodes, path)
    }

    fn find_timing_node_in_children<'a>(
        nodes: &'a [TimingNode],
        path: &[&str],
    ) -> Option<&'a TimingNode> {
        let (head, tail) = path.split_first()?;
        let node = nodes.iter().find(|node| node.label == *head)?;
        if tail.is_empty() {
            Some(node)
        } else {
            find_timing_node_in_children(&node.children, tail)
        }
    }
}

fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    crate::support::compile_lua_case(dialect_label, source_relative)
}
