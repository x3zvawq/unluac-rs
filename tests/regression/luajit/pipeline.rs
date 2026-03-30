//! 这些测试固定 LuaJIT 已经修好的主 pipeline 回归点。

use unluac::decompile::{DecompileDialect, DecompileOptions, DecompileStage, decompile};

mod decompile_pipeline {
    use super::*;

    #[test]
    fn goto_cdata_accumulator_generate_stage_keeps_carried_state_on_original_bindings() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/01_goto_cdata_accumulator.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit cdata goto fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");
        let mut lines = generated.source.lines();
        let first_line = lines.next().expect("fixture should emit at least one line");
        let (lhs, rhs) = first_line
            .split_once(" = ")
            .expect("fixture should initialize the carried bindings on the first line");

        assert!(lhs.starts_with("local "), "{}", generated.source);
        assert_eq!(
            lhs["local ".len()..].split(',').count(),
            2,
            "{}",
            generated.source
        );
        assert_eq!(rhs.split(',').count(), 2, "{}", generated.source);
        assert!(rhs.contains("0LL"), "{}", generated.source);

        for line in generated
            .source
            .lines()
            .filter(|line| !line.trim().is_empty())
        {
            if let Some((assign_lhs, _)) = line.split_once(" = ") {
                let is_local_init = line.trim_start().starts_with("local ");
                if !is_local_init {
                    assert!(!assign_lhs.contains(','), "{}", generated.source);
                }
            }
        }

        assert!(generated.source.contains("goto L1"), "{}", generated.source);
    }

    #[test]
    fn imaginary_wave_fold_generate_stage_recovers_truthy_ternary_method_call() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/02_imaginary_wave_fold.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit imaginary wave fold fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");

        assert!(
            generated
                .source
                .contains(":find(\"%-\") and \"neg\" or \"pos\""),
            "{}",
            generated.source
        );
    }

    #[test]
    fn ffi_struct_goto_mesh_generate_stage_recovers_multiline_cdef_and_loop_body() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/03_ffi_struct_goto_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit ffi struct goto mesh fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");

        assert!(generated.source.contains("cdef([["));
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("[i].id = i + 1")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("[i].weight = (i + 1) * 1.25")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("= ok +") && line.contains("[i].weight")),
            "{}",
            generated.source
        );
    }

    #[test]
    fn bit_cdata_pipeline_generate_stage_recovers_loop_inline_shapes() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/04_bit_cdata_pipeline.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit bit cdata pipeline fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");

        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("bxor(tonumber(") && line.contains("tonumber(")),
            "{}",
            generated.source
        );
        assert!(
            generated.source.lines().any(|line| line.contains("[#")
                && line.contains("+ 1]")
                && line.contains("string.format")),
            "{}",
            generated.source
        );
    }

    #[test]
    fn ffi_metatype_counter_generate_stage_recovers_method_body_and_loop_call_shape() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/07_ffi_metatype_counter.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit ffi metatype counter fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");

        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains(".value =") && line.contains(".value +")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .contains("metatype(\"counter_t\", {\n    __index = {\n        bump = function"),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("= ") && line.contains(":bump(")),
            "{}",
            generated.source
        );
    }

    #[test]
    fn imaginary_branch_mesh_generate_stage_avoids_hoisted_empty_locals() {
        let chunk = crate::support::compile_lua_case(
            "luajit",
            "tests/lua_cases/luajit/08_imaginary_branch_mesh.lua",
        );
        let result = decompile(
            &chunk,
            DecompileOptions {
                dialect: DecompileDialect::Luajit,
                target_stage: DecompileStage::Generate,
                ..DecompileOptions::default()
            },
        )
        .expect("luajit imaginary branch mesh fixture should decompile successfully");

        let generated = result
            .state
            .generated
            .as_ref()
            .expect("generate stage should leave generated source in state");

        assert!(
            generated
                .source
                .lines()
                .all(|line| !line.trim_start().starts_with("local ") || line.contains(" = ")),
            "{}",
            generated.source
        );
        assert!(
            !generated.source.lines().any(|line| {
                let Some((lhs, _)) = line.split_once(" = ") else {
                    return false;
                };
                !line.trim_start().starts_with("local ") && lhs.contains(',')
            }),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("local ") && line.contains("= tostring(")),
            "{}",
            generated.source
        );
        assert!(
            generated
                .source
                .lines()
                .any(|line| line.contains("local ") && line.contains("= tonumber(")),
            "{}",
            generated.source
        );
    }
}
