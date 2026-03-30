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
}
