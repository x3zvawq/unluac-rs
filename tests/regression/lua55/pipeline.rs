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
}
