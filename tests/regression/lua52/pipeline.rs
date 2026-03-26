//! 这些测试固定 Lua 5.2 主 pipeline 的 AST smoke 契约。

use unluac::decompile::{
    DebugDetail, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage, decompile,
};

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
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("lua5.2 ast stage should succeed for continue-like fixture");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Ast));
        let dump = &result.debug_output[0].content;
        assert!(dump.contains("===== Dump AST ====="), "{dump}");
        assert!(dump.contains("goto L"), "{dump}");
        assert!(dump.contains("::L"), "{dump}");
        assert!(!dump.contains("\ncontinue\n"), "{dump}");
    }
}
