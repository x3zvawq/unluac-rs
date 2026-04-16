//! 这些测试固定 Lua 5.2 `goto` 相关 case 的 HIR 形状。
//!
//! 它们不要求 HIR 一定恢复成最高层结构；但至少要保证：
//! 1. `break-like` / irreducible case 不再退回 fallback
//! 2. `continue-like` case 仍然能恢复成语义级 `continue`
//! 3. 必须保留 `goto` 的 case 真的在 HIR 里可见

use unluac::decompile::{
    DebugColorMode, DebugDetail, DebugOptions, DecompileOptions, DecompileStage, decompile,
};

mod decompile_pipeline {
    use super::*;

    #[test]
    fn goto_break_like_case_keeps_explicit_goto_without_hir_residuals() {
        let dump = hir_dump_for("tests/lua_cases/lua5.2/04_goto_break_like.lua");

        assert!(dump.contains("goto L"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
    }

    #[test]
    fn goto_continue_like_case_recovers_semantic_continue() {
        let dump = hir_dump_for("tests/lua_cases/lua5.2/05_goto_continue_like.lua");

        assert!(dump.contains("continue"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
    }

    #[test]
    fn irreducible_goto_case_stays_in_explicit_goto_form_without_fallback() {
        let dump = hir_dump_for("tests/lua_cases/lua5.2/06_goto_irreducible_mesh.lua");

        assert!(dump.contains("goto L"), "{dump}");
        assert!(!dump.contains("unresolved("), "{dump}");
        assert!(!dump.contains("unstructured summary=fallback"), "{dump}");
    }
}

fn hir_dump_for(source_relative: &str) -> String {
    let chunk = crate::support::compile_lua_case("lua5.2", source_relative);
    let result = decompile(
        &chunk,
        DecompileOptions {
            dialect: unluac::decompile::DecompileDialect::Lua52,
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
            ..DecompileOptions::default()
        },
    )
    .expect("lua5.2 case should reach hir");

    result.debug_output[0].content.clone()
}
