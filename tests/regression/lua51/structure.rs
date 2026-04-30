//! 这些测试固定 Lua 5.1 下 StructureFacts 到 HIR 的结构恢复回归。

use unluac::decompile::{DecompileOptions, DecompileStage, decompile};
use unluac::naming::{NamingMode, NamingOptions};

#[test]
fn guarded_return_chain_generate_keeps_structured_if_without_goto() {
    let result = decompile(
        &crate::support::compile_lua_case(
            "lua5.1",
            "tests/lua_cases/regress_03_guarded_return_chain.lua",
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
    .expect("guarded_return_chain generate stage should succeed");

    let generated = result
        .state
        .generated
        .as_ref()
        .expect("generate stage should provide source");
    assert!(
        generated.source.contains("if r1_0 then")
            && generated.source.contains("return r1_0, r1_1, r1_2"),
        "{}",
        generated.source
    );
    assert!(
        !generated.source.contains("goto"),
        "should recover structured Lua 5.1 control flow:\n{}",
        generated.source
    );
    assert!(
        !generated.source.contains("else\n\n"),
        "readability should remove empty else arms:\n{}",
        generated.source
    );
}

#[test]
fn short_circuit_header_call_generate_keeps_single_type_call() {
    let result = decompile(
        &crate::support::compile_lua_case(
            "lua5.1",
            "tests/lua_cases/regress_04_short_circuit_header_call.lua",
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
    .expect("short_circuit_header_call generate stage should succeed");

    let generated = result
        .state
        .generated
        .as_ref()
        .expect("generate stage should provide source");
    let type_call_count = generated.source.matches("type(").count();
    assert_eq!(
        type_call_count, 1,
        "header call should not be duplicated in short-circuit condition:\n{}",
        generated.source
    );
    assert!(
        generated.source.contains("_G.type("),
        "explicit _G.type access should be preserved:\n{}",
        generated.source
    );
}
