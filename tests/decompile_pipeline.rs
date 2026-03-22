//! 这些集成测试固定主 pipeline 当前的最小可用契约。
//!
//! 现在只有 parser 真正接上，但入口、停阶段行为和 parser dump 形状
//! 都需要先锁定，避免后续接更多层时把当前调试工作流回归掉。

use unluac::decompile::{
    DebugDetail, DebugFormat, DebugOptions, DecompileError, DecompileOptions, DecompileStage,
    decompile,
};

// 这里继续保留固定 chunk fixture，而不是动态调用 luac，
// 是为了让这份测试专注锁定“库契约是否回归”，避免被本地工具链或构建状态干扰。
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
            &decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                debug: DebugOptions {
                    enable: true,
                    output_stage: Some(DecompileStage::Parse),
                    format: DebugFormat::Human,
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
            &decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                debug: DebugOptions {
                    enable: true,
                    output_stage: Some(DecompileStage::Parse),
                    format: DebugFormat::Human,
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
    fn reports_next_stage_as_not_implemented() {
        let error = decompile(
            &decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Transform,
                ..DecompileOptions::default()
            },
        )
        .expect_err("transform stage should not be implemented yet");

        assert!(matches!(
            error,
            DecompileError::StageNotImplemented {
                stage: DecompileStage::Transform,
                completed_stage: DecompileStage::Parse,
            }
        ));
    }
}

fn decode_hex(hex: &str) -> Vec<u8> {
    let compact = hex
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    assert_eq!(compact.len() % 2, 0, "fixture hex should have even length");

    compact
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair).expect("fixture hex should stay ascii");
            u8::from_str_radix(digits, 16).expect("fixture hex should decode")
        })
        .collect()
}
