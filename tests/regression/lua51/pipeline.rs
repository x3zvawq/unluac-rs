//! 这些测试固定 Lua 5.1 主 pipeline 的对外契约。
//!
//! 它们不关心某一层内部怎么实现，而是验证主入口停阶段、dump 输出和错误语义
//! 是否稳定，因此归类为 regression。

use unluac::decompile::{
    DebugDetail, DebugOptions, DecompileError, DecompileOptions, DecompileStage, decompile,
};

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
    fn ignores_unreached_dump_stage_when_target_stage_stops_earlier() {
        let result = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Parse,
                debug: DebugOptions {
                    enable: true,
                    output_stages: vec![DecompileStage::Parse, DecompileStage::Transform],
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
                    detail: DebugDetail::Normal,
                    filters: Default::default(),
                },
                ..DecompileOptions::default()
            },
        )
        .expect("transform stage should succeed");

        assert_eq!(result.state.completed_stage, Some(DecompileStage::Transform));
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
    fn reports_cfg_stage_as_not_implemented_after_transform() {
        let error = decompile(
            &crate::support::decode_hex(SETFENV_CHUNK_HEX),
            DecompileOptions {
                target_stage: DecompileStage::Cfg,
                ..DecompileOptions::default()
            },
        )
        .expect_err("cfg stage should not be implemented yet");

        assert!(matches!(
            error,
            DecompileError::StageNotImplemented {
                stage: DecompileStage::Cfg,
                completed_stage: DecompileStage::Transform,
            }
        ));
    }
}
