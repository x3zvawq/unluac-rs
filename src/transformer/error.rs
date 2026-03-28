//! 这个文件定义 transformer 层的错误类型。
//!
//! transformer 的职责虽然是规则转译，但一旦 raw 指令模式不满足 lowering 前提，
//! 这里必须尽早报错，而不是把含糊状态继续传给 CFG/Dataflow 去猜。

use thiserror::Error;

use crate::parser::DialectVersion;

/// raw -> low-IR lowering 期间可能产生的错误。
#[derive(Debug, Error)]
pub enum TransformError {
    #[error("unsupported transform dialect `{version:?}`")]
    UnsupportedDialect { version: DialectVersion },
    #[error("unsupported opcode `{opcode}` at raw pc {raw_pc}")]
    UnsupportedOpcode { raw_pc: u32, opcode: &'static str },
    #[error("unexpected operands for opcode `{opcode}` at raw pc {raw_pc}: expected {expected}")]
    UnexpectedOperands {
        raw_pc: u32,
        opcode: &'static str,
        expected: &'static str,
    },
    #[error("opcode `{opcode}` at raw pc {raw_pc} must be followed by a helper JMP")]
    MissingHelperJump { raw_pc: u32, opcode: &'static str },
    #[error(
        "helper instruction after raw pc {raw_pc} must be JMP, found `{found}` at raw pc {helper_pc}"
    )]
    InvalidHelperJump {
        raw_pc: u32,
        helper_pc: u32,
        found: &'static str,
    },
    #[error("opcode `{opcode}` at raw pc {raw_pc} must be followed by EXTRAARG")]
    MissingExtraArg { raw_pc: u32, opcode: &'static str },
    #[error(
        "helper instruction after raw pc {raw_pc} must be EXTRAARG, found `{found}` at raw pc {helper_pc}"
    )]
    InvalidExtraArg {
        raw_pc: u32,
        helper_pc: u32,
        found: &'static str,
    },
    #[error("unexpected standalone EXTRAARG at raw pc {raw_pc}")]
    UnexpectedStandaloneExtraArg { raw_pc: u32 },
    #[error(
        "raw pc {raw_pc} references constant k{const_index}, but only {const_count} constants exist"
    )]
    InvalidConstRef {
        raw_pc: u32,
        const_index: usize,
        const_count: usize,
    },
    #[error(
        "raw pc {raw_pc} references upvalue u{upvalue_index}, but only {upvalue_count} upvalues exist"
    )]
    InvalidUpvalueRef {
        raw_pc: u32,
        upvalue_index: usize,
        upvalue_count: usize,
    },
    #[error(
        "raw pc {raw_pc} references child proto p{proto_index}, but only {child_count} children exist"
    )]
    InvalidProtoRef {
        raw_pc: u32,
        proto_index: usize,
        child_count: usize,
    },
    #[error(
        "raw pc {raw_pc} jumps to raw pc {target_raw}, but current proto only has {instr_count} raw instructions"
    )]
    InvalidJumpTarget {
        raw_pc: u32,
        target_raw: usize,
        instr_count: usize,
    },
    #[error(
        "raw pc {raw_pc} targets raw pc {target_raw}, but that raw instruction does not start a low-IR instruction"
    )]
    UntargetableRawInstruction { raw_pc: u32, target_raw: usize },
    #[error(
        "numeric for at raw pc {raw_pc} must target a matching FORLOOP, but raw pc {target_raw} is `{found}`"
    )]
    InvalidNumericForPair {
        raw_pc: u32,
        target_raw: usize,
        found: &'static str,
    },
    #[error("generic for call at raw pc {raw_pc} must be followed by TFORLOOP")]
    MissingGenericForLoop { raw_pc: u32 },
    #[error(
        "generic for helper after raw pc {raw_pc} must be TFORLOOP, found `{found}` at raw pc {helper_pc}"
    )]
    InvalidGenericForLoop {
        raw_pc: u32,
        helper_pc: u32,
        found: &'static str,
    },
    #[error(
        "generic for pair at raw pc {raw_pc} is inconsistent: TFORCALL base r{call_base}, TFORLOOP control r{loop_control}"
    )]
    InvalidGenericForPair {
        raw_pc: u32,
        call_base: usize,
        loop_control: usize,
    },
    #[error("closure at raw pc {raw_pc} is missing capture helper #{capture_index}")]
    MissingClosureCapture { raw_pc: u32, capture_index: usize },
    #[error(
        "closure at raw pc {raw_pc} expects MOVE/GETUPVAL capture helper, found `{found}` at raw pc {capture_pc}"
    )]
    InvalidClosureCapture {
        raw_pc: u32,
        capture_pc: u32,
        found: &'static str,
    },
}
