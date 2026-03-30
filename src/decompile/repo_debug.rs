//! 这个文件集中维护仓库内调试入口共享的默认 preset。
//!
//! `examples/debug.rs` 与本仓库自带的 CLI 都需要一套偏“本地排错”的默认反编译配置。
//! 把它们收敛到这里，可以避免两个入口各自手写一份默认值，后续修改时再慢慢漂移。
//! 这里明确只负责“repo 内调试 preset”，不会把源码路径、编译器路径这类仓库文件系统
//! 细节也塞进库层。

use crate::generate::GenerateOptions;
use crate::naming::{NamingMode, NamingOptions};
use crate::parser::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};
use crate::readability::ReadabilityOptions;

use super::{
    DebugColorMode, DebugFilters, DebugOptions, DecompileDialect, DecompileOptions, DecompileStage,
};
use crate::debug::DebugDetail;

/// 仓库内调试入口共享的默认反编译选项。
pub fn repo_debug_decompile_options() -> DecompileOptions {
    DecompileOptions {
        dialect: DecompileDialect::Lua51,
        parse: ParseOptions {
            mode: ParseMode::Permissive,
            string_encoding: StringEncoding::Utf8,
            string_decode_mode: StringDecodeMode::Strict,
        },
        // 这个 preset 更偏向直接看最终源码形状，所以默认停在 Generate。
        target_stage: DecompileStage::Generate,
        debug: DebugOptions {
            enable: true,
            output_stages: vec![DecompileStage::Generate],
            timing: false,
            color: DebugColorMode::Always,
            detail: DebugDetail::Verbose,
            filters: DebugFilters::default(),
        },
        readability: ReadabilityOptions {
            return_inline_max_complexity: 10,
            index_inline_max_complexity: 10,
            args_inline_max_complexity: 6,
            access_base_inline_max_complexity: 5,
        },
        naming: NamingOptions {
            mode: NamingMode::DebugLike,
            debug_like_include_function: true,
        },
        generate: GenerateOptions::default(),
    }
}
