//! 这个文件实现主反编译 pipeline 的统一入口。
//!
//! 这里只负责补齐默认选项、创建一次调用的 `DecompileState` 和 stage 上下文，
//! 再把固定阶段推进交给 `stages` 模块。这样主入口保留“反编译调用生命周期”的语义，
//! 阶段读写槽位、debug dump、target-stage 停止点等编排细节集中在调度表里维护。

use crate::ast::AstTargetDialect;
use crate::timing::{TimingCollector, TimingReport};

use super::error::DecompileError;
use super::options::{DecompileDialect, DecompileOptions};
use super::stages::run_decompile_stages;
use super::state::{DecompileContext, DecompileState, StageDebugOutput};

/// 一次主 pipeline 调用的返回值。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileResult {
    pub state: DecompileState,
    pub debug_output: Vec<StageDebugOutput>,
    pub timing_report: Option<TimingReport>,
}

/// 对外暴露唯一的主入口，统一完成默认值补齐和阶段调度。
pub fn decompile(
    bytes: &[u8],
    options: DecompileOptions,
) -> Result<DecompileResult, DecompileError> {
    DecompilerPipeline.run(bytes, options)
}

struct DecompilerPipeline;

impl DecompilerPipeline {
    fn run(
        self,
        bytes: &[u8],
        options: DecompileOptions,
    ) -> Result<DecompileResult, DecompileError> {
        let mut options = options.normalized();
        if options.dialect == DecompileDialect::Auto {
            options.dialect = crate::parser::detect_dialect(bytes)?;
        }

        let mut debug_output = Vec::new();
        let timings = TimingCollector::new(options.debug.enable && options.debug.timing);
        let requested_target = AstTargetDialect::new(options.dialect);
        let context = DecompileContext {
            bytes,
            options: &options,
            timings: &timings,
            requested_target,
        };

        let mut state = DecompileState::new(options.dialect, options.target_stage);
        run_decompile_stages(&mut state, &context, &mut debug_output)?;

        Ok(DecompileResult {
            state,
            debug_output,
            timing_report: context.timings.finish(),
        })
    }
}
