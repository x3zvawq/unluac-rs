//! 这个文件承载主反编译 pipeline 的阶段调度表。
//!
//! `pipeline.rs` 只负责创建一次调用的状态与上下文；这里维护固定阶段顺序，统一处理
//! 阶段 timing、完成标记、target-stage 停止点和 debug dump 分派。阶段表直接用模块路径绑定
//! `DecompileStage` 与对应层主体入口，调度循环只按表调用，不再手写阶段 match。
//!
//! 这种拆分保留了“固定阶段枚举 + 强类型槽位”的可排错性，同时让 Structure / AST
//! 自己调度内部子步骤。Generate 相关 warning 也在 Generate 阶段内基于最终 AST
//! 产物计算，不再由 AST 内部步骤提前返回计划对象。

use super::error::DecompileError;
use super::options::DebugOptions;
use super::state::{DecompileContext, DecompileStage, DecompileState, StageDebugOutput};

struct StageDescriptor {
    stage: DecompileStage,
    run: for<'a> fn(&mut DecompileState, &DecompileContext<'a>) -> Result<(), DecompileError>,
    dump: fn(&DecompileState, &DebugOptions) -> Result<StageDebugOutput, DecompileError>,
}

const PIPELINE_STAGES: &[StageDescriptor] = &[
    StageDescriptor {
        stage: DecompileStage::Parser,
        run: crate::parser::parse_input,
        dump: crate::parser::dump_parser,
    },
    StageDescriptor {
        stage: DecompileStage::Transformer,
        run: crate::transformer::lower_chunk,
        dump: crate::transformer::dump_lir,
    },
    StageDescriptor {
        stage: DecompileStage::Structure,
        run: crate::structure::analyze_structure_stage,
        dump: crate::structure::dump_structure,
    },
    StageDescriptor {
        stage: DecompileStage::Hir,
        run: crate::hir::analyze_hir,
        dump: crate::hir::dump_hir,
    },
    StageDescriptor {
        stage: DecompileStage::Ast,
        run: crate::ast::analyze_ast_stage,
        dump: crate::ast::dump_ast,
    },
    StageDescriptor {
        stage: DecompileStage::Generate,
        run: crate::generate::generate_chunk,
        dump: crate::generate::dump_generate,
    },
];

pub(super) fn run_decompile_stages(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
    debug_output: &mut Vec<StageDebugOutput>,
) -> Result<(), DecompileError> {
    for descriptor in PIPELINE_STAGES {
        {
            let _timing = context
                .timings
                .scope(<&'static str>::from(descriptor.stage));
            (descriptor.run)(state, context)?;
            state.mark_completed(descriptor.stage);
        }

        if context.options.debug.enable
            && context
                .options
                .debug
                .output_stages
                .contains(&descriptor.stage)
        {
            debug_output.push((descriptor.dump)(state, &context.options.debug)?);
        }

        if descriptor.stage == context.options.target_stage {
            break;
        }
    }

    Ok(())
}
