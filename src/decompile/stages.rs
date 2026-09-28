//! 主反编译流水线的阶段调度表。
//!
//! 消费单次调用的状态与选项，统一阶段顺序、完成标记、停止点、计时和 dump 分派；
//! 各层自行组织内部步骤并发布产物。

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
