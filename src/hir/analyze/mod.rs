//! 这个文件承载 HIR 初始恢复的主入口。
//!
//! 外层文件只负责声明 analyze 子模块、组织跨 proto 的递归入口，并把目录内真正的
//! lowering 能力串起来。这样 `src/hir/analyze` 和 `src/hir/simplify` 的外层形状就会
//! 保持一致，后续继续拆分实现时也更容易定位“入口”与“细节”。

mod bindings;
mod exprs;
mod helpers;
mod lower;
mod short_circuit;
mod structure;

use self::lower::{LowerArtifacts, lower_proto};
use super::simplify::{PassDumpConfig, simplify_hir};
use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::hir::common::HirModule;

use self::exprs::lower_branch_cond;
use self::helpers::{assign_stmt, branch_stmt, build_label_map_for_summary, goto_block};
use self::lower::{
    ProtoBindings, ProtoLowering, is_control_terminator, lower_control_instr,
    lower_phi_materialization_with_allowed_blocks_except, lower_regular_instr,
};

/// HIR 阶段入口：消费结构事实与前序控制/数据流事实，写回 HIR 模块。
pub(crate) fn analyze_hir(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let mut artifacts = LowerArtifacts::default();
    let entry = context
        .timings
        .record("lower", || lower_proto(state, context, &mut artifacts));

    let mut module = HirModule {
        entry,
        protos: artifacts.protos,
    };

    let dump_config = PassDumpConfig {
        pass_names: context.options.debug.dump_passes.clone(),
        filters: context.options.debug.filters,
    };

    context.timings.record("simplify", || {
        simplify_hir(
            &mut module,
            context.options.readability,
            context.timings,
            &artifacts.promotion_facts,
            context.options.generate.mode,
            context.options.dialect,
            &dump_config,
        );
    });
    state.hir = Some(module);
    Ok(())
}
