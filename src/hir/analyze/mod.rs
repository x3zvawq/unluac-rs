//! HIR 初始恢复的模块入口。
//!
//! 组织跨 proto 构造并串联表达式、绑定和结构 lowering，输出 HIR module。

mod artifact_recovery;
mod bindings;
mod capture_initializers;
mod exprs;
mod global_decls;
mod helpers;
mod instrs;
mod lower;
pub(super) mod method_setups;
mod shared_closures;
mod short_circuit;
mod structure;

use self::lower::{LowerArtifacts, lower_proto};
use super::simplify::{PassDumpConfig, simplify_hir};
use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::hir::common::HirModule;

/// HIR 阶段入口：消费结构事实与前序控制/数据流事实，写回 HIR 模块。
pub(crate) fn analyze_hir(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let mut artifacts = LowerArtifacts::default();
    let entry = context
        .timings
        .record("lower", || lower_proto(state, context, &mut artifacts))?;

    let mut module = HirModule {
        entry,
        protos: artifacts.protos,
        required_luau_inlining: artifacts.required_luau_inlining,
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
            &mut artifacts.promotion_facts,
            context.options.generate.mode,
            context.options.dialect,
            &dump_config,
        )
    })?;
    state.hir = Some(module);
    Ok(())
}
