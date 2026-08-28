//! 这个文件提供 proto 级恢复使用的最小中间产物 dump。
//!
//! 正常 `--dump structure` 仍由 debug 模块负责完整、可过滤的展示；这里的输出会进入
//! `DiagnosticPseudocode` 注释，因此必须在关闭 `decompile-debug` 的 WASM 构建中也可用。
//! 它只序列化已经完成的 Dataflow 或 Structure 事实，不参与候选选择和错误恢复决策。

use std::fmt::Write as _;

use crate::debug::format_display_set;
use crate::transformer::{LoweredProto, format_low_instr};

use super::{Cfg, DataflowFacts, ReadyStructureFacts};

pub(crate) fn dump_dataflow_proto(
    proto_id: usize,
    proto: &LoweredProto,
    cfg: &Cfg,
    facts: &DataflowFacts,
) -> String {
    let mut output = String::new();
    let _ = writeln!(
        output,
        "dataflow proto#{proto_id} blocks={} defs={} open-defs={} phis={}",
        cfg.block_order.len(),
        facts.defs.len(),
        facts.open_defs.len(),
        facts.phi_candidates.len(),
    );
    for (index, instr) in proto.instrs.iter().enumerate() {
        let block = cfg.instr_to_block.get(index).copied();
        let uses = facts
            .instr_effects
            .get(index)
            .map(|effect| format_display_set(&effect.fixed_uses))
            .unwrap_or_else(|| "[-]".to_owned());
        let defs = facts
            .instr_effects
            .get(index)
            .map(|effect| format_display_set(&effect.fixed_must_defs))
            .unwrap_or_else(|| "[-]".to_owned());
        let _ = writeln!(
            output,
            "  @{index:03} block={} {} reads={uses} writes={defs}",
            block.map_or_else(|| "-".to_owned(), |block| block.to_string()),
            format_low_instr(instr),
        );
    }
    for candidate in &facts.phi_candidates {
        let _ = writeln!(
            output,
            "  phi block={} reg={} incoming={:?}",
            candidate.block, candidate.reg, candidate.incoming,
        );
    }
    output
}

pub(crate) fn dump_structure_proto(proto_id: usize, facts: &ReadyStructureFacts) -> String {
    let plan = facts.plan();
    let mut output = String::new();
    let _ = writeln!(
        output,
        "structure proto#{proto_id} root=r{} regions={} branches={} loops={} conditions={} phis={} labels={} requirements={}",
        plan.root().index(),
        plan.regions().len(),
        plan.branches().len(),
        plan.loops().len(),
        plan.conditions().len(),
        plan.phis().len(),
        plan.labels().len(),
        plan.requirements().iter().count(),
    );
    for (region, payload) in plan.regions() {
        let _ = writeln!(output, "  region r{} {payload:?}", region.index());
    }
    for (branch, payload) in plan.branches() {
        let _ = writeln!(output, "  branch b{} {payload:?}", branch.index());
    }
    for (loop_id, payload) in plan.loops() {
        let _ = writeln!(output, "  loop l{} {payload:?}", loop_id.index());
    }
    for phi in plan.phis() {
        let _ = writeln!(output, "  phi {phi:?}");
    }
    for (requirement, payload) in plan.requirements().iter() {
        let _ = writeln!(output, "  requirement q{} {payload:?}", requirement.index());
    }
    output
}
