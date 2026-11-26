//! Analysis 阶段调试输出：展示 CFG、支配/循环摘要、Pruned SSA 与数据流事实。

use std::fmt::Write;

use crate::debug::{DebugDetail, build_proto_nodes, compute_focus_plan};
use crate::decompile::{DebugOptions, DecompileError, DecompileStage, DecompileState, StageDebugOutput};

use super::AnalysisChunk;

pub fn dump_analysis(
    state: &DecompileState,
    options: &DebugOptions,
) -> Result<StageDebugOutput, DecompileError> {
    let analysis = state.require_analysis()?;
    let lowered = state.require_lowered()?;
    let content = render_analysis(analysis, lowered, options);
    Ok(StageDebugOutput {
        stage: DecompileStage::Analysis,
        detail: options.detail,
        content,
    })
}

fn render_analysis(
    analysis: &AnalysisChunk,
    lowered: &crate::transformer::LoweredChunk,
    options: &DebugOptions,
) -> String {
    let mut out = String::new();
    let parents: Vec<Option<usize>> = analysis.protos.iter().map(|p| p.parent).collect();
    let focus = compute_focus_plan(
        &build_proto_nodes(&parents),
        &options.filters.as_focus_request(),
    );

    // 按 DFS 前序收集 LoweredProto 引用（与 analysis.protos 一一对应）
    let mut lowered_protos = Vec::with_capacity(analysis.protos.len());
    let mut stack = vec![&lowered.main];
    while let Some(proto) = stack.pop() {
        lowered_protos.push(proto);
        for child in proto.children.iter().rev() {
            stack.push(child.as_ref());
        }
    }

    for (idx, proto) in analysis.protos.iter().enumerate() {
        let visible = focus.is_visible(idx);
        let elided = focus.is_elided(idx);
        if !visible && !elided {
            continue;
        }
        let _ = writeln!(
            out,
            "=== Analysis proto#{} (blocks={}, loops={}, sccs={}, phis={}, defs={}) ===",
            idx,
            proto.cfg.block_order.len(),
            proto.graph.natural_loops.len(),
            proto.graph.sccs.len(),
            proto.ssa.phis.len(),
            proto.ssa.defs.len()
        );
        if elided {
            let _ = writeln!(out, "  <elided>");
            continue;
        }
        if options.detail == DebugDetail::Summary {
            continue;
        }
        let lproto = lowered_protos.get(idx).copied();
        for &b in &proto.cfg.block_order {
            let info = &proto.cfg.blocks[b.index()];
            let succs: Vec<String> = proto.cfg.succs[b.index()]
                .iter()
                .map(|&eid| {
                    let e = proto.cfg.edges[eid.index()];
                    format!("{}({})", e.to, e.kind.as_str())
                })
                .collect();
            let _ = writeln!(
                out,
                "  {} [{}] -> [{}]",
                b,
                info.kind.as_str(),
                succs.join(", ")
            );
            for &phi_id in &proto.ssa.block_phis[b.index()] {
                let phi = &proto.ssa.phis[phi_id.index()];
                let incs: Vec<String> = phi
                    .incomings
                    .iter()
                    .map(|(e, v)| format!("{}:v{}", proto.cfg.edges[e.index()].from, v.index()))
                    .collect();
                let _ = writeln!(
                    out,
                    "    v{} = phi(r{}#{}) [{}]",
                    phi.value.index(),
                    phi.slot.reg.index(),
                    phi.slot.epoch,
                    incs.join(", ")
                );
            }
            if options.detail == DebugDetail::Verbose
                && let Some(lp) = lproto
            {
                for iref in info.instrs.iter() {
                    if let Some(instr) = lp.instrs.get(iref.index()) {
                        let _ = writeln!(
                            out,
                            "    @{} {}",
                            iref.index(),
                            crate::transformer::format_low_instr(instr)
                        );
                    }
                }
            }
        }
    }
    out
}
