//! 这个文件实现共享循环候选提取。
//!
//! 这个 pass 只消费 CFG / GraphFacts / Dataflow / low-IR terminator，产出“循环形态 hint +
//! 可直接复用的源码绑定证据 + loop merge incoming 事实”，不会越权决定最终
//! `while/repeat/for` 语法。
//!
//! 例子：
//! - `NumericForInit/Loop` 会产出 `LoopKindHint::NumericForLike`，并把源码绑定寄存器
//!   记录成 `LoopSourceBindings::Numeric`
//! - `GenericForCall/Loop` 会产出 `LoopKindHint::GenericForLike`，并把源码绑定区间
//!   记录成 `LoopSourceBindings::Generic`
//! - 无自身回边的 generic-for 以 body target 支配区域恢复完整语义 owner，零次迭代
//!   出口仍保持在 body 外侧
//! - `while ... do ... end` 的 header/exit phi 会被整理成 `inside/outside` 两臂的
//!   incoming facts，后续 HIR 直接消费这些结构事实，不再自己回头拆 `phi.incoming`
//! - 普通 `while/repeat` 只保留形态 hint，不会伪造额外 binding 证据
//! - branch 经共享 backedge pad 提前进入下一轮时，会在 branch 候选齐备后记录唯一
//!   `continue_edges` owner，HIR 不再按 jump 形状猜测归属
//! - 多条 loop-exclusive exit 可先写回 live-out 再直接汇入同一 continuation；需要跨越
//!   中间 pad 时仍只接受 `Close + Jump` 或 `Close-only + fallthrough`
//! - for binding 的提前退出域在多个物理 exit 的共同后继前结束，不会穿过
//!   cleanup pad 把循环变量身份带到 post-loop
//! - repeat body 的首个条件可能让 natural-loop 暂时呈现为 while；若该 header 的局部
//!   break pad 严格汇入独立尾条件出口，则由 Structure 恢复真正的 repeat 形态
//! - 同一 header 的全部 natural backedge 只形成一个候选；源码里的重叠循环写法若
//!   编译成同一控制身份，由这个 region 内的 branch/break/continue 表达，不在后层
//!   重新按回边拆候选
//! - 全部出口都直接终止时，多条 sibling latch 共同归一个 while-true owner，header
//!   作为它们共享的下一轮入口
//! - `WhileLike` 的 header 前缀必须属于 branch 条件的数据依赖链，或是可丢弃的
//!   无副作用残留；带副作用但不参与条件的语句应保守留给 repeat/unknown/goto 形态

use std::collections::{BTreeMap, BTreeSet};

use crate::structure::{BlockRef, Cfg, DataflowFacts, EdgeKind, EdgeRef, GraphFacts};
use crate::transformer::{GenericForLoopInstr, LowInstr, LoweredProto, Reg};

use super::common::{
    BranchCandidate, BranchKind, LoopCandidate, LoopExitAlias, LoopExitValueMergeCandidate,
    LoopKindHint, LoopSourceBindings, LoopValueMerge, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitTarget,
};
use super::helpers::{
    block_has_non_control_prefix, collect_forward_region_blocks, collect_region_exits,
    equivalent_single_return_targets, is_reducible_region, same_or_transparent_jump_target,
};
use super::phi_facts::loop_value_merges_in_block;

mod candidates;
mod continue_edges;
mod exits;
mod natural_loops;
mod repeat_refine;
mod shape;

pub(super) use candidates::generic_for_immediate_break;
use candidates::*;
pub(super) use continue_edges::assign_continue_edge_ownership;
pub(super) use exits::transparent_loop_exit_target;
use exits::*;
pub(super) use natural_loops::branch_conditions_share_subject;
use natural_loops::*;
use repeat_refine::*;
pub(super) use repeat_refine::{RepeatRefinementInput, refine_short_circuit_repeat_candidates};
use shape::*;

#[derive(Clone, Copy)]
struct LoopAnalysisContext<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    graph_facts: &'a GraphFacts,
    dataflow: &'a DataflowFacts,
}

pub(super) fn analyze_loops(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
) -> Vec<LoopCandidate> {
    let context = LoopAnalysisContext {
        proto,
        cfg,
        graph_facts,
        dataflow,
    };
    let mut shared_exit_workspace = SharedExitWorkspace::new(cfg.blocks.len());
    let mut domain_workspace = NaturalLoopDomainWorkspace::new(cfg.blocks.len());
    let mut loop_candidates = Vec::with_capacity(graph_facts.natural_loops.len());
    for natural_loop in &graph_facts.natural_loops {
        if let Some(partition) = reachable_numeric_for_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else if let Some(partition) = partition_repeat_like_natural_loop(
            &context,
            &mut shared_exit_workspace,
            &mut domain_workspace,
            natural_loop,
        ) {
            loop_candidates.extend(partition);
        } else {
            loop_candidates.push(build_loop_candidate(
                &context,
                &mut shared_exit_workspace,
                natural_loop.header,
                natural_loop.blocks.clone(),
                natural_loop.backedges.clone(),
            ));
        }
    }
    let mut grouped_headers = vec![false; cfg.blocks.len()];
    let mut numeric_headers = vec![false; cfg.blocks.len()];
    for candidate in &loop_candidates {
        grouped_headers[candidate.header.index()] = true;
        if candidate.kind_hint == LoopKindHint::NumericForLike {
            numeric_headers[candidate.header.index()] = true;
        }
    }

    let degenerate_generic_for_loops = analyze_degenerate_generic_for_loops(
        proto,
        cfg,
        dataflow,
        graph_facts,
        &grouped_headers,
        &mut shared_exit_workspace,
    );
    loop_candidates.extend(degenerate_generic_for_loops);
    let numeric_for_latches = index_numeric_for_latches(proto, cfg);
    loop_candidates.extend(
        cfg.reachable_blocks
            .iter()
            .copied()
            .filter_map(|preheader| {
                degenerate_numeric_for_loop(
                    &context,
                    &numeric_headers,
                    &numeric_for_latches,
                    &mut shared_exit_workspace,
                    preheader,
                )
            }),
    );
    loop_candidates.sort_by_key(|candidate| (candidate.header, candidate.blocks.len()));
    refine_nested_for_exit_loops(proto, cfg, graph_facts, &mut loop_candidates);
    refine_ambiguous_repeat_candidates(
        proto,
        cfg,
        graph_facts,
        &mut shared_exit_workspace,
        &mut loop_candidates,
    );
    loop_candidates
}
