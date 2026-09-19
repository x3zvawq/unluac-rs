//! 汇总 if/else 合流后的必写 temp，供 locals 建立稳定绑定。
//!
//! 消费 HirFlowGraph、当前 HIR 事件和 RootEventBlock，只计算 must-write 与
//! read-before-def，不自行解析控制边，也不分配 local 或改写语句。
//! 例如 if c then t=a else t=b end; use(t) 报告候选 t，主 pass 再在 if 前
//! 建立空 local；候选必须保证该声明能支配全部读取。

use std::collections::BTreeSet;

use super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind, LexicalCfgFailure};
use super::super::root_lifetimes::RootEventBlock;
use super::super::temp_touch::{TempReadCollector, collect_temp_refs_in_expr};
use crate::hir::common::{HirBlock, HirLValue, HirStmt, TempId};
use crate::hir::expr_safety::HirExprSafety;

#[derive(Debug, Clone, Default)]
struct FallthroughSummary {
    falls_through: bool,
    assigned_temps: BTreeSet<TempId>,
    reads_before_assignment: BTreeSet<TempId>,
}

pub(super) fn candidate_temps(
    owner_stmts: &[HirStmt],
    stmt: &HirStmt,
    event_block: RootEventBlock<'_>,
    stmt_index: usize,
    is_reserved: &dyn Fn(TempId) -> bool,
    safety: HirExprSafety,
) -> Vec<TempId> {
    let HirStmt::If(if_stmt) = stmt else {
        return Vec::new();
    };
    let Some(else_block) = &if_stmt.else_block else {
        return Vec::new();
    };

    let then_summary = summarize_block_fallthrough_assignments(&if_stmt.then_block, safety);
    let else_summary = summarize_block_fallthrough_assignments(else_block, safety);
    if matches!(then_summary, Err(RegionCfgFailure::ExternalGoto))
        || matches!(else_summary, Err(RegionCfgFailure::ExternalGoto))
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：`if c then goto L else t=1 end;
        // ::L:: use(t)` 的 arm 外 goto 可能重入当前 if 的外层后缀；这里没有目标边，
        // 若把该路径当成终止路径会凭另一 arm 的写入错误物化 branch local。
        return Vec::new();
    }
    let then_summary = then_summary.expect("HIR label ids must be unique within a branch region");
    let else_summary = else_summary.expect("HIR label ids must be unique within a branch region");
    let Some(common_temps) = intersect_fallthrough_assignment_sets([&then_summary, &else_summary])
    else {
        return Vec::new();
    };
    let condition_reads = collect_temp_refs_in_expr(&if_stmt.cond);
    let reads_before_assignment = [&then_summary, &else_summary]
        .into_iter()
        .flat_map(|summary| summary.reads_before_assignment.iter())
        .copied()
        .chain(condition_reads)
        .collect::<BTreeSet<_>>();
    let mut prefix_cfg = None;

    common_temps
        .into_iter()
        .filter(|temp| !is_reserved(*temp))
        .filter(|temp| !reads_before_assignment.contains(temp))
        .filter(|temp| {
            if !event_block.has_touch_before(*temp, stmt_index)
                || prefix_cfg
                    .get_or_insert_with(|| {
                        RegionTempFlow::for_stmts(&owner_stmts[..stmt_index], safety).ok()
                    })
                    .as_ref()
                    .is_some_and(|cfg| cfg.fallthrough_temp_is_gc_inert(*temp))
            {
                return true;
            }
            // 候选拒绝[SemanticBarrier:Lifetime]：`t=obj; if c then t=a else t=b end; GC`
            // 若在 if 前另建 local，旧 t owner 不再按 arm 写入点覆盖，弱表/`__gc`
            // 可观察旧对象延寿。只有完整 prefix CFG 的每条 fallthrough 都以 GC-inert
            // 写终结旧 root 时才解除该屏障。
            false
        })
        // 合流后没有任何后续 touch 的 branch temp 不形成跨语句
        // 源码 binding；dead-temps 会独立审计其中可删除的写，其余 effect/root 写仍保留原形。
        .filter(|temp| event_block.has_touch_from(*temp, stmt_index + 1))
        .collect()
}

pub(super) fn definite_if_arm_temp_writes(stmt: &HirStmt) -> Option<[TempId; 2]> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref()?;
    Some([
        single_scalar_temp_write(&if_stmt.then_block)?,
        single_scalar_temp_write(else_block)?,
    ])
}

fn single_scalar_temp_write(block: &HirBlock) -> Option<TempId> {
    let [stmt] = block.stmts.as_slice() else {
        return None;
    };
    stmt.scalar_temp_assignment().map(|(temp, _)| temp)
}

fn summarize_block_fallthrough_assignments(
    block: &HirBlock,
    safety: HirExprSafety,
) -> Result<FallthroughSummary, RegionCfgFailure> {
    Ok(RegionTempFlow::for_block(block, safety)?.summarize())
}

#[derive(Default)]
struct TempFlowEvent {
    reads: BTreeSet<TempId>,
    writes: BTreeSet<TempId>,
    gc_inert_writes: BTreeSet<TempId>,
}

struct RegionTempFlow<'a> {
    graph: HirFlowGraph<'a>,
    events: Vec<TempFlowEvent>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum RegionCfgFailure {
    AmbiguousLabel,
    ExternalGoto,
}

impl From<LexicalCfgFailure> for RegionCfgFailure {
    fn from(_: LexicalCfgFailure) -> Self {
        Self::AmbiguousLabel
    }
}

impl<'a> RegionTempFlow<'a> {
    fn for_block(block: &'a HirBlock, safety: HirExprSafety) -> Result<Self, RegionCfgFailure> {
        Self::from_graph(HirFlowGraph::for_block(block, safety)?, safety)
    }

    fn for_stmts(stmts: &'a [HirStmt], safety: HirExprSafety) -> Result<Self, RegionCfgFailure> {
        Self::from_graph(HirFlowGraph::for_stmts(stmts, safety)?, safety)
    }

    fn from_graph(
        graph: HirFlowGraph<'a>,
        safety: HirExprSafety,
    ) -> Result<Self, RegionCfgFailure> {
        if graph.has_reachable_unresolved_goto() {
            return Err(RegionCfgFailure::ExternalGoto);
        }
        let events = graph
            .nodes()
            .iter()
            .map(|node| temp_flow_event(node.kind(), safety))
            .collect();
        Ok(Self { graph, events })
    }

    fn fallthrough_temp_is_gc_inert(&self, temp: TempId) -> bool {
        let incoming = self.graph.solve_forward(
            false,
            |current, outgoing| {
                let merged = *current && *outgoing;
                let changed = *current != merged;
                *current = merged;
                changed
            },
            |id, _, outgoing| {
                let incoming = *outgoing;
                if self.events[id.index()].writes.contains(&temp) {
                    *outgoing = self.events[id.index()].gc_inert_writes.contains(&temp);
                }
                incoming
            },
        );

        incoming[self.graph.exit().index()] == Some(true)
    }

    fn summarize(&self) -> FallthroughSummary {
        let mut summary = FallthroughSummary::default();
        self.graph.solve_forward(
            BTreeSet::new(),
            |current, outgoing| {
                let before = current.len();
                current.retain(|temp| outgoing.contains(temp));
                current.len() != before
            },
            |id, _, outgoing| {
                let event = &self.events[id.index()];
                // must-def 在首次到达后只会交集缩小，未定义读取只会增长；直接汇总
                // 单调观察结果，避免为每个节点保留整份已赋值集合。
                summary
                    .reads_before_assignment
                    .extend(event.reads.difference(outgoing).copied());
                if id == self.graph.exit() {
                    summary.falls_through = true;
                    summary.assigned_temps.clone_from(outgoing);
                }
                outgoing.extend(event.writes.iter().copied());
            },
        );

        summary
    }
}

fn temp_flow_event(kind: HirFlowNodeKind<'_>, safety: HirExprSafety) -> TempFlowEvent {
    // GlobalDecl 只写全局名字，但 RHS 仍可先读 temp；不能因不是 Temp Assign 就漏掉读取。
    let mut collector = TempReadCollector::default();
    kind.visit_evaluation(&mut collector);
    let reads = collector.temps;
    let HirFlowNodeKind::Stmt(HirStmt::Assign(assign)) = kind else {
        return TempFlowEvent {
            reads,
            ..TempFlowEvent::default()
        };
    };
    let mut writes = BTreeSet::new();
    let mut gc_inert_writes = BTreeSet::new();
    // 并行赋值的重复目标由最后一次写决定；逆序首次登记时直接读取对应 RHS，
    // 不为每个 temp 重新扫描整组目标。未知 tail 仍不能证明其结果 GC 惰性。
    for (index, target) in assign.targets.iter().enumerate().rev() {
        if let HirLValue::Temp(temp) = target
            && writes.insert(*temp)
            && assign.values.fixed.get(index).map_or_else(
                || assign.values.tail.is_none(),
                |value| safety.result_is_gc_inert(value),
            )
        {
            gc_inert_writes.insert(*temp);
        }
    }
    TempFlowEvent {
        reads,
        writes,
        gc_inert_writes,
    }
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = &'a FallthroughSummary>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .filter(|summary| summary.falls_through)
        .map(|summary| &summary.assigned_temps);
    let mut intersection = fallthrough_sets.next()?.clone();
    for set in fallthrough_sets {
        intersection.retain(|temp| set.contains(temp));
    }
    Some(intersection)
}
