//! 从共享 HIR CFG 投影显式资源的活跃程序点，保留 Structure 发布的 origin 身份。
//!
//! 范围只是一份候选：may 活跃点给出末端，must 活跃点检查范围内的求值事件。
//! 例如 `TBC a; if x then goto out end; Close(a); side; ::out::` 中 side 不属于 a；
//! goto 只消费目标实际跨过的 cleanup 事件，不用 must-active barrier 的补集推断关闭。
//! 本模块不重建 CFG、寄存器覆盖或 loop cleanup 协议，也不直接删除 Close。
//! 求值事件按顶层位置累计总数，origin 只索引可接受事件；相同 owner 的多个 typed event
//! 分别计数。候选以区间计数相等证明 must 覆盖，不逐候选重扫整张事件表。
//! 事件的根层位置在共享图构建时投影到节点索引；不另走语句树建立地址到位置的关联。

use super::super::lexical_cfg::{FlowRefinement, HirFlowGraph, HirFlowNodeKind};
use super::{ScopeCandidate, paired_return_cleanup};
use crate::hir::common::{HirBlock, HirStmt};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::visit::{HirVisitor, visit_stmts};
use crate::transformer::InstrRef;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Default)]
struct Active {
    may: BTreeSet<InstrRef>,
    must: BTreeSet<InstrRef>,
}

pub(super) fn scope_ends(
    stmts: &[HirStmt],
    candidates: &[ScopeCandidate],
    safety: HirExprSafety,
) -> BTreeMap<InstrRef, Option<usize>> {
    let origins = candidates
        .iter()
        .map(|scope| scope.origin)
        .collect::<BTreeSet<_>>();
    let paired_returns = paired_return_cleanups(stmts);
    let mut unpaired_origins = BTreeSet::<InstrRef>::new();
    let mut positions = Vec::new();
    let mut goto_cleanup = BTreeMap::new();
    let graph = HirFlowGraph::for_stmts_with_locations(stmts, safety, |id, event, block, index| {
        positions.resize(id.index() + 1, 0);
        positions[id.index()] = block.root_stmt_index(index);
        if let HirFlowNodeKind::Stmt(stmt @ HirStmt::Close(close)) = event
            && matches!(close.kind, crate::transformer::CloseKind::Return(_))
            && !paired_returns.contains(&std::ptr::from_ref(stmt).addr())
        {
            unpaired_origins.extend(&close.origins);
        }
        if let HirFlowNodeKind::Stmt(HirStmt::Label(label)) = event {
            goto_cleanup.insert(label.id, label.entry_cleanup.clone());
        }
    })
    .expect("HIR resource scope has unique labels");
    let mut last_live = BTreeMap::<InstrRef, usize>::new();
    let states = graph.solve_forward(
        Active::default(),
        |target, incoming| {
            let old_may = target.may.len();
            let old_must = target.must.len();
            target.may.extend(&incoming.may);
            target.must.retain(|origin| incoming.must.contains(origin));
            target.may.len() != old_may || target.must.len() != old_must
        },
        |id, event, active| {
            let stmt = graph.nodes()[id.index()].owner_stmt();
            let observation = stmt.map(|stmt| {
                let position = positions[id.index()];
                let accepted = if matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_)) {
                    None
                } else {
                    let mut accepted = active.must.iter().copied().collect::<Vec<_>>();
                    if let HirStmt::Close(close) = stmt {
                        accepted.extend(close.origins.iter().copied().filter(|origin| {
                            origins.contains(origin) && !active.must.contains(origin)
                        }));
                        accepted.sort_unstable();
                        accepted.dedup();
                    }
                    Some(accepted)
                };
                (position, stmt, accepted)
            });
            // may transfer 单调；回边重访只能增加已见位置，直接发布最大值即可。
            // goto 自身仍发生在退出前，其它事件保持原来的 transfer 后观察约定。
            if let Some((position, HirStmt::Goto(_), _)) = &observation {
                record_last_live(&mut last_live, &active.may, *position);
            }
            if let HirFlowNodeKind::Stmt(stmt) = event {
                match stmt {
                    HirStmt::ToBeClosed(tbc) if origins.contains(&tbc.origin) => {
                        active.may.insert(tbc.origin);
                        active.must.insert(tbc.origin);
                    }
                    HirStmt::Close(close)
                        if !paired_returns.contains(&std::ptr::from_ref(stmt).addr()) =>
                    {
                        for origin in &close.origins {
                            active.may.remove(origin);
                            active.must.remove(origin);
                        }
                    }
                    HirStmt::Goto(goto) => {
                        for origin in goto_cleanup
                            .get(&goto.target)
                            .into_iter()
                            .flat_map(|origins| origins.iter())
                        {
                            active.may.remove(origin);
                            active.must.remove(origin);
                        }
                    }
                    _ => {}
                }
            }
            observation.and_then(|(position, stmt, accepted)| {
                if !matches!(stmt, HirStmt::Goto(_)) {
                    record_last_live(&mut last_live, &active.may, position);
                }
                accepted.map(|accepted| (position, accepted))
            })
        },
        |_expr, _truthy, _state| FlowRefinement::Unchanged,
    );
    let mut event_prefix = vec![0usize; stmts.len() + 1];
    let mut accepted_positions = BTreeMap::<InstrRef, Vec<usize>>::new();
    for (position, accepted) in states.into_iter().flatten().flatten() {
        event_prefix[position + 1] += 1;
        for origin in accepted {
            accepted_positions.entry(origin).or_default().push(position);
        }
    }
    for index in 1..event_prefix.len() {
        event_prefix[index] += event_prefix[index - 1];
    }
    for positions in accepted_positions.values_mut() {
        // 图节点顺序不是词法位置顺序；保留同位置的各个事件，不能使用会去重的位置索引。
        positions.sort_unstable();
    }
    candidates
        .iter()
        .map(|scope| {
            let end = last_live.get(&scope.origin).copied().filter(|&end| {
                if unpaired_origins.contains(&scope.origin) {
                    return false;
                }
                let start = scope.start + 2;
                if end <= start {
                    return true;
                }
                let accepted = accepted_positions
                    .get(&scope.origin)
                    .map_or(0, |positions| {
                        positions.partition_point(|&position| position < end)
                            - positions.partition_point(|&position| position < start)
                    });
                accepted == event_prefix[end] - event_prefix[start]
            });
            (scope.origin, end)
        })
        .collect()
}

fn record_last_live(
    last_live: &mut BTreeMap<InstrRef, usize>,
    active: &BTreeSet<InstrRef>,
    position: usize,
) {
    for &origin in active {
        last_live
            .entry(origin)
            .and_modify(|last| *last = (*last).max(position + 1))
            .or_insert(position + 1);
    }
}

/// 原始 Return 的 cleanup 只能与同一直属块中相邻、同来源的 Return 共同物化。
fn paired_return_cleanups(stmts: &[HirStmt]) -> BTreeSet<usize> {
    struct Collector(BTreeSet<usize>);
    impl Collector {
        fn record(&mut self, stmts: &[HirStmt]) {
            for (index, stmt) in stmts.iter().enumerate() {
                if paired_return_cleanup(stmts, index) {
                    self.0.insert(std::ptr::from_ref(stmt).addr());
                }
            }
        }
    }
    impl HirVisitor<'_> for Collector {
        fn visit_block(&mut self, block: &HirBlock) {
            self.record(&block.stmts);
        }
    }
    let mut collector = Collector(BTreeSet::new());
    collector.record(stmts);
    visit_stmts(stmts, &mut collector);
    collector.0
}
