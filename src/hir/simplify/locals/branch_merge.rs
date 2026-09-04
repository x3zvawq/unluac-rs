//! 这个文件负责 `locals` pass 内部的 if/else fallthrough 赋值汇总。
//!
//! 主 pass 在普通 temp 链之外，还需要识别一种稳定形状：`if` 的 then/else 两侧都给同一个
//! temp 赋值，合流之后又继续读取这个 temp。这里会把这种 temp 报告给主 pass，让主 pass
//! 在 if 前分配一个空 local，再由两条分支写回同一个 binding。
//!
//! 本文件消费共享 `HirFlowGraph` topology/worklist、当前 HIR 语义事件和 `TempTouchIndex`，
//! 只声明 must 状态的 transfer/intersection，不自行解析 label/goto/loop，也不分配 local、
//! 不改写语句。分支摘要同时
//! 维护“所有合流路径都已写入”和“首次写入前可能读取”，因此主 pass 只会在声明可以
//! 支配所有读取时接受候选。global 声明只向全局名字提交写入，它的 RHS temp 读取仍纳入
//! read-before-def；不会因为 AST-owned 声明身份而丢掉同 arm 后续的 temp must-def。常真
//! while 还会汇总所有 break 出口的 must-def；普通 while 保留零次执行路径，不会把 body
//! 写入误报成 loop fallthrough 写入。
//!
//! 输入形状：`if c then t1 = a else t1 = b end; use(t1)`。
//! 输出形状：候选 temp 集合 `{ t1 }`，后续由主 pass 物化成 `local l; if c then l = a else l = b end`。

use std::collections::BTreeSet;

use super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind, LexicalCfgFailure};
use super::super::temp_touch::{
    TempTouchIndex, collect_temp_reads_by_stmt, collect_temp_refs_in_expr,
};
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
    temp_touches: &TempTouchIndex,
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
    let prefix_cfg = RegionTempFlow::for_stmts(&owner_stmts[..stmt_index], safety).ok();

    common_temps
        .into_iter()
        .filter(|temp| !is_reserved(*temp))
        .filter(|temp| !reads_before_assignment.contains(temp))
        .filter(|temp| {
            if !temp_touches.touches_before(stmt_index, *temp)
                || prefix_cfg
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
        .filter(|temp| temp_touches.touches_after(stmt_index + 1, *temp))
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
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [_], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some(*temp)
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
        let incoming = self.graph.solve_forward(
            BTreeSet::new(),
            |current, outgoing| {
                let before = current.len();
                current.retain(|temp| outgoing.contains(temp));
                current.len() != before
            },
            |id, _, outgoing| {
                let incoming = outgoing.clone();
                outgoing.extend(self.events[id.index()].writes.iter().copied());
                incoming
            },
        );

        let reads_before_assignment = self
            .events
            .iter()
            .enumerate()
            .filter_map(|(node_id, node)| incoming[node_id].as_ref().map(|defs| (node, defs)))
            .flat_map(|(node, defs)| node.reads.difference(defs).copied())
            .collect();
        let assigned_temps = incoming[self.graph.exit().index()]
            .clone()
            .unwrap_or_default();
        FallthroughSummary {
            falls_through: incoming[self.graph.exit().index()].is_some(),
            assigned_temps,
            reads_before_assignment,
        }
    }
}

fn temp_flow_event(kind: HirFlowNodeKind<'_>, safety: HirExprSafety) -> TempFlowEvent {
    let reads = match kind {
        HirFlowNodeKind::Exit
        | HirFlowNodeKind::FunctionExit
        | HirFlowNodeKind::UnknownControl
        | HirFlowNodeKind::NumericForDispatch
        | HirFlowNodeKind::GenericForDispatch(_)
        | HirFlowNodeKind::ForBinding(_) => BTreeSet::new(),
        HirFlowNodeKind::RepeatCondition(repeat_stmt) => {
            collect_temp_refs_in_expr(&repeat_stmt.cond)
        }
        HirFlowNodeKind::Stmt(stmt) => match stmt {
            HirStmt::Block(_) | HirStmt::Repeat(_) => BTreeSet::new(),
            HirStmt::If(if_stmt) => collect_temp_refs_in_expr(&if_stmt.cond),
            HirStmt::While(while_stmt) => collect_temp_refs_in_expr(&while_stmt.cond),
            HirStmt::NumericFor(for_stmt) => collect_temp_refs_in_expr(&for_stmt.start)
                .into_iter()
                .chain(collect_temp_refs_in_expr(&for_stmt.limit))
                .chain(collect_temp_refs_in_expr(&for_stmt.step))
                .collect(),
            HirStmt::GenericFor(for_stmt) => for_stmt
                .iterator
                .iter()
                .flat_map(collect_temp_refs_in_expr)
                .collect(),
            _ => stmt_reads(stmt),
        },
        HirFlowNodeKind::GenericForInit(flow) => flow
            .for_stmt()
            .iterator
            .iter()
            .flat_map(collect_temp_refs_in_expr)
            .collect(),
    };
    let HirFlowNodeKind::Stmt(HirStmt::Assign(assign)) = kind else {
        return TempFlowEvent {
            reads,
            ..TempFlowEvent::default()
        };
    };
    let writes = assign
        .targets
        .iter()
        .filter_map(|target| match target {
            HirLValue::Temp(temp) => Some(*temp),
            HirLValue::Param(_)
            | HirLValue::Local(_)
            | HirLValue::Upvalue(_)
            | HirLValue::Global(_)
            | HirLValue::TableAccess(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let gc_inert_writes = writes
        .iter()
        .copied()
        .filter(|temp| assignment_final_temp_value_is_gc_inert(assign, *temp, safety))
        .collect();
    TempFlowEvent {
        reads,
        writes,
        gc_inert_writes,
    }
}

fn assignment_final_temp_value_is_gc_inert(
    assign: &crate::hir::common::HirAssign,
    temp: TempId,
    safety: HirExprSafety,
) -> bool {
    let Some(index) = assign
        .targets
        .iter()
        .rposition(|target| matches!(target, HirLValue::Temp(target) if *target == temp))
    else {
        return false;
    };
    assign.values.fixed.get(index).map_or_else(
        || assign.values.tail.is_none(),
        |value| safety.result_is_gc_inert(value),
    )
}

fn stmt_reads(stmt: &HirStmt) -> BTreeSet<TempId> {
    collect_temp_reads_by_stmt(std::slice::from_ref(stmt))
        .into_iter()
        .next()
        .unwrap_or_default()
}

fn intersect_fallthrough_assignment_sets<'a>(
    summaries: impl IntoIterator<Item = &'a FallthroughSummary>,
) -> Option<BTreeSet<TempId>> {
    let mut fallthrough_sets = summaries
        .into_iter()
        .filter(|summary| summary.falls_through)
        .map(|summary| summary.assigned_temps.clone());
    let mut intersection = fallthrough_sets.next()?;
    for set in fallthrough_sets {
        intersection = intersection
            .intersection(&set)
            .copied()
            .collect::<BTreeSet<_>>();
    }
    Some(intersection)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::ParamId;
    use crate::hir::common::{
        HirAssign, HirExpr, HirGoto, HirIf, HirLabel, HirLabelId, HirReturn, HirValuePack,
    };

    fn block(stmts: Vec<HirStmt>) -> HirBlock {
        HirBlock { stmts }
    }

    fn assign_temp(temp: TempId) -> HirStmt {
        assign_temp_value(temp, HirExpr::Integer(1))
    }

    fn assign_temp_value(temp: TempId, value: HirExpr) -> HirStmt {
        HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Temp(temp)],
            values: HirValuePack::fixed(vec![value]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }))
    }

    fn goto(label: HirLabelId) -> HirStmt {
        HirStmt::Goto(Box::new(HirGoto { target: label }))
    }

    fn label(id: HirLabelId) -> HirStmt {
        HirStmt::Label(Box::new(HirLabel {
            id,
            tbc_barriers: Vec::new(),
        }))
    }

    fn branch(then_stmts: Vec<HirStmt>, else_stmts: Vec<HirStmt>) -> HirStmt {
        HirStmt::If(Box::new(HirIf {
            cond: HirExpr::Boolean(true),
            then_block: block(then_stmts),
            else_block: Some(block(else_stmts)),
        }))
    }

    fn candidates(stmt: &HirStmt, temp: TempId) -> Vec<TempId> {
        let stmt_refs = [BTreeSet::from([temp]), BTreeSet::from([temp])];
        let owner_stmts = [stmt.clone()];
        candidate_temps(
            &owner_stmts,
            stmt,
            &TempTouchIndex::new(&stmt_refs),
            0,
            &|_| false,
            HirExprSafety::for_dialect(crate::decompile::DecompileDialect::Auto),
        )
    }

    fn candidates_after_prefix(prefix: HirStmt, temp: TempId) -> Vec<TempId> {
        let candidate = branch(vec![assign_temp(temp)], vec![assign_temp(temp)]);
        let stmts = vec![
            prefix,
            candidate,
            HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::fixed(vec![HirExpr::TempRef(temp)]),
            })),
        ];
        let stmt_refs = vec![BTreeSet::from([temp]); stmts.len()];
        candidate_temps(
            &stmts,
            &stmts[1],
            &TempTouchIndex::new(&stmt_refs),
            1,
            &|_| false,
            HirExprSafety::for_dialect(crate::decompile::DecompileDialect::Lua54),
        )
    }

    #[test]
    fn prior_gc_inert_write_does_not_create_a_false_lifetime_barrier() {
        let temp = TempId(0);

        assert_eq!(
            candidates_after_prefix(assign_temp_value(temp, HirExpr::Boolean(false)), temp),
            vec![temp]
        );
    }

    #[test]
    fn prefix_must_end_every_fallthrough_with_a_gc_inert_value() {
        let temp = TempId(0);
        let both_inert = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::ParamRef(ParamId(0)),
            then_block: block(vec![assign_temp_value(temp, HirExpr::Boolean(false))]),
            else_block: Some(block(vec![assign_temp_value(temp, HirExpr::Integer(0))])),
        }));
        assert_eq!(candidates_after_prefix(both_inert, temp), vec![temp]);

        let maybe_old_root = HirStmt::If(Box::new(HirIf {
            cond: HirExpr::ParamRef(ParamId(0)),
            then_block: block(vec![assign_temp_value(temp, HirExpr::Boolean(false))]),
            else_block: Some(block(Vec::new())),
        }));
        assert!(candidates_after_prefix(maybe_old_root, temp).is_empty());
    }

    #[test]
    fn prior_collectable_write_keeps_the_lifetime_barrier() {
        let temp = TempId(0);

        assert!(
            candidates_after_prefix(
                assign_temp_value(temp, HirExpr::TableConstructor(Box::default())),
                temp,
            )
            .is_empty()
        );
    }

    #[test]
    fn goto_unknown_arm_cannot_be_ignored_during_merge() {
        let temp = TempId(0);
        let stmt = branch(vec![goto(HirLabelId(0))], vec![assign_temp(temp)]);

        assert!(candidates(&stmt, temp).is_empty());
    }

    #[test]
    fn unreachable_external_goto_does_not_disable_the_region_proof() {
        let temp = TempId(0);
        let stmt = branch(
            vec![
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::Boolean(false),
                    then_block: block(vec![goto(HirLabelId(9))]),
                    else_block: None,
                })),
                assign_temp(temp),
            ],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }

    #[test]
    fn local_forward_goto_follows_the_reachable_assignment_path() {
        let temp = TempId(0);
        let skipped = TempId(1);
        let join = HirLabelId(0);
        let stmt = branch(
            vec![
                goto(join),
                assign_temp_value(skipped, HirExpr::TempRef(temp)),
                label(join),
                assign_temp(temp),
            ],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }

    #[test]
    fn local_forward_goto_does_not_count_a_skipped_assignment() {
        let temp = TempId(0);
        let join = HirLabelId(0);
        let stmt = branch(
            vec![goto(join), assign_temp(temp), label(join)],
            vec![assign_temp(temp)],
        );

        assert!(candidates(&stmt, temp).is_empty());
    }

    #[test]
    fn local_backward_loop_that_never_falls_through_does_not_block_other_arm() {
        let temp = TempId(0);
        let head = HirLabelId(0);
        let stmt = branch(
            vec![label(head), assign_temp(temp), goto(head)],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }

    #[test]
    fn nested_backward_edge_uses_region_wide_must_def() {
        let temp = TempId(0);
        let condition = TempId(1);
        let head = HirLabelId(0);
        let stmt = branch(
            vec![
                label(head),
                assign_temp(temp),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(condition),
                    then_block: block(vec![goto(head)]),
                    else_block: Some(block(Vec::new())),
                })),
            ],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }

    #[test]
    fn nested_backward_edge_keeps_first_iteration_read_before_def() {
        let temp = TempId(0);
        let condition = TempId(1);
        let head = HirLabelId(0);
        let stmt = branch(
            vec![
                label(head),
                assign_temp_value(TempId(2), HirExpr::TempRef(temp)),
                assign_temp(temp),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(condition),
                    then_block: block(vec![goto(head)]),
                    else_block: Some(block(Vec::new())),
                })),
            ],
            vec![assign_temp(temp)],
        );

        assert!(candidates(&stmt, temp).is_empty());
    }

    #[test]
    fn proven_terminal_arm_does_not_block_clean_fallthrough_merge() {
        let temp = TempId(0);
        let stmt = branch(
            vec![HirStmt::Return(Box::new(HirReturn {
                values: HirValuePack::default(),
            }))],
            vec![assign_temp(temp)],
        );

        assert_eq!(candidates(&stmt, temp), vec![temp]);
    }
}
