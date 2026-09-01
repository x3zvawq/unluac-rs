//! 这个文件负责 `locals` pass 内部的 if/else fallthrough 赋值汇总。
//!
//! 主 pass 在普通 temp 链之外，还需要识别一种稳定形状：`if` 的 then/else 两侧都给同一个
//! temp 赋值，合流之后又继续读取这个 temp。这里会把这种 temp 报告给主 pass，让主 pass
//! 在 if 前分配一个空 local，再由两条分支写回同一个 binding。
//!
//! 本文件只消费当前 HIR 树和 `TempTouchIndex`，不分配 local、不改写语句。分支摘要同时
//! 维护“所有合流路径都已写入”和“首次写入前可能读取”，因此主 pass 只会在声明可以
//! 支配所有读取时接受候选。global 声明只向全局名字提交写入，它的 RHS temp 读取仍纳入
//! read-before-def；不会因为 AST-owned 声明身份而丢掉同 arm 后续的 temp must-def。常真
//! while 还会汇总所有 break 出口的 must-def；普通 while 保留零次执行路径，不会把 body
//! 写入误报成 loop fallthrough 写入。
//!
//! 输入形状：`if c then t1 = a else t1 = b end; use(t1)`。
//! 输出形状：候选 temp 集合 `{ t1 }`，后续由主 pass 物化成 `local l; if c then l = a else l = b end`。

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use super::super::expr_facts::expr_truthiness;
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

    common_temps
        .into_iter()
        .filter(|temp| !is_reserved(*temp))
        .filter(|temp| !reads_before_assignment.contains(temp))
        // 候选拒绝[SemanticBarrier:Lifetime]：`t=obj; if c then t=a else t=b end; GC` 若在 if 前另建 local，旧 t 物理槽不再按原时点覆盖，弱表/`__gc` 可观察旧对象延寿。
        .filter(|temp| !temp_touches.touches_before(stmt_index, *temp))
        // 候选拒绝[LayerBoundary]：合流后没有 touch 的 branch temp 是 dead-temps 的删除候选，不应物化为空 local。
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
    Ok(RegionCfg::build(block, safety)?.summarize())
}

type FlowNodeId = usize;

#[derive(Default)]
struct FlowNode {
    reads: BTreeSet<TempId>,
    writes: BTreeSet<TempId>,
    successors: BTreeSet<FlowNodeId>,
}

struct RegionCfg {
    nodes: Vec<FlowNode>,
    entry: FlowNodeId,
    exit: FlowNodeId,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum RegionCfgFailure {
    AmbiguousLabel,
    ExternalGoto,
}

impl RegionCfg {
    fn build(block: &HirBlock, safety: HirExprSafety) -> Result<Self, RegionCfgFailure> {
        let mut builder = RegionCfgBuilder {
            nodes: vec![FlowNode::default()],
            labels: BTreeMap::new(),
            pending_gotos: Vec::new(),
            safety,
        };
        let exit = 0;
        let entry = builder
            .build_block(&block.stmts, exit, None, None)
            .ok_or(RegionCfgFailure::AmbiguousLabel)?;
        let mut external_goto_sources = Vec::new();
        for (source, target) in builder.pending_gotos {
            // Direct and nested local labels are resolved against the complete region
            // map, including backward edges. An outer target cannot be classified as
            // a terminal edge without the owner block, so report it to the caller.
            if let Some(&target) = builder.labels.get(&target) {
                builder.nodes[source].successors.insert(target);
            } else {
                external_goto_sources.push(source);
            }
        }
        let reachable = reachable_flow_nodes(&builder.nodes, entry);
        if external_goto_sources
            .into_iter()
            .any(|source| reachable[source])
        {
            return Err(RegionCfgFailure::ExternalGoto);
        }
        Ok(Self {
            nodes: builder.nodes,
            entry,
            exit,
        })
    }

    fn summarize(&self) -> FallthroughSummary {
        let mut incoming = vec![None::<BTreeSet<TempId>>; self.nodes.len()];
        incoming[self.entry] = Some(BTreeSet::new());
        let mut pending = VecDeque::from([self.entry]);

        while let Some(node_id) = pending.pop_front() {
            let mut outgoing = incoming[node_id]
                .clone()
                .expect("worklist only contains reachable CFG nodes");
            outgoing.extend(self.nodes[node_id].writes.iter().copied());
            for &successor in &self.nodes[node_id].successors {
                let changed = match &mut incoming[successor] {
                    Some(current) => {
                        let intersection = current
                            .intersection(&outgoing)
                            .copied()
                            .collect::<BTreeSet<_>>();
                        if *current == intersection {
                            false
                        } else {
                            *current = intersection;
                            true
                        }
                    }
                    slot @ None => {
                        *slot = Some(outgoing.clone());
                        true
                    }
                };
                if changed {
                    pending.push_back(successor);
                }
            }
        }

        let reads_before_assignment = self
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(node_id, node)| incoming[node_id].as_ref().map(|defs| (node, defs)))
            .flat_map(|(node, defs)| node.reads.difference(defs).copied())
            .collect();
        let assigned_temps = incoming[self.exit].clone().unwrap_or_default();
        FallthroughSummary {
            falls_through: incoming[self.exit].is_some(),
            assigned_temps,
            reads_before_assignment,
        }
    }
}

fn reachable_flow_nodes(nodes: &[FlowNode], entry: FlowNodeId) -> Vec<bool> {
    let mut reachable = vec![false; nodes.len()];
    reachable[entry] = true;
    let mut pending = vec![entry];
    while let Some(node) = pending.pop() {
        for &successor in &nodes[node].successors {
            if !reachable[successor] {
                reachable[successor] = true;
                pending.push(successor);
            }
        }
    }
    reachable
}

struct RegionCfgBuilder {
    nodes: Vec<FlowNode>,
    labels: BTreeMap<crate::hir::common::HirLabelId, FlowNodeId>,
    pending_gotos: Vec<(FlowNodeId, crate::hir::common::HirLabelId)>,
    safety: HirExprSafety,
}

impl RegionCfgBuilder {
    fn new_node(
        &mut self,
        reads: BTreeSet<TempId>,
        writes: BTreeSet<TempId>,
        successors: impl IntoIterator<Item = FlowNodeId>,
    ) -> FlowNodeId {
        let id = self.nodes.len();
        self.nodes.push(FlowNode {
            reads,
            writes,
            successors: successors.into_iter().collect(),
        });
        id
    }

    fn build_block(
        &mut self,
        stmts: &[HirStmt],
        next: FlowNodeId,
        break_target: Option<FlowNodeId>,
        continue_target: Option<FlowNodeId>,
    ) -> Option<FlowNodeId> {
        let mut entry = next;
        for stmt in stmts.iter().rev() {
            entry = self.build_stmt(stmt, entry, break_target, continue_target)?;
        }
        Some(entry)
    }

    fn build_stmt(
        &mut self,
        stmt: &HirStmt,
        next: FlowNodeId,
        break_target: Option<FlowNodeId>,
        continue_target: Option<FlowNodeId>,
    ) -> Option<FlowNodeId> {
        match stmt {
            HirStmt::Label(label) => {
                let node = self.new_node(BTreeSet::new(), BTreeSet::new(), [next]);
                if self.labels.insert(label.id, node).is_some() {
                    return None;
                }
                Some(node)
            }
            HirStmt::Goto(goto) => {
                let node = self.new_node(BTreeSet::new(), BTreeSet::new(), []);
                self.pending_gotos.push((node, goto.target));
                Some(node)
            }
            HirStmt::Break => Some(self.new_node(BTreeSet::new(), BTreeSet::new(), break_target)),
            HirStmt::Continue => {
                Some(self.new_node(BTreeSet::new(), BTreeSet::new(), continue_target))
            }
            HirStmt::Return(_) => Some(self.new_node(stmt_reads(stmt), BTreeSet::new(), [])),
            HirStmt::Block(block) => {
                self.build_block(&block.stmts, next, break_target, continue_target)
            }
            HirStmt::If(if_stmt) => {
                let then_entry = self.build_block(
                    &if_stmt.then_block.stmts,
                    next,
                    break_target,
                    continue_target,
                )?;
                let else_entry = match &if_stmt.else_block {
                    Some(block) => {
                        self.build_block(&block.stmts, next, break_target, continue_target)?
                    }
                    None => next,
                };
                let successors = match expr_truthiness(&if_stmt.cond, self.safety) {
                    Some(true) => vec![then_entry],
                    Some(false) => vec![else_entry],
                    None => vec![then_entry, else_entry],
                };
                Some(self.new_node(
                    collect_temp_refs_in_expr(&if_stmt.cond),
                    BTreeSet::new(),
                    successors,
                ))
            }
            HirStmt::While(while_stmt) => {
                let condition = self.new_node(BTreeSet::new(), BTreeSet::new(), []);
                let body = self.build_block(
                    &while_stmt.body.stmts,
                    condition,
                    Some(next),
                    Some(condition),
                )?;
                self.nodes[condition].reads = collect_temp_refs_in_expr(&while_stmt.cond);
                match expr_truthiness(&while_stmt.cond, self.safety) {
                    Some(true) => self.nodes[condition].successors.insert(body),
                    Some(false) => self.nodes[condition].successors.insert(next),
                    None => {
                        self.nodes[condition].successors.extend([body, next]);
                        true
                    }
                };
                Some(condition)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let condition = self.new_node(BTreeSet::new(), BTreeSet::new(), []);
                let body = self.build_block(
                    &repeat_stmt.body.stmts,
                    condition,
                    Some(next),
                    Some(condition),
                )?;
                self.nodes[condition].reads = collect_temp_refs_in_expr(&repeat_stmt.cond);
                match expr_truthiness(&repeat_stmt.cond, self.safety) {
                    Some(true) => self.nodes[condition].successors.insert(next),
                    Some(false) => self.nodes[condition].successors.insert(body),
                    None => {
                        self.nodes[condition].successors.extend([body, next]);
                        true
                    }
                };
                Some(body)
            }
            HirStmt::NumericFor(numeric_for) => {
                let dispatch = self.new_node(BTreeSet::new(), BTreeSet::new(), []);
                let body = self.build_block(
                    &numeric_for.body.stmts,
                    dispatch,
                    Some(next),
                    Some(dispatch),
                )?;
                self.nodes[dispatch].successors.extend([body, next]);
                Some(
                    self.new_node(
                        collect_temp_refs_in_expr(&numeric_for.start)
                            .into_iter()
                            .chain(collect_temp_refs_in_expr(&numeric_for.limit))
                            .chain(collect_temp_refs_in_expr(&numeric_for.step))
                            .collect(),
                        BTreeSet::new(),
                        [dispatch],
                    ),
                )
            }
            HirStmt::GenericFor(generic_for) => {
                let dispatch = self.new_node(BTreeSet::new(), BTreeSet::new(), []);
                let body = self.build_block(
                    &generic_for.body.stmts,
                    dispatch,
                    Some(next),
                    Some(dispatch),
                )?;
                self.nodes[dispatch].successors.extend([body, next]);
                Some(
                    self.new_node(
                        generic_for
                            .iterator
                            .iter()
                            .flat_map(collect_temp_refs_in_expr)
                            .collect(),
                        BTreeSet::new(),
                        [dispatch],
                    ),
                )
            }
            HirStmt::Assign(assign) => Some(
                self.new_node(
                    stmt_reads(stmt),
                    assign
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
                        .collect(),
                    [next],
                ),
            ),
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::TableSetList(_) => {
                Some(self.new_node(stmt_reads(stmt), BTreeSet::new(), [next]))
            }
        }
    }
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
        candidate_temps(
            stmt,
            &TempTouchIndex::new(&stmt_refs),
            0,
            &|_| false,
            HirExprSafety::for_dialect(crate::decompile::DecompileDialect::Auto),
        )
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
