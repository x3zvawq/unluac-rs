//! 这个文件集中处理 HIR 对短路 DAG 的消费。
//!
//! `StructureFacts` 现在提供的是“按 truthy/falsy 连边的短路 DAG”，而不是先验压平
//! 的线性链。这里的职责就是把这些 DAG 重新折回 HIR 的 `LogicalAnd / LogicalOr`，
//! 同时保留值位置和条件位置在 Lua 里的不同语义。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, DefId, PhiCandidate, PhiId, SsaValue};
use crate::hir::common::{
    HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef, HirDecisionTarget, HirExpr, TempId,
};
use crate::hir::decision::{finalize_condition_decision_expr, finalize_value_decision_expr};
use crate::structure::{
    ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode, ShortCircuitNodeRef,
    ShortCircuitTarget,
};
use crate::transformer::LowInstr;

use super::exprs::{
    expr_for_fixed_def, expr_for_reg_at_block_entry, expr_for_reg_use, lower_branch_subject,
    lower_branch_subject_inline,
};
use super::{ProtoLowering, is_control_terminator};

/// 条件型短路恢复后交给结构层继续决定 `if-then` 还是 `if-else`。
pub(super) struct BranchShortCircuitPlan {
    pub cond: HirExpr,
    pub truthy: BlockRef,
    pub falsy: BlockRef,
    pub consumed_headers: Vec<BlockRef>,
}

/// 当值型 merge 本质上是在“保留旧值”和“条件写入新值”之间二选一时，
/// HIR 更适合把它恢复成 `init + if cond then assign end`，而不是一整个大表达式。
pub(super) struct ConditionalReassignPlan {
    pub merge: BlockRef,
    pub phi_id: PhiId,
    pub target_temp: TempId,
    pub init_value: HirExpr,
    pub cond: HirExpr,
    pub assigned_value: HirExpr,
}

/// 尝试把 merge 点上的 phi 候选直接恢复成值级短路表达式。
pub(super) fn recover_value_phi_expr(
    lowering: &ProtoLowering<'_>,
    phi: &PhiCandidate,
) -> Option<HirExpr> {
    recover_value_phi_expr_with_allowed_blocks(lowering, phi, &BTreeSet::new())
}

pub(super) fn recover_value_phi_expr_with_allowed_blocks(
    lowering: &ProtoLowering<'_>,
    phi: &PhiCandidate,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Option<HirExpr> {
    let short = lowering.structure.short_circuit_candidates.iter().find(|candidate| {
        candidate.reducible
            && candidate.result_reg == Some(phi.reg)
            && matches!(candidate.exit, ShortCircuitExit::ValueMerge(merge) if merge == phi.block)
    })?;
    let decision = build_value_decision_expr(lowering, short, short.entry)?;
    if decision_references_forbidden_candidate_temps(lowering, short, &decision, allowed_blocks) {
        return None;
    }
    Some(finalize_value_decision_expr(decision))
}

/// 条件型短路恢复入口。
pub(super) fn build_branch_short_circuit_plan(
    lowering: &ProtoLowering<'_>,
    header: BlockRef,
) -> Option<BranchShortCircuitPlan> {
    let short = lowering
        .structure
        .short_circuit_candidates
        .iter()
        .find(|candidate| {
            candidate.header == header
                && candidate.reducible
                && matches!(candidate.exit, ShortCircuitExit::BranchExit { .. })
        })?;
    let ShortCircuitExit::BranchExit { truthy, falsy } = short.exit else {
        return None;
    };

    let decision = build_branch_decision_expr(lowering, short, short.entry)?;
    let allowed_blocks = BTreeSet::from([header]);
    if decision_references_forbidden_candidate_temps(lowering, short, &decision, &allowed_blocks) {
        return None;
    }
    let cond = finalize_condition_decision_expr(decision);
    let consumed_headers = short.nodes.iter().map(|node| node.header).collect();

    Some(BranchShortCircuitPlan {
        cond,
        truthy,
        falsy,
        consumed_headers,
    })
}

/// 如果一个 value merge 的一部分叶子只是“把 merge 前的旧值原样带过去”，
/// 而另一部分叶子才真正产生新值，那么这更像 `if cond then x = new end`。
pub(super) fn build_conditional_reassign_plan(
    lowering: &ProtoLowering<'_>,
    header: BlockRef,
) -> Option<ConditionalReassignPlan> {
    let short = value_merge_candidate_by_header(lowering, header)?;
    let ShortCircuitExit::ValueMerge(merge) = short.exit else {
        return None;
    };
    let reg = short.result_reg?;
    let phi = lowering
        .dataflow
        .phi_candidates
        .iter()
        .find(|phi| phi.block == merge && phi.reg == reg)?;
    if phi_use_count(lowering, phi.id) <= 1 {
        return None;
    }
    let instr_ref = lowering.cfg.blocks[header.index()].instrs.last()?;
    let entry_defs = lowering.dataflow.reaching_defs[instr_ref.index()]
        .fixed
        .get(&reg)?
        .clone();
    if entry_defs.is_empty() {
        return None;
    }

    let leaf_kinds = classify_value_leaves(phi, &entry_defs)?;
    let changed_region = find_changed_region_entry(short, &leaf_kinds)?;
    let cond_decision = build_region_reach_decision_expr(lowering, short, changed_region)?;
    let allowed_blocks = BTreeSet::from([header]);
    if decision_references_forbidden_candidate_temps(
        lowering,
        short,
        &cond_decision,
        &allowed_blocks,
    ) {
        return None;
    }
    let cond = finalize_condition_decision_expr(cond_decision);
    let assigned_value = build_changed_region_value_expr(lowering, short, changed_region)?;
    let init_value = expr_for_reg_use(lowering, header, instr_ref, reg);
    let target_temp = *lowering.bindings.phi_temps.get(phi.id.index())?;

    Some(ConditionalReassignPlan {
        merge,
        phi_id: phi.id,
        target_temp,
        init_value,
        cond,
        assigned_value,
    })
}

/// 单次消费的 value merge 更像普通值表达式，强行提前拆成 `init + if` 反而会把
/// `a and b` / `a or b` 这类很自然的 Lua 形状拉坏。所以这里只在 merge 值后续
/// 被多次读取时，才把它恢复成“保留旧值 + 条件改写”的语句结构。
fn phi_use_count(lowering: &ProtoLowering<'_>, phi_id: PhiId) -> usize {
    lowering
        .dataflow
        .use_values
        .iter()
        .flat_map(|uses| uses.fixed.values())
        .filter(|values| values.contains(&SsaValue::Phi(phi_id)))
        .count()
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum ValueLeafKind {
    Preserved,
    Changed,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum ChangedRegionEntry {
    Node(ShortCircuitNodeRef),
    Leaf(BlockRef),
}

fn classify_value_leaves(
    phi: &PhiCandidate,
    entry_defs: &BTreeSet<DefId>,
) -> Option<BTreeMap<BlockRef, ValueLeafKind>> {
    let mut leaf_kinds = BTreeMap::new();
    let mut has_preserved = false;
    let mut has_changed = false;

    for incoming in &phi.incoming {
        let kind = if &incoming.defs == entry_defs {
            has_preserved = true;
            ValueLeafKind::Preserved
        } else {
            has_changed = true;
            ValueLeafKind::Changed
        };
        leaf_kinds.insert(incoming.pred, kind);
    }

    (has_preserved && has_changed).then_some(leaf_kinds)
}

fn find_changed_region_entry(
    short: &ShortCircuitCandidate,
    leaf_kinds: &BTreeMap<BlockRef, ValueLeafKind>,
) -> Option<ChangedRegionEntry> {
    let changed_leaves = leaf_kinds
        .iter()
        .filter_map(|(block, kind)| (*kind == ValueLeafKind::Changed).then_some(*block))
        .collect::<BTreeSet<_>>();
    if changed_leaves.is_empty() {
        return None;
    }

    let mut leaf_memo = BTreeMap::new();
    let node_depths = short_circuit_node_depths(short);
    let candidates = short
        .nodes
        .iter()
        .filter_map(|node| {
            let leaves = collect_node_leaves(short, node.id, &mut leaf_memo);
            (leaves == changed_leaves).then_some(node.id)
        })
        .collect::<Vec<_>>();

    // 这里必须选“最浅”的 changed-only 子图入口，而不是最深的那个命中节点。
    //
    // 原因是 conditional reassign 需要覆盖“所有发生改写的路径”。如果选得过深，
    // 它虽然也可能拥有同一批叶子，但已经落在某个 changed 分支内部，最终会把
    // `"yes" / "maybe" / "no"` 这类整体改写错误截成更窄的一支。
    candidates
        .into_iter()
        .min_by_key(|node_ref| {
            (
                node_depths.get(node_ref).copied().unwrap_or(usize::MAX),
                node_ref.index(),
            )
        })
        .map(ChangedRegionEntry::Node)
        .or_else(|| {
            (changed_leaves.len() == 1)
                .then(|| changed_leaves.iter().next().copied())
                .flatten()
                .map(ChangedRegionEntry::Leaf)
        })
}

fn short_circuit_node_depths(
    short: &ShortCircuitCandidate,
) -> BTreeMap<ShortCircuitNodeRef, usize> {
    let mut depths = BTreeMap::new();
    let mut worklist = vec![(short.entry, 0usize)];

    while let Some((node_ref, depth)) = worklist.pop() {
        if depths
            .get(&node_ref)
            .is_some_and(|known_depth| *known_depth <= depth)
        {
            continue;
        }
        depths.insert(node_ref, depth);

        let Some(node) = short.nodes.get(node_ref.index()) else {
            continue;
        };
        if let ShortCircuitTarget::Node(next_ref) = node.truthy {
            worklist.push((next_ref, depth + 1));
        }
        if let ShortCircuitTarget::Node(next_ref) = node.falsy {
            worklist.push((next_ref, depth + 1));
        }
    }

    depths
}

fn collect_node_leaves(
    short: &ShortCircuitCandidate,
    node_ref: ShortCircuitNodeRef,
    memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
) -> BTreeSet<BlockRef> {
    if let Some(leaves) = memo.get(&node_ref) {
        return leaves.clone();
    }

    let Some(node) = short.nodes.get(node_ref.index()) else {
        return BTreeSet::new();
    };

    let mut leaves = collect_target_leaves(short, &node.truthy, memo);
    leaves.extend(collect_target_leaves(short, &node.falsy, memo));
    memo.insert(node_ref, leaves.clone());
    leaves
}

fn collect_target_leaves(
    short: &ShortCircuitCandidate,
    target: &ShortCircuitTarget,
    memo: &mut BTreeMap<ShortCircuitNodeRef, BTreeSet<BlockRef>>,
) -> BTreeSet<BlockRef> {
    match target {
        ShortCircuitTarget::Node(next_ref) => collect_node_leaves(short, *next_ref, memo),
        ShortCircuitTarget::Value(block) => BTreeSet::from([*block]),
        ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => BTreeSet::new(),
    }
}

fn build_region_reach_decision_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    region: ChangedRegionEntry,
) -> Option<HirDecisionExpr> {
    build_decision_expr(
        lowering,
        short,
        short.entry,
        lower_short_circuit_subject_inline,
        |_, target| {
            if target_is_region_entry(target, region) {
                return Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                    HirExpr::Boolean(true),
                )));
            }

            match target {
                ShortCircuitTarget::Node(next_ref)
                    if node_contains_region(short, *next_ref, region) =>
                {
                    Some(DecisionEdge::Node(*next_ref))
                }
                ShortCircuitTarget::Node(_)
                | ShortCircuitTarget::Value(_)
                | ShortCircuitTarget::TruthyExit
                | ShortCircuitTarget::FalsyExit => Some(DecisionEdge::Leaf(
                    HirDecisionTarget::Expr(HirExpr::Boolean(false)),
                )),
            }
        },
    )
}

fn build_changed_region_value_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    region: ChangedRegionEntry,
) -> Option<HirExpr> {
    match region {
        ChangedRegionEntry::Node(node_ref) => {
            let decision = build_value_decision_expr(lowering, short, node_ref)?;
            if decision_references_forbidden_candidate_temps(
                lowering,
                short,
                &decision,
                &BTreeSet::new(),
            ) {
                return None;
            }
            Some(finalize_value_decision_expr(decision))
        }
        ChangedRegionEntry::Leaf(block) => lower_value_leaf_expr(lowering, short, block),
    }
}

fn target_is_region_entry(target: &ShortCircuitTarget, region: ChangedRegionEntry) -> bool {
    match (target, region) {
        (ShortCircuitTarget::Node(node_ref), ChangedRegionEntry::Node(region_ref)) => {
            *node_ref == region_ref
        }
        (ShortCircuitTarget::Value(block), ChangedRegionEntry::Leaf(region_block)) => {
            *block == region_block
        }
        _ => false,
    }
}

fn node_contains_region(
    short: &ShortCircuitCandidate,
    node_ref: ShortCircuitNodeRef,
    region: ChangedRegionEntry,
) -> bool {
    match region {
        ChangedRegionEntry::Node(region_ref) => {
            let mut visited = BTreeSet::new();
            node_reaches_node(short, node_ref, region_ref, &mut visited)
        }
        ChangedRegionEntry::Leaf(region_block) => {
            let mut memo = BTreeMap::new();
            collect_node_leaves(short, node_ref, &mut memo).contains(&region_block)
        }
    }
}

fn node_reaches_node(
    short: &ShortCircuitCandidate,
    start: ShortCircuitNodeRef,
    target: ShortCircuitNodeRef,
    visited: &mut BTreeSet<ShortCircuitNodeRef>,
) -> bool {
    if start == target {
        return true;
    }
    if !visited.insert(start) {
        return false;
    }

    let Some(node) = short.nodes.get(start.index()) else {
        return false;
    };

    target_reaches_node(short, &node.truthy, target, visited)
        || target_reaches_node(short, &node.falsy, target, visited)
}

fn target_reaches_node(
    short: &ShortCircuitCandidate,
    target: &ShortCircuitTarget,
    node_ref: ShortCircuitNodeRef,
    visited: &mut BTreeSet<ShortCircuitNodeRef>,
) -> bool {
    match target {
        ShortCircuitTarget::Node(next_ref) => {
            node_reaches_node(short, *next_ref, node_ref, visited)
        }
        ShortCircuitTarget::Value(_)
        | ShortCircuitTarget::TruthyExit
        | ShortCircuitTarget::FalsyExit => false,
    }
}

/// 如果某个 branch header 已经被值型短路完整消费，结构层就不应该再产出一层重复 `if`。
pub(super) fn value_merge_candidate_by_header<'a>(
    lowering: &'a ProtoLowering<'_>,
    header: BlockRef,
) -> Option<&'a ShortCircuitCandidate> {
    lowering
        .structure
        .short_circuit_candidates
        .iter()
        .find(|candidate| {
            candidate.header == header
                && candidate.reducible
                && matches!(candidate.exit, ShortCircuitExit::ValueMerge(_))
        })
}

/// 值型短路被消费时，需要把候选区域里的其余 block 标记成“已经由表达式吸收”。
pub(super) fn value_merge_skipped_blocks(short: &ShortCircuitCandidate) -> BTreeSet<BlockRef> {
    short
        .blocks
        .iter()
        .copied()
        .filter(|block| *block != short.header)
        .collect()
}

fn build_branch_decision_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
) -> Option<HirDecisionExpr> {
    build_decision_expr(
        lowering,
        short,
        entry,
        lower_short_circuit_subject,
        |node, target| match target {
            ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
            ShortCircuitTarget::TruthyExit => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                HirExpr::Boolean(true),
            ))),
            ShortCircuitTarget::FalsyExit => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                HirExpr::Boolean(false),
            ))),
            ShortCircuitTarget::Value(block) if *block == node.header => Some(DecisionEdge::Leaf(
                HirDecisionTarget::Expr(HirExpr::Boolean(true)),
            )),
            ShortCircuitTarget::Value(_) => None,
        },
    )
}

fn build_value_decision_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
) -> Option<HirDecisionExpr> {
    build_decision_expr(
        lowering,
        short,
        entry,
        lower_short_circuit_subject_inline,
        |node, target| match target {
            ShortCircuitTarget::Node(next_ref) => Some(DecisionEdge::Node(*next_ref)),
            ShortCircuitTarget::Value(block) if *block == node.header => {
                Some(DecisionEdge::Leaf(HirDecisionTarget::CurrentValue))
            }
            ShortCircuitTarget::Value(block) => Some(DecisionEdge::Leaf(HirDecisionTarget::Expr(
                lower_value_leaf_expr(lowering, short, *block)?,
            ))),
            ShortCircuitTarget::TruthyExit | ShortCircuitTarget::FalsyExit => None,
        },
    )
}

#[derive(Debug, Clone)]
enum DecisionEdge {
    Node(ShortCircuitNodeRef),
    Leaf(HirDecisionTarget),
}

/// 共享 DAG 恢复本身就是一次图重建过程，这里把中间状态收进一个结构体里，
/// 避免在递归构图时把 `remap/nodes` 之类的细节参数层层外泄。
struct DecisionBuildState {
    remap: BTreeMap<ShortCircuitNodeRef, HirDecisionNodeRef>,
    nodes: Vec<HirDecisionNode>,
}

fn build_decision_expr<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
    test_for_block: FTest,
    target_for_edge: FTarget,
) -> Option<HirDecisionExpr>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    let mut state = DecisionBuildState {
        remap: BTreeMap::new(),
        nodes: Vec::new(),
    };
    let entry = build_decision_node(
        lowering,
        short,
        entry,
        &test_for_block,
        &target_for_edge,
        &mut state,
    )?;
    Some(HirDecisionExpr {
        entry,
        nodes: state.nodes,
    })
}

fn build_decision_node<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    node_ref: ShortCircuitNodeRef,
    test_for_block: &FTest,
    target_for_edge: &FTarget,
    state: &mut DecisionBuildState,
) -> Option<HirDecisionNodeRef>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    if let Some(mapped) = state.remap.get(&node_ref) {
        return Some(*mapped);
    }

    let node = short.nodes.get(node_ref.index())?;
    let mapped = HirDecisionNodeRef(state.nodes.len());
    state.remap.insert(node_ref, mapped);
    state.nodes.push(HirDecisionNode {
        id: mapped,
        test: HirExpr::Boolean(false),
        truthy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
        falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
    });

    let test = test_for_block(lowering, node.header)?;
    let truthy = build_decision_target(
        lowering,
        short,
        node,
        &node.truthy,
        test_for_block,
        target_for_edge,
        state,
    )?;
    let falsy = build_decision_target(
        lowering,
        short,
        node,
        &node.falsy,
        test_for_block,
        target_for_edge,
        state,
    )?;

    state.nodes[mapped.index()] = HirDecisionNode {
        id: mapped,
        test,
        truthy,
        falsy,
    };
    Some(mapped)
}

fn build_decision_target<FTest, FTarget>(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    node: &ShortCircuitNode,
    target: &ShortCircuitTarget,
    test_for_block: &FTest,
    target_for_edge: &FTarget,
    state: &mut DecisionBuildState,
) -> Option<HirDecisionTarget>
where
    FTest: Fn(&ProtoLowering<'_>, BlockRef) -> Option<HirExpr>,
    FTarget: Fn(&ShortCircuitNode, &ShortCircuitTarget) -> Option<DecisionEdge>,
{
    match target_for_edge(node, target)? {
        DecisionEdge::Node(next_ref) => Some(HirDecisionTarget::Node(build_decision_node(
            lowering,
            short,
            next_ref,
            test_for_block,
            target_for_edge,
            state,
        )?)),
        DecisionEdge::Leaf(target) => Some(target),
    }
}

pub(super) fn lower_short_circuit_subject(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<HirExpr> {
    let instr_ref = lowering.cfg.blocks[block.index()].instrs.last()?;
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr_ref.index()] else {
        return None;
    };

    Some(lower_branch_subject(
        lowering,
        block,
        instr_ref,
        branch.cond,
    ))
}

fn lower_short_circuit_subject_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> Option<HirExpr> {
    let instr_ref = lowering.cfg.blocks[block.index()].instrs.last()?;
    let LowInstr::Branch(branch) = &lowering.proto.instrs[instr_ref.index()] else {
        return None;
    };

    Some(lower_branch_subject_inline(
        lowering,
        block,
        instr_ref,
        branch.cond,
    ))
}

fn lower_value_leaf_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    block: BlockRef,
) -> Option<HirExpr> {
    if short.nodes.iter().any(|node| node.header == block) {
        return lower_short_circuit_subject(lowering, block);
    }

    let def = latest_reg_def_in_block(lowering, block, short.result_reg?)?;
    expr_for_fixed_def(lowering, def)
}

/// 语句级短路恢复已经先把 leaf block 自己的副作用语句物化出来了。
///
/// 因此这里不能再把 leaf 结果重新 inline 成 `call(...)` 之类的表达式，而是应该优先
/// 引用“这个 block 最后一次给 result_reg 写出的稳定绑定”；若本 block 没有重写它，
/// 就回退到 block 入口时已经可见的那个值。
pub(super) fn lower_materialized_value_leaf_expr(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    block: BlockRef,
) -> Option<HirExpr> {
    let reg = short.result_reg?;
    if short.nodes.iter().any(|node| node.header == block) {
        return lower_short_circuit_subject(lowering, block);
    }

    if let Some(def) = latest_reg_def_in_block(lowering, block, reg) {
        return Some(HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]));
    }

    Some(expr_for_reg_at_block_entry(lowering, block, reg))
}

pub(super) fn latest_reg_def_in_block(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: crate::transformer::Reg,
) -> Option<DefId> {
    let range = lowering.cfg.blocks[block.index()].instrs;
    let last = range.last()?;
    let last_instr = &lowering.proto.instrs[last.index()];
    let end = if matches!(last_instr, LowInstr::Jump(_)) {
        range.end().checked_sub(1)?
    } else if is_control_terminator(last_instr) {
        return None;
    } else {
        range.end()
    };

    (range.start.index()..end)
        .flat_map(|instr_index| lowering.dataflow.instr_defs[instr_index].iter().copied())
        .rfind(|def_id| lowering.dataflow.defs[def_id.index()].reg == reg)
}

fn decision_references_forbidden_candidate_temps(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    decision: &HirDecisionExpr,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> bool {
    let forbidden = short
        .blocks
        .iter()
        .copied()
        .filter(|block| !allowed_blocks.contains(block))
        .flat_map(|block| {
            let range = lowering.cfg.blocks[block.index()].instrs;
            (range.start.index()..range.end())
                .flat_map(|instr_index| lowering.dataflow.instr_defs[instr_index].iter().copied())
                .map(|def_id| lowering.bindings.fixed_temps[def_id.index()])
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();

    decision.nodes.iter().any(|node| {
        expr_references_any_temp(&node.test, &forbidden)
            || decision_target_references_any_temp(&node.truthy, &forbidden)
            || decision_target_references_any_temp(&node.falsy, &forbidden)
    })
}

fn decision_target_references_any_temp(
    target: &HirDecisionTarget,
    forbidden: &BTreeSet<TempId>,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => expr_references_any_temp(expr, forbidden),
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn expr_references_any_temp(expr: &HirExpr, forbidden: &BTreeSet<TempId>) -> bool {
    match expr {
        HirExpr::TempRef(temp) => forbidden.contains(temp),
        HirExpr::TableAccess(access) => {
            expr_references_any_temp(&access.base, forbidden)
                || expr_references_any_temp(&access.key, forbidden)
        }
        HirExpr::Unary(unary) => expr_references_any_temp(&unary.expr, forbidden),
        HirExpr::Binary(binary) => {
            expr_references_any_temp(&binary.lhs, forbidden)
                || expr_references_any_temp(&binary.rhs, forbidden)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_references_any_temp(&logical.lhs, forbidden)
                || expr_references_any_temp(&logical.rhs, forbidden)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_references_any_temp(&node.test, forbidden)
                || decision_target_references_any_temp(&node.truthy, forbidden)
                || decision_target_references_any_temp(&node.falsy, forbidden)
        }),
        HirExpr::Call(call) => {
            expr_references_any_temp(&call.callee, forbidden)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_references_any_temp(arg, forbidden))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                crate::hir::common::HirTableField::Array(expr) => {
                    expr_references_any_temp(expr, forbidden)
                }
                crate::hir::common::HirTableField::Record(field) => {
                    matches!(
                        &field.key,
                        crate::hir::common::HirTableKey::Expr(expr)
                            if expr_references_any_temp(expr, forbidden)
                    ) || expr_references_any_temp(&field.value, forbidden)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|expr| expr_references_any_temp(expr, forbidden))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_references_any_temp(&capture.value, forbidden)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::structure::{
        ShortCircuitCandidate, ShortCircuitExit, ShortCircuitNode, ShortCircuitTarget,
    };

    #[test]
    fn conditional_reassign_picks_shallowest_changed_only_region() {
        let short = ShortCircuitCandidate {
            header: BlockRef(12),
            blocks: BTreeSet::from([
                BlockRef(12),
                BlockRef(13),
                BlockRef(14),
                BlockRef(15),
                BlockRef(16),
                BlockRef(17),
                BlockRef(18),
                BlockRef(19),
                BlockRef(20),
                BlockRef(21),
                BlockRef(22),
            ]),
            entry: ShortCircuitNodeRef(0),
            nodes: vec![
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(0),
                    header: BlockRef(12),
                    truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(1)),
                    falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(6)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(1),
                    header: BlockRef(13),
                    truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(2)),
                    falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(6)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(2),
                    header: BlockRef(16),
                    truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(3)),
                    falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(4)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(3),
                    header: BlockRef(17),
                    truthy: ShortCircuitTarget::Value(BlockRef(18)),
                    falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(4)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(4),
                    header: BlockRef(19),
                    truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(5)),
                    falsy: ShortCircuitTarget::Value(BlockRef(22)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(5),
                    header: BlockRef(20),
                    truthy: ShortCircuitTarget::Value(BlockRef(21)),
                    falsy: ShortCircuitTarget::Value(BlockRef(22)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(6),
                    header: BlockRef(14),
                    truthy: ShortCircuitTarget::Value(BlockRef(14)),
                    falsy: ShortCircuitTarget::Node(ShortCircuitNodeRef(7)),
                },
                ShortCircuitNode {
                    id: ShortCircuitNodeRef(7),
                    header: BlockRef(15),
                    truthy: ShortCircuitTarget::Node(ShortCircuitNodeRef(2)),
                    falsy: ShortCircuitTarget::Value(BlockRef(15)),
                },
            ],
            exit: ShortCircuitExit::ValueMerge(BlockRef(23)),
            result_reg: None,
            reducible: true,
        };
        let leaf_kinds = BTreeMap::from([
            (BlockRef(14), ValueLeafKind::Preserved),
            (BlockRef(15), ValueLeafKind::Preserved),
            (BlockRef(18), ValueLeafKind::Changed),
            (BlockRef(21), ValueLeafKind::Changed),
            (BlockRef(22), ValueLeafKind::Changed),
        ]);

        let region = find_changed_region_entry(&short, &leaf_kinds);

        assert_eq!(
            region,
            Some(ChangedRegionEntry::Node(ShortCircuitNodeRef(2)))
        );
    }
}
