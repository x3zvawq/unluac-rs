//! value-merge 短路的 conditional reassign 计划恢复。
//!
//! 这个模块只处理一类值型短路：部分叶子保留 merge 前旧值，另一部分叶子写入新值。
//! 这种形状在 HIR 中更适合恢复成 `init + if cond then assign end`，而不是强行折成
//! 一个大型逻辑表达式。它依赖 StructureFacts 给出的 short-circuit DAG / value incoming，
//! 不重新扫描 CFG 去识别短路候选，也不负责普通 branch short-circuit 或 subject 消费保护。
//!
//! 例子：
//! - 输入形状：`x = x or y` 对应的 value merge
//! - 输出计划：`x = <entry>; if <reaches changed region> then x = <changed value> end`

use super::recovery::recover_pure_value_decision_expr_with_allowed_blocks;
use super::*;

/// 当值型 merge 本质上是在“保留旧值”和“条件写入新值”之间二选一时，
/// HIR 更适合把它恢复成 `init + if cond then assign end`，而不是一整个大表达式。
pub(crate) struct ConditionalReassignPlan {
    pub merge: BlockRef,
    pub phi_id: PhiId,
    pub target_temp: TempId,
    pub init_value: HirExpr,
    pub cond: HirExpr,
    pub assigned_value: HirExpr,
}

/// 如果一个 value merge 的一部分叶子只是“把 merge 前的旧值原样带过去”，
/// 而另一部分叶子才真正产生新值，那么这更像 `if cond then x = new end`。
pub(crate) fn build_conditional_reassign_plan(
    lowering: &ProtoLowering<'_>,
    header: BlockRef,
) -> Option<ConditionalReassignPlan> {
    let short = value_merge_candidate_by_header(lowering, header)?;
    let ShortCircuitExit::ValueMerge(merge) = short.exit else {
        return None;
    };
    let phi_id = short.result_phi_id?;
    if phi_use_count(lowering, phi_id) <= 1 {
        return None;
    }
    let entry_defs = short.entry_defs.clone();
    if entry_defs.is_empty() {
        return None;
    }

    let leaf_kinds = classify_value_leaves(short, &entry_defs)?;
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
    let init_value = preserved_entry_value_expr(lowering, &entry_defs)?;
    let target_temp = *lowering.bindings.phi_temps.get(phi_id.index())?;

    Some(ConditionalReassignPlan {
        merge,
        phi_id,
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
    lowering.dataflow.phi_use_count(phi_id)
}

fn preserved_entry_value_expr(
    lowering: &ProtoLowering<'_>,
    entry_defs: &BTreeSet<DefId>,
) -> Option<HirExpr> {
    if entry_defs.len() == 1 {
        let def = *entry_defs
            .iter()
            .next()
            .expect("len checked above, exactly one reaching def exists");
        let temp = *lowering.bindings.fixed_temps.get(def.index())?;
        return Some(HirExpr::TempRef(temp));
    }

    let mut shared_expr = None;
    for def in entry_defs {
        let expr = expr_for_dup_safe_fixed_def(lowering, *def)?;
        if shared_expr
            .as_ref()
            .is_some_and(|known_expr: &HirExpr| *known_expr != expr)
        {
            return None;
        }
        shared_expr = Some(expr);
    }

    shared_expr
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
    short: &ShortCircuitCandidate,
    entry_defs: &BTreeSet<DefId>,
) -> Option<BTreeMap<BlockRef, ValueLeafKind>> {
    let mut leaf_kinds = BTreeMap::new();
    let mut has_preserved = false;
    let mut has_changed = false;

    for incoming in &short.value_incomings {
        let kind = if incoming.defs.iter().eq(entry_defs.iter()) {
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
    let node_depths = short.node_depths();
    let candidates = short
        .nodes
        .iter()
        .filter_map(|node| {
            let leaves = short.node_leaves(node.id, &mut leaf_memo);
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
        ChangedRegionEntry::Node(node_ref) => recover_pure_value_decision_expr_with_allowed_blocks(
            lowering,
            short,
            node_ref,
            &BTreeSet::new(),
        )
        .map(|(expr, _)| expr),
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
            short
                .node_leaves(node_ref, &mut memo)
                .contains(&region_block)
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
