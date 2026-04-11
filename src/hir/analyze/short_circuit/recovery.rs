//! 这个子模块负责把短路值合流恢复成更接近源码的 HIR 计划。
//!
//! 它依赖 StructureFacts 给好的短路 DAG、value merge 事实和 HIR lowering 上下文，不会
//! 回头重新扫描 CFG 去猜短路形状。
//! 例如：`x = x or y` 对应的 merge，可能在这里恢复成“条件重赋值”计划而不是裸 phi。

use super::*;

/// 条件型短路恢复后交给结构层继续决定 `if-then` 还是 `if-else`。
pub(crate) struct BranchShortCircuitPlan {
    pub cond: HirExpr,
    pub truthy: BlockRef,
    pub falsy: BlockRef,
    pub consumed_headers: Vec<BlockRef>,
}

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

#[derive(Debug, Clone)]
pub(crate) enum ValueMergeExprRecovery {
    Pure {
        expr: HirExpr,
        consumed_header_subject: bool,
    },
    Impure(HirExpr),
}

impl ValueMergeExprRecovery {
    fn into_expr(self) -> HirExpr {
        match self {
            Self::Pure { expr, .. } | Self::Impure(expr) => expr,
        }
    }

    pub(crate) fn consumes_header_subject(&self) -> bool {
        match self {
            Self::Pure {
                consumed_header_subject,
                ..
            } => *consumed_header_subject,
            Self::Impure(_) => true,
        }
    }
}

pub(crate) fn recover_short_value_merge_expr_with_allowed_blocks(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Option<HirExpr> {
    recover_short_value_merge_expr_recovery_with_allowed_blocks(lowering, short, allowed_blocks)
        .map(ValueMergeExprRecovery::into_expr)
}

pub(crate) fn recover_short_value_merge_expr_recovery_with_allowed_blocks(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Option<ValueMergeExprRecovery> {
    if let Some((expr, consumed_header_subject)) =
        recover_pure_value_decision_expr_with_allowed_blocks(
            lowering,
            short,
            short.entry,
            allowed_blocks,
        )
    {
        let recovery = ValueMergeExprRecovery::Pure {
            expr,
            consumed_header_subject,
        };
        if !expr_references_consumed_subject_temps(lowering, short, &recovery) {
            return Some(recovery);
        }
    }

    let expr = build_impure_value_merge_expr(lowering, short, short.entry)?;
    if expr_references_forbidden_candidate_temps(lowering, short, &expr, allowed_blocks) {
        return None;
    }
    let recovery = ValueMergeExprRecovery::Impure(expr);
    if expr_references_consumed_subject_temps(lowering, short, &recovery) {
        return None;
    }
    Some(recovery)
}

fn recover_pure_value_decision_expr_with_allowed_blocks(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    entry: ShortCircuitNodeRef,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Option<(HirExpr, bool)> {
    let decision = build_value_decision_expr(lowering, short, entry)?;
    let decision_needs_single_eval =
        decision_references_forbidden_candidate_temps(lowering, short, &decision, allowed_blocks);
    let decision = if decision_needs_single_eval {
        build_value_decision_expr_single_eval(lowering, short, entry)?
    } else {
        decision
    };
    if decision_references_forbidden_candidate_temps(lowering, short, &decision, allowed_blocks) {
        return None;
    }
    let expr = finalize_value_decision_expr(decision);
    if matches!(&expr, HirExpr::Decision(decision) if !decision_is_synth_safe(decision)) {
        return None;
    }
    Some((expr, decision_needs_single_eval))
}

pub(crate) fn value_merge_candidates_in_block<'a>(
    lowering: &'a ProtoLowering<'a>,
    block: BlockRef,
) -> impl Iterator<Item = &'a ShortCircuitCandidate> + 'a {
    lowering
        .structure
        .short_circuit_candidates
        .iter()
        .filter(move |candidate| {
            candidate.reducible
                && matches!(candidate.exit, ShortCircuitExit::ValueMerge(merge) if merge == block)
        })
}

/// 条件型短路恢复入口。
pub(crate) fn build_branch_short_circuit_plan(
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
                && matches!(
                    candidate.exit,
                    ShortCircuitExit::BranchExit { .. } | ShortCircuitExit::ValueMerge(_)
                )
        })?;
    let (truthy, falsy, decision) = match short.exit {
        ShortCircuitExit::BranchExit { truthy, falsy } => (
            truthy,
            falsy,
            build_branch_decision_expr(lowering, short, short.entry)?,
        ),
        ShortCircuitExit::ValueMerge(_) => {
            let (truthy, falsy, truthy_leaves, falsy_leaves) =
                branch_exit_blocks_from_value_merge_candidate(short)?;
            (
                truthy,
                falsy,
                build_branch_decision_expr_for_value_merge_candidate(
                    lowering,
                    short,
                    &truthy_leaves,
                    &falsy_leaves,
                )?,
            )
        }
    };

    let consumed_headers = short
        .nodes
        .iter()
        .map(|node| node.header)
        .collect::<Vec<_>>();
    // structured branch short-circuit 只会显式物化入口 header 的 block prefix；
    // 其余 consumed headers 会直接被整段吃掉，不会再单独 lower。
    //
    // 因此这里不能把“后续 header 里定义出来的 temp”也算进允许范围，否则 cond
    // 一旦还引用这些 temp，就会得到“定义语句被吞掉，但 temp 仍留在条件/then 里”
    // 的悬空 HIR。多节点链条里只有入口 header 自己的 temp 能保证随后会被物化。
    let allowed_blocks = BTreeSet::from([header]);
    let decision = if decision_references_forbidden_candidate_temps(
        lowering,
        short,
        &decision,
        &allowed_blocks,
    ) {
        match short.exit {
            // branch short-circuit 的最终条件只会在当前结构位点求值一次。
            // 当后续 consumed header 的 subject 只是被保守地留成 temp ref 时，
            // 这里允许沿既有 decision builder 退回到 single-eval lowering，
            // 把那一跳恢复成源码级操作数本体，而不是直接整段退化成布尔壳。
            ShortCircuitExit::BranchExit { .. } => {
                build_branch_decision_expr_single_eval(lowering, short, short.entry)?
            }
            ShortCircuitExit::ValueMerge(_) => {
                let (_, _, truthy_leaves, falsy_leaves) =
                    branch_exit_blocks_from_value_merge_candidate(short)?;
                build_branch_decision_expr_for_value_merge_candidate_single_eval(
                    lowering,
                    short,
                    &truthy_leaves,
                    &falsy_leaves,
                )?
            }
        }
    } else {
        decision
    };
    if decision_references_forbidden_candidate_temps(lowering, short, &decision, &allowed_blocks) {
        return None;
    }
    let cond = finalize_condition_decision_expr(decision);

    Some(BranchShortCircuitPlan {
        cond,
        truthy,
        falsy,
        consumed_headers,
    })
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
pub(super) enum ValueLeafKind {
    Preserved,
    Changed,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub(super) enum ChangedRegionEntry {
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

pub(super) fn find_changed_region_entry(
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

/// 如果某个 branch header 已经被值型短路完整消费，结构层就不应该再产出一层重复 `if`。
pub(crate) fn value_merge_candidate_by_header<'a>(
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
pub(crate) fn value_merge_skipped_blocks(short: &ShortCircuitCandidate) -> BTreeSet<BlockRef> {
    short
        .blocks
        .iter()
        .copied()
        .filter(|block| *block != short.header)
        .collect()
}
/// 当值短路恢复把 header 的 subject 吸收进表达式后（`consumes_header_subject`），
/// subject-producing 指令会被 suppress，其 def 对应的 temp 不再有独立的赋值语句。
/// 如果已构建的表达式在 subject 以外的子树中仍引用了这些 temp（例如 `t999["key"]`），
/// 就会产生"空 local"孤儿。该函数检测这种情况，让调用方能及时拒绝本次恢复。
fn expr_references_consumed_subject_temps(
    lowering: &ProtoLowering<'_>,
    short: &ShortCircuitCandidate,
    recovery: &ValueMergeExprRecovery,
) -> bool {
    if !recovery.consumes_header_subject() {
        return false;
    }
    let consumed_instrs = consumed_value_merge_subject_instrs(lowering, short.header);
    if consumed_instrs.is_empty() {
        return false;
    }
    let consumed_temps: BTreeSet<TempId> = consumed_instrs
        .into_iter()
        .flat_map(|instr| {
            lowering.dataflow.instr_defs[instr.index()]
                .iter()
                .copied()
                .map(|def_id| lowering.bindings.fixed_temps[def_id.index()])
        })
        .collect();
    let expr = match recovery {
        ValueMergeExprRecovery::Pure { expr, .. } | ValueMergeExprRecovery::Impure(expr) => expr,
    };
    super::guards::expr_references_any_temp(expr, &consumed_temps)
}
/// 当值短路已经把某个 branch header 的 subject 直接吸收到表达式里时，紧邻 branch 的
/// subject-producing def 不应该再作为 prefix 语句单独物化，否则就会出现“先求值一次，
/// 表达式里又再求值一次”的重复。
///
/// 这里刻意只吃当前 header 内、且没有被后续 prefix 指令再次读取的那批 def，避免把
/// 还服务于其它前缀语句的中间值一起抹掉。
pub(crate) fn consumed_value_merge_subject_instrs(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
) -> BTreeSet<InstrRef> {
    let range = lowering.cfg.blocks[block.index()].instrs;
    let Some(branch_instr_ref) = range.last() else {
        return BTreeSet::new();
    };
    let LowInstr::Branch(branch) = &lowering.proto.instrs[branch_instr_ref.index()] else {
        return BTreeSet::new();
    };

    let mut candidate_defs = BTreeSet::new();
    for reg in branch_cond_regs(branch.cond) {
        collect_consumed_single_eval_defs(
            lowering,
            block,
            branch_instr_ref,
            reg,
            &mut candidate_defs,
        );
    }

    let candidate_instrs = candidate_defs
        .iter()
        .map(|def_id| lowering.dataflow.def_instr(*def_id))
        .collect::<BTreeSet<_>>();

    candidate_defs
        .into_iter()
        .filter_map(|def_id| {
            let def_instr = lowering.dataflow.def_instr(def_id);
            let effect = &lowering.dataflow.instr_effects[def_instr.index()];
            let used_elsewhere = effect.fixed_must_defs.iter().any(|reg| {
                ((def_instr.index() + 1)..branch_instr_ref.index()).any(|instr_index| {
                    lowering.dataflow.instr_effects[instr_index]
                        .fixed_uses
                        .contains(reg)
                        && !candidate_instrs.contains(&InstrRef(instr_index))
                })
            });
            (!used_elsewhere).then_some(def_instr)
        })
        .collect()
}

fn collect_consumed_single_eval_defs(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    consumer_instr: InstrRef,
    reg: Reg,
    out: &mut BTreeSet<DefId>,
) {
    let Some(values) = lowering.dataflow.use_values_at(consumer_instr).get(reg) else {
        return;
    };
    if values.len() != 1 {
        return;
    }
    let Some(SsaValue::Def(def_id)) = values.iter().next() else {
        return;
    };
    let def_block = lowering.dataflow.def_block(def_id);
    let def_instr = lowering.dataflow.def_instr(def_id);
    if def_block != block || !out.insert(def_id) {
        return;
    }

    let recoverable = if consumer_instr == lowering.cfg.blocks[block.index()].instrs.last().unwrap()
    {
        expr_for_fixed_def(lowering, def_id).is_some()
    } else {
        expr_for_dup_safe_fixed_def(lowering, def_id).is_some()
    };
    if !recoverable {
        out.remove(&def_id);
        return;
    }

    let effect = &lowering.dataflow.instr_effects[def_instr.index()];
    for used_reg in &effect.fixed_uses {
        collect_consumed_single_eval_defs(lowering, block, def_instr, *used_reg, out);
    }
}

fn branch_cond_regs(cond: crate::transformer::BranchCond) -> Vec<Reg> {
    match cond.operands {
        BranchOperands::Unary(operand) => cond_operand_reg(operand).into_iter().collect(),
        BranchOperands::Binary(lhs, rhs) => cond_operand_reg(lhs)
            .into_iter()
            .chain(cond_operand_reg(rhs))
            .collect(),
    }
}

fn cond_operand_reg(operand: CondOperand) -> Option<Reg> {
    match operand {
        CondOperand::Reg(reg) => Some(reg),
        CondOperand::Const(_)
        | CondOperand::Nil
        | CondOperand::Boolean(_)
        | CondOperand::Integer(_)
        | CondOperand::Number(_) => None,
    }
}
