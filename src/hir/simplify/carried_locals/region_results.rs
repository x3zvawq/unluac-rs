//! 结构化 region result 与既有状态 binding 的交棒收敛。
//!
//! StructurePlan 会为 branch/loop result 保留独立 SSA 身份。提升到 HIR 后，这类身份
//! 可能表现为 `local result; if ... result = state ... end`，或在每个 loop break 前把
//! carried state 复制到 result temp。只有所有能抵达后缀的路径都完整定义 result，
//! 并能证明同一 home slot，或证明动态 repeat 的匿名 result 在每个出口都只是 state 的
//! 精确副本时，result 才能安全复用原 local/param；reference capture、外部入口与独立状态
//! 写入都会阻止该折叠。By-value capture 由创建点的 reaching relation 验证；proto 级资源
//! 身份门还拒绝 TBC 和 reference-capture raw-home may-alias；
//! 与改写两端 possible-home 不相交的 cleanup 会原位保留，不会伪装成整个 region 的屏障；
//! self-contained goto/label 由 owner-wide lexical CFG 证明；跨 owner transfer 只在其
//! relation 会让目标观察错误 result/state epoch 时保留原形。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl, HirStmt, HirValuePack, LocalId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::local_shapes::{empty_single_local_decl_binding, initialized_single_local_decl};
use super::super::walk::rewrite_stmts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    bindings_share_exact_home_slot, carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::reads::{
    binding_is_mentioned_in_stmts, bindings_are_mentioned_in_exprs,
    bindings_are_mentioned_in_stmts, collect_binding_mentions_by_stmt,
    collect_binding_mentions_in_expr,
};
use super::{HandoffIdentityFacts, RegionControlFacts};
use crate::hir::visit::{HirVisitor, visit_stmts};

mod assignments;
mod binding_facts;
mod conditions;
mod flow;
mod parallel;
mod rewrites;

use assignments::*;
use binding_facts::*;
use conditions::*;
pub(super) use flow::collapse_result_writeback_transactions;
use flow::{
    ExternalTransferScope, expr_has_hard_barrier, region_has_hard_barrier,
    region_rewrites_preserve_external_transfers,
};
use parallel::*;
use rewrites::*;

// 当前块快照保留读写角色，私有性消费二者并集，loop live-out 消费首读/首写位置。
// 例如 `r = r + 1` 在同一位置读写，不能当作不观察旧 result 的覆盖；成功改写后重建索引。
pub(super) struct RegionResultIndex {
    reads: crate::graph::PositionIndex<CarryBinding>,
    writes: crate::graph::PositionIndex<CarryBinding>,
    local_declarations: BTreeMap<LocalId, usize>,
}

impl RegionResultIndex {
    pub(super) fn new(stmts: &[HirStmt]) -> RegionResultIndex {
        let mut reads = crate::graph::PositionIndex::default();
        let mut writes = crate::graph::PositionIndex::default();
        let mut local_declarations = BTreeMap::new();
        for (index, stmt) in stmts.iter().enumerate() {
            let facts = binding_facts(std::slice::from_ref(stmt));
            for binding in facts.reads {
                reads.record(binding, index);
            }
            for binding in facts.writes.into_keys() {
                writes.record(binding, index);
            }
            if let HirStmt::LocalDecl(local_decl) = stmt {
                for local in &local_decl.bindings {
                    local_declarations.entry(*local).or_insert(index);
                }
            }
        }
        Self {
            reads,
            writes,
            local_declarations,
        }
    }

    fn is_available_before(&self, binding: CarryBinding, index: usize) -> bool {
        match binding {
            CarryBinding::Param(_) => true,
            CarryBinding::Local(local) => self
                .local_declarations
                .get(&local)
                .is_some_and(|declaration| *declaration < index),
            CarryBinding::Temp(_) => false,
        }
    }

    fn is_private_after(&self, binding: CarryBinding, index: usize) -> bool {
        [&self.reads, &self.writes].into_iter().all(|positions| {
            positions
                .span(&binding)
                .is_none_or(|(_, last)| last <= index)
        })
    }
}

pub(super) fn collapse_inferred_if_result_chains(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    let result_index = RegionResultIndex::new(&block.stmts);
    let mut rewrites = BTreeMap::<CarryBinding, CarryBinding>::new();
    let mut removed_declarations = vec![false; block.stmts.len()];
    let mut seed_merge_groups = Vec::<Vec<LocalId>>::new();
    let mut cursor = 0;

    while cursor < block.stmts.len() {
        let declaration_start = cursor;
        let mut results = Vec::new();
        while let Some(result) = block
            .stmts
            .get(cursor)
            .and_then(empty_single_local_decl_binding)
        {
            results.push(CarryBinding::Local(result));
            cursor += 1;
        }
        if results.is_empty() {
            cursor += 1;
            continue;
        }
        let region_index = cursor;
        let candidate = (|| {
            let HirStmt::If(if_stmt) = block.stmts.get(region_index)? else {
                return None;
            };
            if region_has_hard_barrier(&block.stmts[region_index..=region_index], control_facts)
                || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
            {
                // 候选拒绝[SemanticBarrier:ControlFlow]：外部入口可绕过 tracked fallthrough
                // assignment；外跳 relation 在 rewrite map 形成后另行逐项验证。
                // 候选拒绝[SemanticBarrier:ValueFlow]：condition 读取空 result 时原值为 nil；
                // 改名后会读取 seed 的旧值并可能选择另一分支。
                // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
                return None;
            }
            let exits = if_fallthrough_assignments(if_stmt, &results)?;
            let inferred = infer_rewrites(
                &results,
                &exits,
                region_index,
                &result_index,
                promotion_facts,
                true,
            )?;
            (!inferred.iter().any(|(result, seed)| {
                outer_bindings.contains(result) || outer_bindings.contains(seed)
            }) && rewrites_preserve_identity(&inferred, promotion_facts, identity_facts)
                && rewrite_is_private_after(region_index, &inferred, &result_index)
                && region_rewrites_preserve_external_transfers(
                    &block.stmts[region_index..=region_index],
                    &inferred,
                    control_facts,
                    ExternalTransferScope::WholeRegion,
                ))
            // 候选拒绝[SemanticBarrier:Lifetime]：outer/reference-capture/identity 或 region
            // 后仍活跃的 seed/result 可观察合并前的独立 epoch/root。
            .then_some(inferred)
        })();
        let Some(inferred) = candidate else {
            cursor = declaration_start + 1;
            continue;
        };

        if inferred.len() > 1 {
            let seeds = inferred.values().copied().collect::<Vec<_>>();
            let local_seeds = seeds
                .iter()
                .map(|seed| match seed {
                    CarryBinding::Local(local) => Some(*local),
                    CarryBinding::Param(_) | CarryBinding::Temp(_) => None,
                })
                .collect::<Option<Vec<_>>>();
            if let Some(local_seeds) = local_seeds {
                let declaration_indices = local_seeds
                    .iter()
                    .map(|local| result_index.local_declarations.get(local).copied())
                    .collect::<Option<Vec<_>>>();
                if declaration_indices.is_some_and(|indices| {
                    indices.windows(2).all(|pair| pair[1] == pair[0] + 1)
                        && indices.last().is_some_and(|last| *last < declaration_start)
                        && indices.iter().zip(&local_seeds).all(|(index, local)| {
                            block
                                .stmts
                                .get(*index)
                                .and_then(initialized_single_local_decl)
                                .is_some_and(|(binding, _)| binding == *local)
                        })
                }) {
                    seed_merge_groups.push(local_seeds);
                }
            }
        }
        for result in inferred.keys().copied() {
            let CarryBinding::Local(local) = result else {
                continue;
            };
            let declaration = result_index
                .local_declarations
                .get(&local)
                .copied()
                .expect("inferred local result retains its planned declaration");
            assert!(
                (declaration_start..region_index).contains(&declaration),
                "inferred result declaration must belong to the current candidate group"
            );
            removed_declarations[declaration] = true;
        }
        for (result, seed) in inferred {
            let seed = canonical_binding(seed, &rewrites);
            rewrites.insert(result, seed);
        }
        cursor = region_index + 1;
    }

    if rewrites.is_empty() {
        return false;
    }
    let rewritten = rewrites.values().copied().collect::<BTreeSet<_>>();
    rewrite_stmts(
        &mut block.stmts,
        &mut BindingClassRewritePass {
            rewrites: rewrites.clone(),
            promotion_facts,
        },
    );
    rewrite_stmts(
        &mut block.stmts,
        &mut RedundantSelfAssignPrunePass::for_bindings(rewritten.iter().copied()),
    );
    let mut index = 0;
    block.stmts.retain(|_| {
        let keep = !removed_declarations[index];
        index += 1;
        keep
    });
    let mut declaration_index = BTreeMap::new();
    for (index, stmt) in block.stmts.iter().enumerate() {
        if let HirStmt::LocalDecl(local_decl) = stmt {
            for local in &local_decl.bindings {
                declaration_index.insert(*local, index);
            }
        }
    }
    let mut seed_merge_groups = seed_merge_groups
        .into_iter()
        .filter_map(|locals| {
            let start = declaration_index.get(locals.first()?).copied()?;
            locals
                .iter()
                .enumerate()
                .all(|(offset, local)| {
                    declaration_index.get(local).copied() == Some(start + offset)
                })
                .then_some((start, locals))
        })
        .collect::<Vec<_>>();
    seed_merge_groups.sort_by_key(|(start, _)| std::cmp::Reverse(*start));
    for (start, locals) in seed_merge_groups {
        merge_initialized_local_declarations(block, start, locals.len());
    }
    prune_empty_assign_stmts(block);
    true
}

fn canonical_binding(
    mut binding: CarryBinding,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
) -> CarryBinding {
    while let Some(next) = rewrites.get(&binding).copied() {
        binding = next;
    }
    binding
}

pub(super) fn collapse_written_back_if_results(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    let mentions = collect_binding_mentions_by_stmt(&block.stmts);
    let mut mention_counts = BTreeMap::<CarryBinding, usize>::new();
    for stmt_mentions in &mentions {
        for binding in stmt_mentions {
            *mention_counts.entry(*binding).or_default() += 1;
        }
    }

    let mut folds = Vec::new();
    let mut index = 0;
    while index + 2 < block.stmts.len() {
        let Some(result) =
            empty_single_local_decl_binding(&block.stmts[index]).map(CarryBinding::Local)
        else {
            index += 1;
            continue;
        };
        let Some(HirStmt::If(if_stmt)) = block.stmts.get(index + 1) else {
            index += 1;
            continue;
        };
        let Some(exits) = if_fallthrough_assignments(if_stmt, &[result]) else {
            index += 1;
            continue;
        };
        let Some(state) = exact_state_writeback(&block.stmts[index + 2], result) else {
            index += 1;
            continue;
        };
        if state == result {
            index += 1;
            continue;
        }
        let facts = binding_facts(std::slice::from_ref(&block.stmts[index + 1]));
        let state_writes_preserve_result = exits.iter().all(|exit| {
            !exit.contains_key(&state)
                && exit.get(&result).and_then(ExitValue::exact_binding) == Some(state)
        });
        if outer_bindings.contains(&result)
            || promotion_facts.compacts_home_slots()
            || !bindings_share_exact_home_slot(result, state, promotion_facts)
            || !identity_facts.binding_merge_preserves_identity(result, state, promotion_facts)
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：outer、异槽或资源 identity 可观察
            // result/state 合并前的独立 cell/root epoch。
            index += 1;
            continue;
        }
        if mention_counts.get(&result).copied() != Some(2)
            || facts.reads.contains(&result)
            || facts.writes.get(&result).copied() != Some(exits.len())
            || (facts.writes.contains_key(&state) && !state_writes_preserve_result)
        {
            // 候选拒绝[SemanticBarrier:ValueFlow]：额外 result mention、缺失 producer 或
            // 独立 state write 会让某条 exit 保留可区分的旧 epoch。
            index += 1;
            continue;
        }
        if region_has_hard_barrier(&block.stmts[index + 1..=index + 1], control_facts) {
            // 具体外部入口/Unresolved 原因由 owner-wide region proof 标注；外跳不 blanket 拒绝。
            index += 1;
            continue;
        }
        folds.push(WrittenBackIfResult {
            declaration: index,
            region: index + 1,
            writeback: index + 2,
            result,
            state,
            condition: match &if_stmt.cond {
                HirExpr::LocalRef(local) => Some(*local),
                _ => None,
            },
        });
        index += 3;
    }
    if folds.is_empty() {
        return false;
    }

    let mut removed = vec![false; block.stmts.len()];
    let mut condition_scratch = BTreeSet::new();
    for fold in folds {
        let mut rewrites = BTreeMap::new();
        rewrites.insert(fold.result, fold.state);
        rewrite_stmts(
            &mut block.stmts[fold.region..=fold.region],
            &mut BindingClassRewritePass {
                rewrites,
                promotion_facts,
            },
        );
        rewrite_stmts(
            &mut block.stmts[fold.region..=fold.region],
            &mut RedundantSelfAssignPrunePass::for_bindings([fold.state]),
        );
        removed[fold.declaration] = true;
        removed[fold.writeback] = true;
        if let Some(condition) = fold.condition {
            condition_scratch.insert(condition);
        }
    }
    let mut cursor = 0;
    block.stmts.retain(|_| {
        let keep = !removed[cursor];
        cursor += 1;
        keep
    });
    inline_owned_branch_conditions(block, &condition_scratch, outer_bindings, identity_facts);
    true
}

#[derive(Clone, Copy)]
struct WrittenBackIfResult {
    declaration: usize,
    region: usize,
    writeback: usize,
    result: CarryBinding,
    state: CarryBinding,
    condition: Option<LocalId>,
}

pub(super) fn try_collapse_region_result_handoff(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    result_index: &RegionResultIndex,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    try_collapse_seeded_if_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
        control_facts,
    ) || try_collapse_inferred_if_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
        control_facts,
    ) || try_collapse_loop_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
        control_facts,
    )
}

fn try_collapse_seeded_if_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    result_index: &RegionResultIndex,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    let mut cursor = index;
    let mut seeds = Vec::new();
    while let Some((seed, _)) = block
        .stmts
        .get(cursor)
        .and_then(initialized_single_local_decl)
    {
        seeds.push(seed);
        cursor += 1;
    }
    let result_start = cursor;
    let mut results = Vec::new();
    while let Some(result) = block
        .stmts
        .get(cursor)
        .and_then(empty_single_local_decl_binding)
    {
        results.push(CarryBinding::Local(result));
        cursor += 1;
    }
    if seeds.is_empty() || seeds.len() != results.len() {
        return false;
    }
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(cursor) else {
        return false;
    };
    if region_has_hard_barrier(&block.stmts[cursor..=cursor], control_facts)
        || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部入口可绕过 tracked assignment；
        // 外跳 relation 在 rewrite map 形成后另行逐项验证。
        // 候选拒绝[SemanticBarrier:ValueFlow]：condition 读取空 result 时，改名会把 nil
        // 换成 seed 旧值并可能选择另一分支。
        // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
        return false;
    }
    let Some(exits) = if_fallthrough_assignments(if_stmt, &results) else {
        return false;
    };
    let rewrites = results
        .iter()
        .copied()
        .zip(seeds.iter().copied().map(CarryBinding::Local))
        .collect::<BTreeMap<_, _>>();
    if !rewritten_results_keep_exit_values(&rewrites, &exits) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：seeded exit 在 result 后写 seed 时，改名后的最后写不再保留原 result 出口值；反最小见 seed_write_after_result_is_rejected。
        return false;
    }
    if !region_rewrites_preserve_external_transfers(
        &block.stmts[cursor..=cursor],
        &rewrites,
        control_facts,
        ExternalTransferScope::WholeRegion,
    ) {
        return false;
    }
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_home_slots(&rewrites, promotion_facts)
        || !rewrites_preserve_identity(&rewrites, promotion_facts, identity_facts)
        || !rewrite_is_private_after(cursor, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/reference-capture、异槽或资源
        // identity 会观察 seed/result 的独立生命周期。
        return false;
    }
    apply_rewrites(
        block,
        result_start..cursor,
        cursor,
        rewrites,
        promotion_facts,
    );
    merge_initialized_local_declarations(block, index, seeds.len());
    true
}

fn try_collapse_inferred_if_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    result_index: &RegionResultIndex,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    let mut cursor = index;
    let mut results = Vec::new();
    while let Some(result) = block
        .stmts
        .get(cursor)
        .and_then(empty_single_local_decl_binding)
    {
        results.push(CarryBinding::Local(result));
        cursor += 1;
    }
    if results.is_empty() {
        return false;
    }
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(cursor) else {
        return false;
    };
    if region_has_hard_barrier(&block.stmts[cursor..=cursor], control_facts)
        || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：外部入口可绕过 tracked assignment；
        // 外跳 relation 在 rewrite map 形成后另行逐项验证。
        // 候选拒绝[SemanticBarrier:ValueFlow]：condition 读取空 result 时，改名会把 nil
        // 换成 seed 旧值并可能选择另一分支。
        // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
        return false;
    }
    let Some(exits) = if_fallthrough_assignments(if_stmt, &results) else {
        return false;
    };
    let Some(rewrites) =
        infer_rewrites(&results, &exits, index, result_index, promotion_facts, true)
    else {
        return false;
    };
    if !region_rewrites_preserve_external_transfers(
        &block.stmts[cursor..=cursor],
        &rewrites,
        control_facts,
        ExternalTransferScope::WholeRegion,
    ) {
        return false;
    }
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_identity(&rewrites, promotion_facts, identity_facts)
        || !rewrite_is_private_after(cursor, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/reference-capture/identity
        // 不满足时，result 改名会影响 region 外或 closure 可见 epoch。
        return false;
    }
    let declarations = (index..cursor)
        .filter(|declaration| {
            block
                .stmts
                .get(*declaration)
                .and_then(empty_single_local_decl_binding)
                .is_some_and(|local| rewrites.contains_key(&CarryBinding::Local(local)))
        })
        .collect();
    let rewrite_end = block.stmts.len();
    apply_rewrites_with_declarations(
        block,
        declarations,
        cursor..rewrite_end,
        rewrites,
        promotion_facts,
    );
    true
}

fn try_collapse_loop_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    result_index: &RegionResultIndex,
    identity_facts: &HandoffIdentityFacts,
    control_facts: &RegionControlFacts,
) -> bool {
    let Some(stmt) = block.stmts.get(index) else {
        return false;
    };
    let (body, include_fallthrough, requires_exact_exits, condition_forbidden) = match stmt {
        HirStmt::While(while_stmt) if while_stmt.cond == HirExpr::Boolean(true) => {
            (&while_stmt.body, false, false, false)
        }
        HirStmt::Repeat(repeat_stmt) => (
            &repeat_stmt.body,
            repeat_stmt.cond != HirExpr::Boolean(false),
            repeat_stmt.cond != HirExpr::Boolean(true),
            expr_has_hard_barrier(&repeat_stmt.cond),
        ),
        _ => return false,
    };
    let mut exits = Vec::new();
    // 内层 loop 的 break/continue 归内层 owner；goto/label 的入口由 owner-wide lexical
    // CFG 验证，外跳 relation 在 rewrite map 形成后逐项检查。Unresolved 不并入普通 exit
    // plan；cleanup 别名风险由后面的 proto 身份门按 possible-home 精确处理。
    if condition_forbidden
        || region_has_hard_barrier(&body.stmts, control_facts)
        || !collect_break_assignments(body, &mut exits, requires_exact_exits)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：未跟踪 transfer 会漏掉 loop 出口，提交不完整 result->state 映射。
        // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据，
        // region-result 不把未知路径并入普通 state 映射。
        return false;
    }
    let has_fallthrough_exit = include_fallthrough && block_may_fall_through(body);
    if has_fallthrough_exit {
        let Some(HirStmt::Assign(assign)) = body.stmts.last() else {
            return false;
        };
        exits.push(assignment_values(assign));
    }
    if exits.is_empty() {
        // 无 tracked break，且 while true/repeat false 没有 fallthrough；region 后缀不可达，
        // 因而这里没有可提交的 live-out result candidate。
        return false;
    }
    let mut results = exits
        .first()
        .into_iter()
        .flat_map(|exit| exit.keys().copied())
        .filter(|binding| matches!(binding, CarryBinding::Temp(_)))
        .collect::<BTreeSet<_>>();
    for exit in &exits[1..] {
        results.retain(|result| exit.contains_key(result));
    }
    let mut rewrite_ends = BTreeMap::new();
    let mut has_path_dependent_live_out = false;
    results.retain(
        |result| match loop_result_rewrite_end(block, index, *result, result_index) {
            LoopResultRewriteBoundary::Exact(rewrite_end) => {
                rewrite_ends.insert(*result, rewrite_end);
                true
            }
            LoopResultRewriteBoundary::PathDependent => {
                has_path_dependent_live_out = true;
                false
            }
            LoopResultRewriteBoundary::NoLiveOut => false,
        },
    );
    if results.is_empty() {
        if has_path_dependent_live_out {
            // 候选拒绝[SemanticBarrier:ControlFlow]：首个 result 覆盖是路径相关的结构化写，
            // 未写分支仍会让后续读取观察 loop 产生的旧 result epoch。
        }
        return false;
    }
    let rewrite_end = *rewrite_ends
        .get(results.first().expect("non-empty result set"))
        .expect("every retained result has a rewrite boundary");
    results.retain(|result| rewrite_ends.get(result) == Some(&rewrite_end));

    let loop_facts = binding_facts(std::slice::from_ref(stmt));
    results.retain(|result| !loop_facts.reads.contains(result));
    if results.is_empty() {
        // 候选拒绝[SemanticBarrier:Lifetime]：loop 内读 result 会观察它在本次/上次迭代的独立 epoch，改名为 seed 会切换该读取。
        return false;
    }
    let require_home_slot = !requires_exact_exits;
    let results = results.into_iter().collect::<Vec<_>>();
    let Some(rewrites) = infer_rewrites(
        &results,
        &exits,
        index,
        result_index,
        promotion_facts,
        require_home_slot,
    ) else {
        return false;
    };
    if !region_rewrites_preserve_external_transfers(
        &body.stmts,
        &rewrites,
        control_facts,
        ExternalTransferScope::LoopExitPlan,
    ) {
        return false;
    }
    // 动态 repeat 的 synthetic result 没有稳定 home slot；只有每条出口都是 state 的
    // 精确快照且不在同一赋值中改写 state，才能把这个跨槽身份安全消掉。
    if requires_exact_exits
        && !rewrites.iter().all(|(result, seed)| {
            exits.iter().all(|exit| {
                !exit.contains_key(seed)
                    && exit.get(result).and_then(ExitValue::exact_binding) == Some(*seed)
            })
        })
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：动态 repeat 某出口不是 state 精确快照或同时写 state 时，改名会改变该出口 live-out。
        return false;
    }
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_identity(&rewrites, promotion_facts, identity_facts)
        || !rewrite_is_private_after(index, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/reference-capture/identity
        // 不满足时，loop 外或 closure 可观察独立 result/state epoch。
        return false;
    }
    let can_rewrite_every_occurrence = rewrite_end == block.stmts.len()
        && rewrites.iter().all(|(result, seed)| {
            !loop_facts.writes.contains_key(seed)
                && result_writes_are_standalone_seed_copies(
                    &body.stmts,
                    *result,
                    *seed,
                    loop_facts.writes.get(result).copied().unwrap_or(0),
                )
        });
    if can_rewrite_every_occurrence {
        apply_rewrites_in_range(
            block,
            index..index,
            index..rewrite_end,
            rewrites,
            promotion_facts,
        );
    } else {
        // 非出口 result 写保留为独立旧 epoch；只改 tracked exit producer 与其 live-out reads，
        // 避免把中间值误写到 seed，且保留它在 seed overwrite/GC 之间的 root 生命周期。
        apply_loop_result_rewrites(
            block,
            index,
            rewrite_end,
            rewrites,
            promotion_facts,
            has_fallthrough_exit,
        );
    }
    true
}

enum LoopResultRewriteBoundary {
    Exact(usize),
    PathDependent,
    NoLiveOut,
}

fn loop_result_rewrite_end(
    block: &HirBlock,
    loop_index: usize,
    result: CarryBinding,
    result_index: &RegionResultIndex,
) -> LoopResultRewriteBoundary {
    let start = loop_index + 1;
    let Some(&read) = result_index.reads.positions_from(&result, start).first() else {
        return LoopResultRewriteBoundary::NoLiveOut;
    };
    let Some(&write) = result_index.writes.positions_from(&result, start).first() else {
        return LoopResultRewriteBoundary::Exact(block.stmts.len());
    };
    // Assign 没有嵌套语句，表达式遍历也不进入子 proto；其中被记录的 binding 写入
    // 必为直接 target。同语句 RHS 先读旧值，因此 read == write 仍须保留 live-out。
    if !matches!(block.stmts[write], HirStmt::Assign(_)) {
        LoopResultRewriteBoundary::PathDependent
    } else if read <= write {
        LoopResultRewriteBoundary::Exact(write)
    } else {
        LoopResultRewriteBoundary::NoLiveOut
    }
}

fn rewrites_preserve_identity(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    rewrites.iter().all(|(source, target)| {
        identity_facts.binding_merge_preserves_identity(*source, *target, promotion_facts)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{
        HirCallExpr, HirCallStmt, HirClose, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef,
        HirDecisionTarget, HirGlobalRef, HirGoto, HirLabel, HirLabelId, HirRepeat, HirReturn,
        HirToBeClosed, HirWhile, ParamId, TempId,
    };
    use crate::hir::expr_safety::HirExprSafety;
    use crate::hir::promotion::HomeSlotKey;
    use crate::transformer::InstrRef;

    fn empty_identity_facts() -> HandoffIdentityFacts {
        HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
            preserved: BTreeSet::new(),
        }
    }

    fn control_facts(stmts: &[HirStmt]) -> RegionControlFacts {
        RegionControlFacts {
            label_refs: crate::hir::simplify::label_refs::count_label_references(stmts),
            expr_safety: HirExprSafety::for_dialect(DecompileDialect::Lua54),
        }
    }

    fn empty_control_facts() -> RegionControlFacts {
        control_facts(&[])
    }

    fn decision(test: HirExpr) -> HirExpr {
        HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test,
                truthy: HirDecisionTarget::CurrentValue,
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        }))
    }

    fn single_fallthrough_result_block(terminating_value: HirExpr) -> HirBlock {
        HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(LocalId(0))],
                            values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                            initializer_merge_transaction: None,
                            generic_for_initializer_producer: None,
                            method_rewrite_transaction: None,
                        }))],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Return(Box::new(HirReturn {
                            source_instr: None,
                            values: HirValuePack::fixed(vec![terminating_value]),
                        }))],
                    }),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Param(ParamId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
                    initializer_merge_transaction: None,
                    generic_for_initializer_producer: None,
                    method_rewrite_transaction: None,
                })),
            ],
        }
    }

    fn same_home_facts() -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        facts
    }

    fn seeded_if_without_copy_block() -> HirBlock {
        let branch = |value| HirBlock {
            stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(1))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(value)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))],
        };
        HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(1)),
                    then_block: branch(1),
                    else_block: Some(branch(2)),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    source_instr: None,
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(1))]),
                })),
            ],
        }
    }

    fn seeded_if_facts(result_home: HomeSlotKey) -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        facts.record_local_home_slot(LocalId(0), HomeSlotKey::new(0, 0));
        facts.record_local_home_slot(LocalId(1), result_home);
        facts
    }

    fn inferred_if_with_distinct_shared_seed_values() -> HirBlock {
        let assignment = |first, second| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Local(LocalId(0)), HirLValue::Local(LocalId(1))],
                values: HirValuePack::fixed(vec![first, second]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::default(),
                    initializer_merge_transaction: None,
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(1)),
                    then_block: HirBlock {
                        stmts: vec![assignment(
                            HirExpr::ParamRef(ParamId(0)),
                            HirExpr::ParamRef(ParamId(0)),
                        )],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![assignment(HirExpr::Integer(1), HirExpr::Integer(2))],
                    }),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    source_instr: None,
                    values: HirValuePack::fixed(vec![
                        HirExpr::LocalRef(LocalId(0)),
                        HirExpr::LocalRef(LocalId(1)),
                    ]),
                })),
            ],
        }
    }

    fn loop_result_block(extra_value: HirExpr) -> HirBlock {
        let result_copy = |value| {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![value]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        HirBlock {
            stmts: vec![
                HirStmt::While(Box::new(HirWhile {
                    cond: HirExpr::Boolean(true),
                    body: HirBlock {
                        stmts: vec![
                            result_copy(extra_value),
                            result_copy(HirExpr::ParamRef(ParamId(0))),
                            HirStmt::Break,
                        ],
                    },
                })),
                HirStmt::Return(Box::new(HirReturn {
                    source_instr: None,
                    values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                })),
            ],
        }
    }

    fn loop_result_facts() -> ProtoPromotionFacts {
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(TempId(0), HomeSlotKey::new(0, 0));
        facts
    }

    fn dynamic_loop_result_with_seed_overwrite() -> HirBlock {
        let result_copy = || {
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![HirExpr::ParamRef(ParamId(0))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            }))
        };
        HirBlock {
            stmts: vec![
                HirStmt::Repeat(Box::new(HirRepeat {
                    body: HirBlock {
                        stmts: vec![
                            result_copy(),
                            HirStmt::Assign(Box::new(HirAssign {
                                targets: vec![HirLValue::Param(ParamId(0))],
                                values: HirValuePack::fixed(vec![HirExpr::Nil]),
                                initializer_merge_transaction: None,
                                generic_for_initializer_producer: None,
                                method_rewrite_transaction: None,
                            })),
                            HirStmt::CallStmt(Box::new(HirCallStmt {
                                call: HirCallExpr {
                                    argument_roots: Vec::new(),
                                    callee: HirExpr::GlobalRef(HirGlobalRef {
                                        key: "collectgarbage".into(),
                                    }),
                                    args: HirValuePack::default(),
                                    method: false,
                                    fastcall: None,
                                    method_key: None,
                                    callee_root_handoff: None,
                                    method_rewrite_transaction: None,
                                },
                            })),
                            result_copy(),
                            HirStmt::Break,
                        ],
                    },
                    cond: HirExpr::TempRef(TempId(1)),
                    lifetime: Default::default(),
                })),
                HirStmt::Return(Box::new(HirReturn {
                    source_instr: None,
                    values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                })),
            ],
        }
    }

    #[test]
    fn written_back_if_accepts_one_fallthrough_result_exit() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let mut facts = same_home_facts();
        let identity_facts = empty_identity_facts();

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &identity_facts,
            &empty_control_facts(),
        ));

        let [HirStmt::If(if_stmt)] = block.stmts.as_slice() else {
            panic!("result declaration and terminal writeback should be removed");
        };
        let [HirStmt::Assign(assign)] = if_stmt.then_block.stmts.as_slice() else {
            panic!("the fallthrough arm should retain its producer assignment");
        };
        assert!(assign.targets == vec![HirLValue::Param(ParamId(0))]);
    }

    #[test]
    fn written_back_if_accepts_a_temp_state_owner() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let HirStmt::Assign(writeback) = &mut block.stmts[2] else {
            unreachable!()
        };
        writeback.targets = vec![HirLValue::Temp(TempId(1))];
        let mut facts = same_home_facts();
        facts.record_temp_home_slot_for_test(TempId(1), HomeSlotKey::new(0, 0));

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        let [HirStmt::If(if_stmt)] = block.stmts.as_slice() else {
            panic!("result declaration and terminal writeback should be removed");
        };
        let [HirStmt::Assign(assign)] = if_stmt.then_block.stmts.as_slice() else {
            panic!("the fallthrough arm should write the existing temp state");
        };
        assert!(assign.targets == vec![HirLValue::Temp(TempId(1))]);
    }

    #[test]
    fn written_back_if_accepts_disjoint_decision_condition() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let HirStmt::If(if_stmt) = &mut block.stmts[1] else {
            unreachable!()
        };
        if_stmt.cond = decision(HirExpr::TempRef(TempId(1)));
        let mut facts = same_home_facts();

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        assert!(matches!(block.stmts.as_slice(), [HirStmt::If(_)]));
    }

    #[test]
    fn written_back_if_accepts_self_contained_label_flow() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let label = HirLabelId(0);
        let HirStmt::If(if_stmt) = &mut block.stmts[1] else {
            unreachable!()
        };
        if_stmt
            .then_block
            .stmts
            .insert(0, HirStmt::Goto(Box::new(HirGoto { target: label })));
        if_stmt.then_block.stmts.insert(
            1,
            HirStmt::Label(Box::new(HirLabel {
                entry_cleanup: Vec::new(),
                id: label,
                tbc_barriers: Default::default(),
            })),
        );
        let control = control_facts(&block.stmts);
        let mut facts = same_home_facts();

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &control,
        ));

        let [HirStmt::If(if_stmt)] = block.stmts.as_slice() else {
            panic!("only the mechanical declaration and writeback should disappear");
        };
        assert!(matches!(if_stmt.then_block.stmts[0], HirStmt::Goto(_)));
        assert!(matches!(if_stmt.then_block.stmts[1], HirStmt::Label(_)));
    }

    #[test]
    fn written_back_if_accepts_an_unproduced_goto_outside_the_region() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let label = HirLabelId(0);
        let HirStmt::If(if_stmt) = &mut block.stmts[1] else {
            unreachable!()
        };
        if_stmt
            .then_block
            .stmts
            .insert(0, HirStmt::Goto(Box::new(HirGoto { target: label })));
        block.stmts.push(HirStmt::Label(Box::new(HirLabel {
            entry_cleanup: Vec::new(),
            id: label,
            tbc_barriers: Default::default(),
        })));
        let control = control_facts(&block.stmts);
        let mut facts = same_home_facts();

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &control,
        ));
        assert!(matches!(block.stmts.last(), Some(HirStmt::Label(_))));
    }

    #[test]
    fn written_back_if_keeps_disjoint_cleanup_inside_region() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        block.stmts.insert(
            0,
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Nil]),
                initializer_merge_transaction: None,
            })),
        );
        let HirStmt::If(if_stmt) = &mut block.stmts[2] else {
            unreachable!()
        };
        if_stmt.then_block.stmts.insert(
            0,
            HirStmt::ToBeClosed(Box::new(HirToBeClosed {
                origin: InstrRef(0),
                reg_index: 9,
                value: HirExpr::LocalRef(LocalId(2)),
            })),
        );
        if_stmt.then_block.stmts.insert(
            1,
            HirStmt::Close(Box::new(HirClose {
                kind: crate::transformer::CloseKind::Explicit,
                from_reg: 9,
                origins: Vec::new(),
            })),
        );
        let mut facts = same_home_facts();
        facts.record_local_home_slot(LocalId(2), HomeSlotKey::new(9, 0));
        let mut identity = empty_identity_facts();
        identity
            .to_be_closed
            .insert(CarryBinding::Local(LocalId(2)));

        assert!(collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &identity,
            &empty_control_facts(),
        ));

        let [HirStmt::LocalDecl(_), HirStmt::If(if_stmt)] = block.stmts.as_slice() else {
            panic!("only the mechanical result declaration and writeback should disappear");
        };
        assert!(matches!(
            if_stmt.then_block.stmts.as_slice(),
            [
                HirStmt::ToBeClosed(_),
                HirStmt::Close(_),
                HirStmt::Assign(_)
            ]
        ));
    }

    #[test]
    fn written_back_if_rejects_decision_condition_reading_empty_result() {
        let mut block = single_fallthrough_result_block(HirExpr::Integer(9));
        let HirStmt::If(if_stmt) = &mut block.stmts[1] else {
            unreachable!()
        };
        if_stmt.cond = decision(HirExpr::LocalRef(LocalId(0)));
        let original = block.clone();
        let mut facts = same_home_facts();

        assert!(!collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        assert!(block == original);
    }

    #[test]
    fn written_back_if_rejects_terminating_arm_reading_unproduced_result() {
        let mut block = single_fallthrough_result_block(HirExpr::LocalRef(LocalId(0)));
        let original = block.clone();
        let mut facts = same_home_facts();
        let identity_facts = empty_identity_facts();

        assert!(!collapse_written_back_if_results(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &identity_facts,
            &empty_control_facts(),
        ));
        assert!(block == original);
    }

    #[test]
    fn seeded_if_accepts_complete_paths_without_exact_seed_copy() {
        let mut block = seeded_if_without_copy_block();
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = seeded_if_facts(HomeSlotKey::new(0, 0));

        assert!(try_collapse_seeded_if_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        assert!(!binding_is_mentioned_in_stmts(
            &block.stmts,
            CarryBinding::Local(LocalId(1)),
        ));
    }

    #[test]
    fn seeded_if_without_copy_rejects_distinct_home_slots() {
        let mut block = seeded_if_without_copy_block();
        let original = block.clone();
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = seeded_if_facts(HomeSlotKey::new(1, 0));

        assert!(!try_collapse_seeded_if_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        assert!(block == original);
    }

    #[test]
    fn selective_if_rewrite_keeps_unmerged_result_declaration() {
        let mut block = inferred_if_with_distinct_shared_seed_values();
        let mut facts = ProtoPromotionFacts::default();
        let rewrite_end = block.stmts.len();

        apply_rewrites_with_declarations(
            &mut block,
            vec![0],
            2..rewrite_end,
            BTreeMap::from([(
                CarryBinding::Local(LocalId(0)),
                CarryBinding::Param(ParamId(0)),
            )]),
            &mut facts,
        );

        assert!(!binding_is_mentioned_in_stmts(
            &block.stmts,
            CarryBinding::Local(LocalId(0)),
        ));
        assert!(binding_is_mentioned_in_stmts(
            &block.stmts,
            CarryBinding::Local(LocalId(1)),
        ));
    }

    #[test]
    fn inferred_chain_keeps_each_unmerged_result_declaration() {
        let mut block = inferred_if_with_distinct_shared_seed_values();
        block.stmts.insert(
            0,
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![LocalId(2)],
                values: HirValuePack::fixed(vec![HirExpr::Integer(0)]),
                initializer_merge_transaction: None,
            })),
        );
        let HirStmt::If(if_stmt) = &mut block.stmts[3] else {
            unreachable!()
        };
        let HirStmt::Assign(assign) = &mut if_stmt.then_block.stmts[0] else {
            unreachable!()
        };
        assign.values = HirValuePack::fixed(vec![
            HirExpr::LocalRef(LocalId(2)),
            HirExpr::LocalRef(LocalId(2)),
        ]);
        let mut facts = ProtoPromotionFacts::default();
        for local in [LocalId(0), LocalId(1), LocalId(2)] {
            facts.record_local_home_slot(local, HomeSlotKey::new(0, 0));
        }

        assert!(collapse_inferred_if_result_chains(
            &mut block,
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        assert!(!binding_is_mentioned_in_stmts(
            &block.stmts,
            CarryBinding::Local(LocalId(0)),
        ));
        assert!(block.stmts.iter().any(|stmt| {
            empty_single_local_decl_binding(stmt).is_some_and(|local| local == LocalId(1))
        }));
        assert!(binding_is_mentioned_in_stmts(
            &block.stmts,
            CarryBinding::Local(LocalId(1)),
        ));
    }

    #[test]
    fn loop_result_accepts_redundant_standalone_seed_copy() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        let [HirStmt::While(while_stmt), HirStmt::Return(return_stmt)] = block.stmts.as_slice()
        else {
            panic!("the loop result should be rewritten without changing control flow");
        };
        assert!(while_stmt.body.stmts == vec![HirStmt::Break]);
        assert!(
            return_stmt.values.fixed == vec![HirExpr::ParamRef(ParamId(0))]
                && return_stmt.values.tail.is_none()
        );
    }

    #[test]
    fn loop_result_preserves_non_exit_write_as_an_unobserved_old_epoch() {
        let mut block = loop_result_block(HirExpr::Integer(7));
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        let [HirStmt::While(while_stmt), HirStmt::Return(return_stmt)] = block.stmts.as_slice()
        else {
            panic!("targeted rewrite preserves only the non-exit old-epoch write");
        };
        assert!(while_stmt.body.stmts.len() == 2);
        assert!(matches!(while_stmt.body.stmts[0], HirStmt::Assign(_)));
        assert!(matches!(while_stmt.body.stmts[1], HirStmt::Break));
        assert!(return_stmt.values.fixed == vec![HirExpr::ParamRef(ParamId(0))]);
    }

    #[test]
    fn loop_result_preserves_root_copy_across_seed_overwrite() {
        let mut block = dynamic_loop_result_with_seed_overwrite();
        let index = RegionResultIndex::new(&block.stmts);

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut ProtoPromotionFacts::default(),
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        let [HirStmt::Repeat(repeat_stmt), HirStmt::Return(return_stmt)] = block.stmts.as_slice()
        else {
            panic!("targeted rewrite keeps the pre-overwrite root transaction");
        };
        assert!(matches!(repeat_stmt.body.stmts[0], HirStmt::Assign(_)));
        assert!(
            repeat_stmt
                .body
                .stmts
                .iter()
                .any(|stmt| matches!(stmt, HirStmt::CallStmt(_)))
        );
        assert!(matches!(
            repeat_stmt.body.stmts.last(),
            Some(HirStmt::Break)
        ));
        assert!(return_stmt.values.fixed == vec![HirExpr::ParamRef(ParamId(0))]);
    }

    #[test]
    fn loop_result_keeps_prior_temp_epoch_outside_rewrite_range() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        block.stmts.insert(
            0,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(99)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            1,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        let HirStmt::Assign(prefix) = &block.stmts[0] else {
            panic!("the prior temp epoch must remain outside the rewrite range");
        };
        assert!(prefix.targets == vec![HirLValue::Temp(TempId(0))]);
    }

    #[test]
    fn loop_result_stops_at_clean_suffix_redefinition() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        block.stmts.insert(
            1,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Param(ParamId(1))],
                values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        block.stmts.insert(
            2,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));

        let HirStmt::Assign(read) = &block.stmts[1] else {
            panic!("the live-out read must remain");
        };
        assert!(read.values.fixed == vec![HirExpr::ParamRef(ParamId(0))]);
        let HirStmt::Assign(overwrite) = &block.stmts[2] else {
            panic!("the next temp epoch must remain");
        };
        assert!(overwrite.targets == vec![HirLValue::Temp(TempId(0))]);
        let HirStmt::Return(return_stmt) = &block.stmts[3] else {
            panic!("the next temp epoch remains observable");
        };
        assert!(return_stmt.values.fixed == vec![HirExpr::TempRef(TempId(0))]);
    }

    #[test]
    fn loop_result_rewrites_reads_in_parallel_suffix_epoch_boundary() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        block.stmts[1] = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![HirLValue::Param(ParamId(1)), HirLValue::Temp(TempId(0))],
            values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0)), HirExpr::Integer(7)]),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
            method_rewrite_transaction: None,
        }));
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        let HirStmt::Assign(boundary) = &block.stmts[1] else {
            panic!("parallel boundary remains an assignment");
        };
        assert!(boundary.targets[1] == HirLValue::Temp(TempId(0)));
        assert!(boundary.values.fixed[0] == HirExpr::ParamRef(ParamId(0)));
    }

    #[test]
    fn loop_result_rejects_path_dependent_suffix_redefinition() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        block.stmts.insert(
            1,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Param(ParamId(1))],
                values: HirValuePack::fixed(vec![HirExpr::TempRef(TempId(0))]),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                method_rewrite_transaction: None,
            })),
        );
        block.stmts.insert(
            2,
            HirStmt::If(Box::new(HirIf {
                cond: HirExpr::TempRef(TempId(1)),
                then_block: HirBlock {
                    stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![HirLValue::Temp(TempId(0))],
                        values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                        initializer_merge_transaction: None,
                        generic_for_initializer_producer: None,
                        method_rewrite_transaction: None,
                    }))],
                },
                else_block: None,
            })),
        );
        let original = block.clone();
        let index = RegionResultIndex::new(&block.stmts);
        let mut facts = loop_result_facts();

        assert!(!try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
            &empty_control_facts(),
        ));
        assert!(block == original);
    }
}
