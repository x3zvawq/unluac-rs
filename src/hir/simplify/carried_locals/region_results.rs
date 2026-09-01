//! 结构化 region result 与既有状态 binding 的交棒收敛。
//!
//! StructurePlan 会为 branch/loop result 保留独立 SSA 身份。提升到 HIR 后，这类身份
//! 可能表现为 `local result; if ... result = state ... end`，或在每个 loop break 前把
//! carried state 复制到 result temp。只有所有能抵达后缀的路径都完整定义 result，
//! 并能证明同一 home slot，或证明动态 repeat 的匿名 result 在每个出口都只是 state 的
//! 精确副本时，result 才能安全复用原 local/param；capture、跨 label 与独立状态写入都会
//! 阻止该折叠。proto 级资源身份门还拒绝 TBC 和 reference-capture raw-home may-alias；
//! continue/goto 的条件路径不由这个 pass 猜测。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl, HirStmt, HirValuePack, LocalId,
};
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::rewrite_stmts;
use super::HandoffIdentityFacts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, binding_home_slot,
    bindings_share_exact_home_slot, carry_binding_from_expr, carry_binding_from_lvalue,
};
use super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};

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
use flow::{expr_has_hard_barrier, region_has_hard_barrier};
use parallel::*;
use rewrites::*;

pub(super) struct RegionResultIndex<'a> {
    mentions: BTreeMap<CarryBinding, Vec<usize>>,
    local_declarations: BTreeMap<LocalId, usize>,
    captured: &'a BTreeSet<CarryBinding>,
}

impl<'a> RegionResultIndex<'a> {
    pub(super) fn new(
        stmts: &[HirStmt],
        captured: &'a BTreeSet<CarryBinding>,
    ) -> RegionResultIndex<'a> {
        let mut mentions = BTreeMap::<CarryBinding, Vec<usize>>::new();
        for (index, bindings) in collect_binding_mentions_by_stmt(stmts)
            .into_iter()
            .enumerate()
        {
            for binding in bindings {
                mentions.entry(binding).or_default().push(index);
            }
        }
        let mut local_declarations = BTreeMap::new();
        for (index, stmt) in stmts.iter().enumerate() {
            if let HirStmt::LocalDecl(local_decl) = stmt {
                for local in &local_decl.bindings {
                    local_declarations.entry(*local).or_insert(index);
                }
            }
        }
        Self {
            mentions,
            local_declarations,
            captured,
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
        !self.captured.contains(&binding)
            && self.mentions.get(&binding).is_none_or(|mentions| {
                mentions.partition_point(|mention| *mention <= index) == mentions.len()
            })
    }
}

pub(super) fn collapse_inferred_if_result_chains(
    block: &mut HirBlock,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    captured_bindings: &BTreeSet<CarryBinding>,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let result_index = RegionResultIndex::new(&block.stmts, captured_bindings);
    let mut rewrites = BTreeMap::<CarryBinding, CarryBinding>::new();
    let mut removed_declarations = vec![false; block.stmts.len()];
    let mut seed_merge_groups = Vec::<Vec<LocalId>>::new();
    let mut cursor = 0;

    while cursor < block.stmts.len() {
        let declaration_start = cursor;
        let mut results = Vec::new();
        while let Some(result) = block.stmts.get(cursor).and_then(empty_local) {
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
            if region_has_hard_barrier(&block.stmts[region_index..=region_index])
                || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
            {
                // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可绕过 tracked fallthrough
                // assignment，使改名后的 seed 在未产出 result 的路径上保持旧值。
                // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 跨 result producer 会改变
                // resource 所属 cell 的 close/root epoch。
                // 候选拒绝[SemanticBarrier:ValueFlow]：condition 读取空 result 时原值为 nil；
                // 改名后会读取 seed 的旧值并可能选择另一分支。
                // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
                return None;
            }
            let exits = if_fallthrough_assignments(if_stmt, &results)?;
            let inferred = infer_rewrites(
                &results,
                &exits,
                declaration_start,
                &result_index,
                promotion_facts,
                true,
            )?;
            (!inferred.iter().any(|(result, seed)| {
                outer_bindings.contains(result) || outer_bindings.contains(seed)
            }) && rewrites_preserve_identity(&inferred, promotion_facts, identity_facts)
                && rewrite_is_private_and_uncaptured(region_index, &inferred, &result_index))
            // 候选拒绝[SemanticBarrier:Lifetime]：outer/capture/identity 或 region 后仍活跃的 seed/result 可观察合并前的独立 epoch/root。
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
                                .and_then(initialized_local)
                                .is_some_and(|(binding, _)| binding == *local)
                        })
                }) {
                    seed_merge_groups.push(local_seeds);
                }
            }
        }
        for (result, seed) in inferred {
            let seed = canonical_binding(seed, &rewrites);
            rewrites.insert(result, seed);
        }
        removed_declarations[declaration_start..region_index].fill(true);
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
    captured_bindings: &BTreeSet<CarryBinding>,
    promotion_facts: &mut ProtoPromotionFacts,
    identity_facts: &HandoffIdentityFacts,
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
        let Some(result) = empty_local(&block.stmts[index]).map(CarryBinding::Local) else {
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
        let facts = binding_facts(std::slice::from_ref(&block.stmts[index + 1]));
        let state_writes_preserve_result = exits.iter().all(|exit| {
            !exit.contains_key(&state)
                && exit.get(&result).and_then(ExitValue::exact_binding) == Some(state)
        });
        if !matches!(state, CarryBinding::Param(_) | CarryBinding::Local(_))
            || state == result
            || outer_bindings.contains(&result)
            || captured_bindings.contains(&result)
            || captured_bindings.contains(&state)
            || promotion_facts.compacts_home_slots()
            || !bindings_share_exact_home_slot(result, state, promotion_facts)
            || !identity_facts.binding_merge_preserves_identity(result, state, promotion_facts)
            || mention_counts.get(&result).copied() != Some(2)
            || facts.reads.contains_key(&result)
            || facts.writes.get(&result).copied() != Some(exits.len())
            || (facts.writes.contains_key(&state) && !state_writes_preserve_result)
            || region_has_hard_barrier(&block.stmts[index + 1..=index + 1])
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：capture/outer use、异槽、额外 result mention 或 state 被独立写入时，改名会合并可区分 epoch。
            // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可绕过 tracked result write。
            // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 跨 result producer 会改变 close/root epoch。
            // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据。
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
    inline_owned_branch_conditions(
        block,
        &condition_scratch,
        outer_bindings,
        captured_bindings,
        identity_facts,
    );
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
    result_index: &RegionResultIndex<'_>,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    try_collapse_seeded_if_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
    ) || try_collapse_inferred_if_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
    ) || try_collapse_loop_results(
        block,
        index,
        outer_bindings,
        promotion_facts,
        result_index,
        identity_facts,
    )
}

fn try_collapse_seeded_if_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &mut ProtoPromotionFacts,
    result_index: &RegionResultIndex<'_>,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let mut cursor = index;
    let mut seeds = Vec::new();
    while let Some((seed, _)) = block.stmts.get(cursor).and_then(initialized_local) {
        seeds.push(seed);
        cursor += 1;
    }
    let result_start = cursor;
    let mut results = Vec::new();
    while let Some(result) = block.stmts.get(cursor).and_then(empty_local) {
        results.push(CarryBinding::Local(result));
        cursor += 1;
    }
    if seeds.is_empty() || seeds.len() != results.len() {
        return false;
    }
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(cursor) else {
        return false;
    };
    if region_has_hard_barrier(&block.stmts[cursor..=cursor])
        || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可绕过某条 tracked exit assignment。
        // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 跨 result producer 会改变 close/root epoch。
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
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_home_slots(&rewrites, promotion_facts)
        || !rewrites_preserve_identity(&rewrites, promotion_facts, identity_facts)
        || !rewrite_is_private_and_uncaptured(cursor, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/capture/异槽或资源 identity 会观察 seed/result 的独立生命周期。
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
    result_index: &RegionResultIndex<'_>,
    identity_facts: &HandoffIdentityFacts,
) -> bool {
    let mut cursor = index;
    let mut results = Vec::new();
    while let Some(result) = block.stmts.get(cursor).and_then(empty_local) {
        results.push(CarryBinding::Local(result));
        cursor += 1;
    }
    if results.is_empty() {
        return false;
    }
    let Some(HirStmt::If(if_stmt)) = block.stmts.get(cursor) else {
        return false;
    };
    if region_has_hard_barrier(&block.stmts[cursor..=cursor])
        || bindings_are_mentioned_in_exprs(std::iter::once(&if_stmt.cond), &results)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：goto/label 可绕过某条 tracked exit assignment。
        // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 跨 result producer 会改变 close/root epoch。
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
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_identity(&rewrites, promotion_facts, identity_facts)
        || !rewrite_is_private_and_uncaptured(cursor, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/capture/identity 不满足时，result 改名会影响 region 外或 closure 可见 epoch。
        return false;
    }
    let declarations = (index..cursor)
        .filter(|declaration| {
            block
                .stmts
                .get(*declaration)
                .and_then(empty_local)
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
    result_index: &RegionResultIndex<'_>,
    identity_facts: &HandoffIdentityFacts,
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
    // 内层 loop 的 break/continue 归内层 owner，但跳转、cleanup 或 Unresolved 可能
    // 绕过/隐藏 result 写回；这类边界不能交给 `collect_break_assignments` 猜测。
    if condition_forbidden
        || region_has_hard_barrier(&body.stmts)
        || !collect_break_assignments(body, &mut exits, requires_exact_exits)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：未跟踪 transfer 会漏掉 loop 出口，提交不完整 result->state 映射。
        // 候选拒绝[SemanticBarrier:Lifetime]：TBC/Close 跨 result producer 会改变 close/root epoch。
        // 候选拒绝[PolicyBoundary]：Unresolved 是 permissive 输出保留的失败证据，
        // region-result 不把未知路径并入普通 state 映射。
        return false;
    }
    if include_fallthrough && block_may_fall_through(body) {
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
    results.retain(|result| {
        loop_result_rewrite_end(block, index, *result).is_some_and(|rewrite_end| {
            rewrite_ends.insert(*result, rewrite_end);
            true
        })
    });
    if results.is_empty() {
        // 候选拒绝[SemanticBarrier:ControlFlow]：result 在后缀无 live-out 读取，或首个写是
        // 路径相关的结构化写；后者可能在未写分支继续观察 loop 产生的旧 result epoch。
        return false;
    }
    let rewrite_end = *rewrite_ends
        .get(results.first().expect("non-empty result set"))
        .expect("every retained result has a rewrite boundary");
    results.retain(|result| rewrite_ends.get(result) == Some(&rewrite_end));

    let loop_facts = binding_facts(std::slice::from_ref(stmt));
    results.retain(|result| loop_facts.reads.get(result).copied().unwrap_or(0) == 0);
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
        || !rewrite_is_private_and_uncaptured(index, &rewrites, result_index)
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：outer/private/capture/identity 不满足时，loop 外或 closure 可观察独立 result/state epoch。
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
        apply_loop_result_rewrites(block, index, rewrite_end, rewrites, promotion_facts);
    }
    true
}

fn loop_result_rewrite_end(
    block: &HirBlock,
    loop_index: usize,
    result: CarryBinding,
) -> Option<usize> {
    let mut saw_read = false;
    for (index, stmt) in block.stmts.iter().enumerate().skip(loop_index + 1) {
        let facts = binding_facts(std::slice::from_ref(stmt));
        let reads = facts.reads.contains_key(&result);
        if facts.writes.contains_key(&result) {
            let direct_overwrite = matches!(stmt, HirStmt::Assign(assign)
                if assign.targets.iter().any(|target| carry_binding_from_lvalue(target) == Some(result)));
            return ((saw_read || reads) && direct_overwrite).then_some(index);
        }
        saw_read |= reads;
    }
    saw_read.then_some(block.stmts.len())
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
    use crate::hir::common::{
        HirCallExpr, HirCallStmt, HirDecisionExpr, HirDecisionNode, HirDecisionNodeRef,
        HirDecisionTarget, HirGlobalRef, HirRepeat, HirReturn, HirWhile, ParamId, TempId,
    };
    use crate::hir::promotion::HomeSlotKey;

    fn empty_identity_facts() -> HandoffIdentityFacts {
        HandoffIdentityFacts {
            debug: BTreeSet::new(),
            for_bindings: BTreeSet::new(),
            physical_roots: BTreeSet::new(),
            captured: BTreeSet::new(),
            reference_captured: BTreeSet::new(),
            to_be_closed: BTreeSet::new(),
        }
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
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(0)),
                    then_block: HirBlock {
                        stmts: vec![HirStmt::Assign(Box::new(HirAssign {
                            targets: vec![HirLValue::Local(LocalId(0))],
                            values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
                        }))],
                    },
                    else_block: Some(HirBlock {
                        stmts: vec![HirStmt::Return(Box::new(HirReturn {
                            values: HirValuePack::fixed(vec![terminating_value]),
                        }))],
                    }),
                })),
                HirStmt::Assign(Box::new(HirAssign {
                    targets: vec![HirLValue::Param(ParamId(0))],
                    values: HirValuePack::fixed(vec![HirExpr::LocalRef(LocalId(0))]),
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
            }))],
        };
        HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::fixed(vec![HirExpr::Integer(10)]),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::default(),
                })),
                HirStmt::If(Box::new(HirIf {
                    cond: HirExpr::TempRef(TempId(1)),
                    then_block: branch(1),
                    else_block: Some(branch(2)),
                })),
                HirStmt::Return(Box::new(HirReturn {
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
            }))
        };
        HirBlock {
            stmts: vec![
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(0)],
                    values: HirValuePack::default(),
                })),
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings: vec![LocalId(1)],
                    values: HirValuePack::default(),
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
                            })),
                            HirStmt::CallStmt(Box::new(HirCallStmt {
                                call: HirCallExpr {
                                    callee: HirExpr::GlobalRef(HirGlobalRef {
                                        name: "collectgarbage".to_owned(),
                                    }),
                                    args: HirValuePack::default(),
                                    method: false,
                                    fastcall: None,
                                    method_name: None,
                                },
                            })),
                            result_copy(),
                            HirStmt::Break,
                        ],
                    },
                    cond: HirExpr::TempRef(TempId(1)),
                })),
                HirStmt::Return(Box::new(HirReturn {
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
            &BTreeSet::new(),
            &mut facts,
            &identity_facts,
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
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
        ));
        assert!(matches!(block.stmts.as_slice(), [HirStmt::If(_)]));
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
            &BTreeSet::new(),
            &mut facts,
            &empty_identity_facts(),
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
            &BTreeSet::new(),
            &mut facts,
            &identity_facts,
        ));
        assert!(block == original);
    }

    #[test]
    fn seeded_if_accepts_complete_paths_without_exact_seed_copy() {
        let mut block = seeded_if_without_copy_block();
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = seeded_if_facts(HomeSlotKey::new(0, 0));

        assert!(try_collapse_seeded_if_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = seeded_if_facts(HomeSlotKey::new(1, 0));

        assert!(!try_collapse_seeded_if_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
    fn loop_result_accepts_redundant_standalone_seed_copy() {
        let mut block = loop_result_block(HirExpr::ParamRef(ParamId(0)));
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut ProtoPromotionFacts::default(),
            &index,
            &empty_identity_facts(),
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
            })),
        );
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            1,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
            })),
        );
        block.stmts.insert(
            2,
            HirStmt::Assign(Box::new(HirAssign {
                targets: vec![HirLValue::Temp(TempId(0))],
                values: HirValuePack::fixed(vec![HirExpr::Integer(7)]),
            })),
        );
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
        }));
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
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
                    }))],
                },
                else_block: None,
            })),
        );
        let original = block.clone();
        let captured = BTreeSet::new();
        let index = RegionResultIndex::new(&block.stmts, &captured);
        let mut facts = loop_result_facts();

        assert!(!try_collapse_loop_results(
            &mut block,
            0,
            &BTreeSet::new(),
            &mut facts,
            &index,
            &empty_identity_facts(),
        ));
        assert!(block == original);
    }
}
