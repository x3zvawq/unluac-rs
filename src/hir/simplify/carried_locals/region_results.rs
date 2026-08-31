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
use flow::{expr_has_forbidden_nodes, region_has_forbidden_nodes};
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
            if region_has_forbidden_nodes(&block.stmts[region_index..=region_index]) {
                // 候选拒绝[LayerBoundary]：goto/close/Decision 等边界分别由 CFG/resource/decision owner 消费。
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
        let Some(exits) = complete_if_assignments(if_stmt, &[result]) else {
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
                && exit.get(&result).and_then(carry_binding_from_expr) == Some(state)
        });
        if exits.len() < 2
            || !matches!(state, CarryBinding::Param(_) | CarryBinding::Local(_))
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
            || region_has_forbidden_nodes(&block.stmts[index + 1..=index + 1])
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：capture/outer use、异槽、额外 result mention 或 state 被独立写入时，改名会合并可区分 epoch。
            // 候选拒绝[ProofIncomplete]：单出口 if 与 forbidden-node region 需要更一般的路径/owner 事实，当前 exact arm 计数不覆盖。
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
    inline_owned_branch_conditions(block, &condition_scratch, outer_bindings, captured_bindings);
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
    if region_has_forbidden_nodes(&block.stmts[cursor..=cursor]) {
        // 候选拒绝[LayerBoundary]：非结构控制、cleanup 与残留 Decision 不由 seeded-if owner 展开。
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
    if !rewrites.iter().all(|(result, seed)| {
        exits
            .iter()
            .any(|exit| exit.get(result).and_then(carry_binding_from_expr) == Some(*seed))
    }) {
        // 候选拒绝[ProofIncomplete]：某 result 没有任何出口精确复制对应 seed 时，seed/result 关系需更一般的路径证明。
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
    if !apply_rewrites(
        block,
        result_start..cursor,
        cursor,
        rewrites,
        promotion_facts,
    ) {
        // 候选拒绝[ConvergenceGuard]：exits 已证明 region 中存在每个 result 写；apply 无命中表示分析/rewriter 契约漂移。
        return false;
    }
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
    if region_has_forbidden_nodes(&block.stmts[cursor..=cursor]) {
        // 候选拒绝[LayerBoundary]：goto/close/Decision 等边界需先由各自 owner 消费。
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
    apply_rewrites(block, index..cursor, cursor, rewrites, promotion_facts)
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
            expr_has_forbidden_nodes(&repeat_stmt.cond),
        ),
        _ => return false,
    };
    let mut exits = Vec::new();
    // 内层 loop 的 break/continue 归内层 owner，但跳转、cleanup 或残留 Decision 都
    // 可能绕过 result 写回；这类边界不能交给 `collect_break_assignments` 猜测。
    if condition_forbidden
        || region_has_forbidden_nodes(&body.stmts)
        || !collect_break_assignments(body, &mut exits, requires_exact_exits)
    {
        // 候选拒绝[SemanticBarrier:ControlFlow]：未跟踪 transfer 会漏掉 loop 出口，提交不完整 result->state 映射。
        // 候选拒绝[LayerBoundary]：cleanup/Decision/Unresolved 分别由资源与 decision owner 处理。
        return false;
    }
    if include_fallthrough && block_may_fall_through(body) {
        let Some(HirStmt::Assign(assign)) = body.stmts.last() else {
            return false;
        };
        let Some(exit) = assignment_values(assign) else {
            return false;
        };
        exits.push(exit);
    }
    if exits.is_empty() {
        // 候选拒绝[ProofIncomplete]：没有显式 break/fallthrough assignment 时尚无 loop result reaching-def。
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
    let suffix = &block.stmts[index + 1..];
    results.retain(|result| {
        binding_is_read_in_stmts(suffix, *result)
            && !binding_is_written_in_stmts(suffix, *result)
            && !binding_is_mentioned_in_stmts(&block.stmts[..index], *result)
    });
    if results.is_empty() {
        // 候选拒绝[ProofIncomplete]：无“suffix 只读且 prefix 不提”的 temp result；其它 live-out 形态需跨区间 def-use。
        return false;
    }

    let loop_facts = binding_facts(std::slice::from_ref(stmt));
    results.retain(|result| {
        loop_facts.reads.get(result).copied().unwrap_or(0) == 0
            && loop_facts.writes.get(result).copied().unwrap_or(0) == exits.len()
    });
    if results.is_empty() {
        // 候选拒绝[ProofIncomplete]：loop 内读 result 或写次数不等于出口数时，当前 exact-exit 模型无法配对路径。
        return false;
    }
    let results = results.into_iter().collect::<Vec<_>>();
    let Some(rewrites) = infer_rewrites(
        &results,
        &exits,
        index,
        result_index,
        promotion_facts,
        !requires_exact_exits,
    ) else {
        return false;
    };
    // 动态 repeat 的 synthetic result 没有稳定 home slot；只有每条出口都是 state 的
    // 精确快照且不在同一赋值中改写 state，才能把这个跨槽身份安全消掉。
    if requires_exact_exits
        && !rewrites.iter().all(|(result, seed)| {
            exits.iter().all(|exit| {
                !exit.contains_key(seed)
                    && exit.get(result).and_then(carry_binding_from_expr) == Some(*seed)
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
    apply_rewrites(block, index..index, index, rewrites, promotion_facts)
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
