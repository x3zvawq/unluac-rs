//! 结构化 region result 与既有状态 binding 的交棒收敛。
//!
//! StructurePlan 会为 branch/loop result 保留独立 SSA 身份。提升到 HIR 后，这类身份
//! 可能表现为 `local result; if ... result = state ... end`，或在每个 loop break 前把
//! carried state 复制到 result temp。只有所有能抵达后缀的路径都完整定义 result，
//! 并能证明相邻写回或后续使用仍由同一 home slot 承担时，result 才能安全复用原
//! local/param；capture、跨 label 与独立状态写入都会阻止该折叠。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirAssign, HirBlock, HirExpr, HirIf, HirLValue, HirLocalDecl, HirStmt, HirValuePack, LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::super::visit::{HirVisitor, visit_stmts};
use super::super::walk::rewrite_stmts;
use super::binding::{
    BindingClassRewritePass, BindingProtection, CarryBinding, carry_binding_from_expr,
    carry_binding_from_lvalue,
};
use super::prune::{RedundantSelfAssignPrunePass, prune_empty_assign_stmts};
use super::reads::{collect_binding_mentions_by_stmt, collect_binding_mentions_in_expr};

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
    promotion_facts: &ProtoPromotionFacts,
    captured_bindings: &BTreeSet<CarryBinding>,
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
            let exits = if_fallthrough_assignments(if_stmt, &results)?;
            let inferred = infer_rewrites(
                &results,
                &exits,
                declaration_start,
                &result_index,
                promotion_facts,
            )?;
            (!inferred.iter().any(|(result, seed)| {
                outer_bindings.contains(result) || outer_bindings.contains(seed)
            }) && rewrite_is_private_and_uncaptured(region_index, &inferred, &result_index))
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
        },
    );
    rewrite_stmts(
        &mut block.stmts,
        &mut RedundantSelfAssignPrunePass::for_bindings(rewritten.iter().copied()),
    );
    for stmt in &mut block.stmts {
        split_rewritten_parallel_assignments(stmt, &rewritten);
    }
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
        if exits.len() < 2
            || !matches!(state, CarryBinding::Param(_) | CarryBinding::Local(_))
            || state == result
            || outer_bindings.contains(&result)
            || captured_bindings.contains(&result)
            || captured_bindings.contains(&state)
            || mention_counts.get(&result).copied() != Some(2)
            || facts.reads.contains_key(&result)
            || facts.writes.get(&result).copied() != Some(exits.len())
            || facts.writes.contains_key(&state)
            || stmt_has_label_or_goto(&block.stmts[index + 1])
        {
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
            &mut BindingClassRewritePass { rewrites },
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
    promotion_facts: &ProtoPromotionFacts,
    result_index: &RegionResultIndex<'_>,
) -> bool {
    try_collapse_seeded_if_results(block, index, outer_bindings, promotion_facts, result_index)
        || try_collapse_inferred_if_results(
            block,
            index,
            outer_bindings,
            promotion_facts,
            result_index,
        )
        || try_collapse_loop_results(block, index, outer_bindings, promotion_facts, result_index)
}

fn try_collapse_seeded_if_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    result_index: &RegionResultIndex<'_>,
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
        return false;
    }
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrites_preserve_home_slots(&rewrites, promotion_facts)
        || !rewrite_is_private_and_uncaptured(cursor, &rewrites, result_index)
    {
        return false;
    }
    if !apply_rewrites(block, result_start..cursor, cursor, rewrites) {
        return false;
    }
    merge_initialized_local_declarations(block, index, seeds.len());
    true
}

fn try_collapse_inferred_if_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    result_index: &RegionResultIndex<'_>,
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
    let Some(exits) = if_fallthrough_assignments(if_stmt, &results) else {
        return false;
    };
    let Some(rewrites) = infer_rewrites(&results, &exits, index, result_index, promotion_facts)
    else {
        return false;
    };
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrite_is_private_and_uncaptured(cursor, &rewrites, result_index)
    {
        return false;
    }
    apply_rewrites(block, index..cursor, cursor, rewrites)
}

fn try_collapse_loop_results(
    block: &mut HirBlock,
    index: usize,
    outer_bindings: &dyn BindingProtection,
    promotion_facts: &ProtoPromotionFacts,
    result_index: &RegionResultIndex<'_>,
) -> bool {
    let Some(stmt) = block.stmts.get(index) else {
        return false;
    };
    let (body, include_fallthrough) = match stmt {
        HirStmt::While(while_stmt) if while_stmt.cond == HirExpr::Boolean(true) => {
            (&while_stmt.body, false)
        }
        HirStmt::Repeat(repeat_stmt) if repeat_stmt.cond == HirExpr::Boolean(true) => {
            (&repeat_stmt.body, true)
        }
        _ => return false,
    };

    let mut exits = Vec::new();
    if !collect_break_assignments(body, &mut exits) || exits.is_empty() {
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
        return false;
    }

    let loop_facts = binding_facts(std::slice::from_ref(stmt));
    results.retain(|result| {
        loop_facts.reads.get(result).copied().unwrap_or(0) == 0
            && loop_facts.writes.get(result).copied().unwrap_or(0) == exits.len()
    });
    if results.is_empty() {
        return false;
    }
    let results = results.into_iter().collect::<Vec<_>>();
    let Some(rewrites) = infer_rewrites(&results, &exits, index, result_index, promotion_facts)
    else {
        return false;
    };
    if rewrites
        .iter()
        .any(|(result, seed)| outer_bindings.contains(result) || outer_bindings.contains(seed))
        || !rewrite_is_private_and_uncaptured(index, &rewrites, result_index)
    {
        return false;
    }
    apply_rewrites(block, index..index, index, rewrites)
}

fn initialized_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    local_decl
        .values
        .tail
        .is_none()
        .then_some((*binding, value))
}

fn empty_local(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

fn if_fallthrough_assignments(
    if_stmt: &HirIf,
    results: &[CarryBinding],
) -> Option<Vec<BTreeMap<CarryBinding, HirExpr>>> {
    let else_block = if_stmt.else_block.as_ref()?;
    let mut exits = Vec::new();
    let then_falls = collect_fallthrough_assignments(&if_stmt.then_block, results, &mut exits)?;
    let else_falls = collect_fallthrough_assignments(else_block, results, &mut exits)?;
    (then_falls || else_falls).then_some(exits)
}

fn complete_if_assignments(
    if_stmt: &HirIf,
    results: &[CarryBinding],
) -> Option<Vec<BTreeMap<CarryBinding, HirExpr>>> {
    let else_block = if_stmt.else_block.as_ref()?;
    let mut exits = Vec::new();
    collect_complete_assignments(&if_stmt.then_block, results, &mut exits)?;
    collect_complete_assignments(else_block, results, &mut exits)?;
    Some(exits)
}

fn collect_complete_assignments(
    block: &HirBlock,
    results: &[CarryBinding],
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
) -> Option<()> {
    let (last, prefix) = block.stmts.split_last()?;
    if bindings_are_mentioned_in_stmts(prefix, results) {
        return None;
    }
    match last {
        HirStmt::Assign(assign) => {
            exits.push(result_assignment_values(assign, results)?);
            Some(())
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            collect_complete_assignments(&if_stmt.then_block, results, exits)?;
            collect_complete_assignments(else_block, results, exits)
        }
        HirStmt::Block(block) => collect_complete_assignments(block, results, exits),
        _ => None,
    }
}

fn exact_state_writeback(stmt: &HirStmt, result: CarryBinding) -> Option<CarryBinding> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() || carry_binding_from_expr(value) != Some(result) {
        return None;
    }
    carry_binding_from_lvalue(target)
}

fn stmt_has_label_or_goto(stmt: &HirStmt) -> bool {
    match stmt {
        HirStmt::Goto(_) | HirStmt::Label(_) => true,
        HirStmt::If(if_stmt) => {
            block_has_label_or_goto(&if_stmt.then_block)
                || if_stmt
                    .else_block
                    .as_ref()
                    .is_some_and(block_has_label_or_goto)
        }
        HirStmt::While(while_stmt) => block_has_label_or_goto(&while_stmt.body),
        HirStmt::Repeat(repeat_stmt) => block_has_label_or_goto(&repeat_stmt.body),
        HirStmt::NumericFor(numeric_for) => block_has_label_or_goto(&numeric_for.body),
        HirStmt::GenericFor(generic_for) => block_has_label_or_goto(&generic_for.body),
        HirStmt::Block(block) => block_has_label_or_goto(block),
        _ => false,
    }
}

fn block_has_label_or_goto(block: &HirBlock) -> bool {
    block.stmts.iter().any(stmt_has_label_or_goto)
}

fn inline_owned_branch_conditions(
    block: &mut HirBlock,
    candidates: &BTreeSet<LocalId>,
    outer_bindings: &dyn BindingProtection,
    captured_bindings: &BTreeSet<CarryBinding>,
) -> bool {
    let mut eligible = candidates
        .iter()
        .copied()
        .filter(|local| {
            let binding = CarryBinding::Local(*local);
            !outer_bindings.contains(&binding) && !captured_bindings.contains(&binding)
        })
        .collect::<BTreeSet<_>>();
    if eligible.is_empty() {
        return false;
    }

    let mentions = collect_binding_mentions_by_stmt(&block.stmts);
    let mut invalid = BTreeSet::new();
    for (index, stmt_mentions) in mentions.iter().enumerate() {
        for local in stmt_mentions.iter().filter_map(|binding| match binding {
            CarryBinding::Local(local) if eligible.contains(local) => Some(*local),
            CarryBinding::Param(_) | CarryBinding::Local(_) | CarryBinding::Temp(_) => None,
        }) {
            if !condition_scratch_mention_is_owned(&block.stmts, index, local) {
                invalid.insert(local);
            }
        }
    }
    eligible.retain(|local| !invalid.contains(local));
    if eligible.is_empty() {
        return false;
    }

    let mut removed = vec![false; block.stmts.len()];
    let producer_count = block.stmts.len().saturating_sub(1);
    for (index, remove) in removed.iter_mut().enumerate().take(producer_count) {
        let Some((local, value)) = condition_scratch_producer(&block.stmts[index]) else {
            continue;
        };
        if !eligible.contains(&local) || !condition_if_uses_only(&block.stmts[index + 1], local) {
            continue;
        }
        let value = value.clone();
        let HirStmt::If(if_stmt) = &mut block.stmts[index + 1] else {
            continue;
        };
        if_stmt.cond = value;
        *remove = true;
    }
    let changed = removed.iter().any(|removed| *removed);
    if changed {
        let mut cursor = 0;
        block.stmts.retain(|_| {
            let keep = !removed[cursor];
            cursor += 1;
            keep
        });
    }
    changed
}

fn condition_scratch_mention_is_owned(stmts: &[HirStmt], index: usize, local: LocalId) -> bool {
    condition_scratch_producer(&stmts[index]).is_some_and(|(binding, _)| {
        binding == local
            && stmts
                .get(index + 1)
                .is_some_and(|stmt| condition_if_uses_only(stmt, local))
    }) || index.checked_sub(1).is_some_and(|producer| {
        condition_scratch_producer(&stmts[producer]).is_some_and(|(binding, _)| {
            binding == local && condition_if_uses_only(&stmts[index], local)
        })
    })
}

fn condition_scratch_producer(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let (binding, values) = match stmt {
        HirStmt::LocalDecl(local_decl) => {
            let [binding] = local_decl.bindings.as_slice() else {
                return None;
            };
            (*binding, &local_decl.values)
        }
        HirStmt::Assign(assign) => {
            let [HirLValue::Local(binding)] = assign.targets.as_slice() else {
                return None;
            };
            (*binding, &assign.values)
        }
        _ => return None,
    };
    let [value] = values.fixed.as_slice() else {
        return None;
    };
    if values.tail.is_some()
        || collect_binding_mentions_in_expr(value).contains(&CarryBinding::Local(binding))
    {
        return None;
    }
    Some((binding, value))
}

fn condition_if_uses_only(stmt: &HirStmt, local: LocalId) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    if if_stmt.cond != HirExpr::LocalRef(local) {
        return false;
    }
    let binding = CarryBinding::Local(local);
    !binding_is_mentioned_in_stmts(&if_stmt.then_block.stmts, binding)
        && if_stmt
            .else_block
            .as_ref()
            .is_none_or(|block| !binding_is_mentioned_in_stmts(&block.stmts, binding))
}

fn collect_fallthrough_assignments(
    block: &HirBlock,
    results: &[CarryBinding],
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
) -> Option<bool> {
    let (last, prefix) = block.stmts.split_last()?;
    if bindings_are_mentioned_in_stmts(prefix, results) {
        return None;
    }
    match last {
        HirStmt::Assign(assign) => {
            exits.push(result_assignment_values(assign, results)?);
            Some(true)
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_falls = collect_fallthrough_assignments(&if_stmt.then_block, results, exits)?;
            let else_falls = collect_fallthrough_assignments(else_block, results, exits)?;
            Some(then_falls || else_falls)
        }
        HirStmt::Block(block) => collect_fallthrough_assignments(block, results, exits),
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => Some(false),
        _ => None,
    }
}

fn result_assignment_values(
    assign: &HirAssign,
    results: &[CarryBinding],
) -> Option<BTreeMap<CarryBinding, HirExpr>> {
    let values = assignment_values(assign)?;
    let result_values = results
        .iter()
        .map(|result| Some((*result, values.get(result)?.clone())))
        .collect::<Option<BTreeMap<_, _>>>()?;
    (!bindings_are_mentioned_in_exprs(result_values.values(), results)).then_some(result_values)
}

fn assignment_values(assign: &HirAssign) -> Option<BTreeMap<CarryBinding, HirExpr>> {
    if assign.values.tail.is_some() || assign.targets.len() != assign.values.fixed.len() {
        return None;
    }
    let mut values = BTreeMap::new();
    for (target, value) in assign.targets.iter().zip(&assign.values.fixed) {
        let Some(binding) = carry_binding_from_lvalue(target) else {
            continue;
        };
        if values.insert(binding, value.clone()).is_some() {
            return None;
        }
    }
    Some(values)
}

fn collect_break_assignments(
    block: &HirBlock,
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
) -> bool {
    for (index, stmt) in block.stmts.iter().enumerate() {
        match stmt {
            HirStmt::Break => {
                let Some(HirStmt::Assign(assign)) = index
                    .checked_sub(1)
                    .and_then(|index| block.stmts.get(index))
                else {
                    return false;
                };
                let Some(exit) = assignment_values(assign) else {
                    return false;
                };
                exits.push(exit);
            }
            HirStmt::If(if_stmt) => {
                if !collect_break_assignments(&if_stmt.then_block, exits)
                    || if_stmt
                        .else_block
                        .as_ref()
                        .is_some_and(|block| !collect_break_assignments(block, exits))
                {
                    return false;
                }
            }
            HirStmt::Block(block) => {
                if !collect_break_assignments(block, exits) {
                    return false;
                }
            }
            HirStmt::While(_)
            | HirStmt::Repeat(_)
            | HirStmt::NumericFor(_)
            | HirStmt::GenericFor(_) => {}
            _ => {}
        }
    }
    true
}

fn block_may_fall_through(block: &HirBlock) -> bool {
    let Some(last) = block.stmts.last() else {
        return true;
    };
    match last {
        HirStmt::Return(_) | HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) => false,
        HirStmt::If(if_stmt) => if_stmt.else_block.as_ref().is_none_or(|else_block| {
            block_may_fall_through(&if_stmt.then_block) || block_may_fall_through(else_block)
        }),
        HirStmt::Block(block) => block_may_fall_through(block),
        _ => true,
    }
}

fn infer_rewrites(
    results: &[CarryBinding],
    exits: &[BTreeMap<CarryBinding, HirExpr>],
    region_index: usize,
    result_index: &RegionResultIndex<'_>,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<BTreeMap<CarryBinding, CarryBinding>> {
    let mut rewrites = BTreeMap::new();
    let mut claimed = BTreeSet::new();
    for result in results {
        let candidates = exits
            .iter()
            .filter_map(|exit| exit.get(result))
            .filter_map(carry_binding_from_expr)
            .filter(|binding| result_index.is_available_before(*binding, region_index))
            .collect::<BTreeSet<_>>();
        let mut candidates = candidates.into_iter();
        let seed = candidates.next()?;
        if candidates.next().is_some() {
            return None;
        }
        if seed == *result || !claimed.insert(seed) {
            return None;
        }
        if !bindings_share_home_slot(*result, seed, promotion_facts) {
            return None;
        }
        rewrites.insert(*result, seed);
    }
    Some(rewrites)
}

fn rewrites_preserve_home_slots(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    rewrites
        .iter()
        .all(|(result, seed)| bindings_share_home_slot(*result, *seed, promotion_facts))
}

fn bindings_share_home_slot(
    result: CarryBinding,
    seed: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    promotion_facts.compacts_home_slots()
        || binding_home_slot(result, promotion_facts)
            .zip(binding_home_slot(seed, promotion_facts))
            .is_some_and(|(result, seed)| result == seed)
}

fn binding_home_slot(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match binding {
        CarryBinding::Param(param) => Some(HomeSlotKey::new(param.index(), 0)),
        CarryBinding::Local(local) => promotion_facts.local_home_slot(local),
        CarryBinding::Temp(temp) => promotion_facts.home_slot(temp),
    }
}

fn rewrite_is_private_and_uncaptured(
    region_index: usize,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    result_index: &RegionResultIndex<'_>,
) -> bool {
    rewrites
        .values()
        .all(|seed| result_index.is_private_after(*seed, region_index))
}

fn apply_rewrites(
    block: &mut HirBlock,
    declarations: std::ops::Range<usize>,
    region_index: usize,
    rewrites: BTreeMap<CarryBinding, CarryBinding>,
) -> bool {
    let prunable = rewrites.values().copied().collect::<BTreeSet<_>>();
    let rewritten = rewrite_stmts(
        &mut block.stmts[region_index..],
        &mut BindingClassRewritePass { rewrites },
    );
    if !rewritten {
        return false;
    }
    rewrite_stmts(
        &mut block.stmts[region_index..],
        &mut RedundantSelfAssignPrunePass::for_bindings(prunable.iter().copied()),
    );
    split_rewritten_parallel_assignments(&mut block.stmts[region_index], &prunable);
    if !declarations.is_empty() {
        block.stmts.drain(declarations);
    }
    prune_empty_assign_stmts(block);
    true
}

fn merge_initialized_local_declarations(block: &mut HirBlock, start: usize, count: usize) -> bool {
    if count < 2 || start + count > block.stmts.len() {
        return false;
    }
    let mut bindings = Vec::with_capacity(count);
    let mut values = Vec::with_capacity(count);
    for stmt in &block.stmts[start..start + count] {
        let Some((binding, value)) = initialized_local(stmt) else {
            return false;
        };
        let earlier = bindings
            .iter()
            .copied()
            .map(CarryBinding::Local)
            .collect::<Vec<_>>();
        if bindings_are_mentioned_in_exprs(std::iter::once(value), &earlier) {
            return false;
        }
        bindings.push(binding);
        values.push(value.clone());
    }
    block.stmts[start] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
        bindings,
        values: HirValuePack::fixed(values),
    }));
    block.stmts.drain(start + 1..start + count);
    true
}

fn split_rewritten_parallel_assignments(
    stmt: &mut HirStmt,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed =
                split_rewritten_parallel_assignments_in_block(&mut if_stmt.then_block, rewritten);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= split_rewritten_parallel_assignments_in_block(else_block, rewritten);
            }
            changed
        }
        HirStmt::While(while_stmt) => {
            split_rewritten_parallel_assignments_in_block(&mut while_stmt.body, rewritten)
        }
        HirStmt::Repeat(repeat_stmt) => {
            split_rewritten_parallel_assignments_in_block(&mut repeat_stmt.body, rewritten)
        }
        HirStmt::NumericFor(numeric_for) => {
            split_rewritten_parallel_assignments_in_block(&mut numeric_for.body, rewritten)
        }
        HirStmt::GenericFor(generic_for) => {
            split_rewritten_parallel_assignments_in_block(&mut generic_for.body, rewritten)
        }
        HirStmt::Block(block) => split_rewritten_parallel_assignments_in_block(block, rewritten),
        _ => false,
    }
}

fn split_rewritten_parallel_assignments_in_block(
    block: &mut HirBlock,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    let mut changed = false;
    let mut rebuilt = Vec::with_capacity(block.stmts.len());
    for mut stmt in std::mem::take(&mut block.stmts) {
        changed |= split_rewritten_parallel_assignments(&mut stmt, rewritten);
        let HirStmt::Assign(assign) = stmt else {
            rebuilt.push(stmt);
            continue;
        };
        if !parallel_assignment_is_independent(&assign, rewritten) {
            rebuilt.push(HirStmt::Assign(assign));
            continue;
        }
        let HirAssign { targets, values } = *assign;
        rebuilt.extend(
            targets
                .into_iter()
                .zip(values.fixed)
                .map(|(target, value)| {
                    HirStmt::Assign(Box::new(HirAssign {
                        targets: vec![target],
                        values: HirValuePack::fixed(vec![value]),
                    }))
                }),
        );
        changed = true;
    }
    block.stmts = rebuilt;
    changed
}

fn parallel_assignment_is_independent(
    assign: &HirAssign,
    rewritten: &BTreeSet<CarryBinding>,
) -> bool {
    if assign.values.tail.is_some()
        || assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
    {
        return false;
    }
    let Some(targets) = assign
        .targets
        .iter()
        .map(carry_binding_from_lvalue)
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    if targets
        .iter()
        .filter(|target| rewritten.contains(target))
        .count()
        < 1
        || targets.iter().copied().collect::<BTreeSet<_>>().len() != targets.len()
    {
        return false;
    }
    !bindings_are_mentioned_in_exprs(assign.values.fixed.iter(), &targets)
}

#[derive(Default)]
struct BindingFacts {
    reads: BTreeMap<CarryBinding, usize>,
    writes: BTreeMap<CarryBinding, usize>,
}

impl HirVisitor for BindingFacts {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let Some(binding) = carry_binding_from_expr(expr) {
            *self.reads.entry(binding).or_default() += 1;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let Some(binding) = carry_binding_from_lvalue(lvalue) {
            *self.writes.entry(binding).or_default() += 1;
        }
    }
}

fn binding_facts(stmts: &[HirStmt]) -> BindingFacts {
    let mut facts = BindingFacts::default();
    visit_stmts(stmts, &mut facts);
    facts
}

fn binding_is_read_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    binding_facts(stmts)
        .reads
        .get(&binding)
        .copied()
        .unwrap_or(0)
        != 0
}

fn binding_is_written_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    binding_facts(stmts)
        .writes
        .get(&binding)
        .copied()
        .unwrap_or(0)
        != 0
}

fn binding_is_mentioned_in_stmts(stmts: &[HirStmt], binding: CarryBinding) -> bool {
    let facts = binding_facts(stmts);
    facts.reads.contains_key(&binding) || facts.writes.contains_key(&binding)
}

fn bindings_are_mentioned_in_stmts(stmts: &[HirStmt], bindings: &[CarryBinding]) -> bool {
    let facts = binding_facts(stmts);
    bindings
        .iter()
        .any(|binding| facts.reads.contains_key(binding) || facts.writes.contains_key(binding))
}

fn bindings_are_mentioned_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a HirExpr>,
    bindings: &[CarryBinding],
) -> bool {
    let mut facts = BindingFacts::default();
    for expr in exprs {
        super::super::visit::visit_expr(expr, &mut facts);
    }
    bindings
        .iter()
        .any(|binding| facts.reads.contains_key(binding))
}
