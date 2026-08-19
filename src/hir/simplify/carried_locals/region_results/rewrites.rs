//! 收集 break assignment、推导 carried binding 重写并校验 home slot/capture；依赖 slot ownership，不负责并行赋值拆分；例如拒绝跨捕获槽的别名重写。

use super::*;

pub(super) fn collect_break_assignments(
    block: &HirBlock,
    exits: &mut Vec<BTreeMap<CarryBinding, HirExpr>>,
    reject_untracked_transfers: bool,
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
                if !collect_break_assignments(
                    &if_stmt.then_block,
                    exits,
                    reject_untracked_transfers,
                ) || if_stmt.else_block.as_ref().is_some_and(|block| {
                    !collect_break_assignments(block, exits, reject_untracked_transfers)
                }) {
                    return false;
                }
            }
            HirStmt::Block(block) => {
                if !collect_break_assignments(block, exits, reject_untracked_transfers) {
                    return false;
                }
            }
            HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_)
                if reject_untracked_transfers =>
            {
                return false;
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

pub(super) fn block_may_fall_through(block: &HirBlock) -> bool {
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

pub(super) fn infer_rewrites(
    results: &[CarryBinding],
    exits: &[BTreeMap<CarryBinding, HirExpr>],
    region_index: usize,
    result_index: &RegionResultIndex<'_>,
    promotion_facts: &ProtoPromotionFacts,
    require_home_slot: bool,
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
        if require_home_slot && !bindings_share_home_slot(*result, seed, promotion_facts) {
            return None;
        }
        rewrites.insert(*result, seed);
    }
    Some(rewrites)
}

pub(super) fn rewrites_preserve_home_slots(
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    rewrites
        .iter()
        .all(|(result, seed)| bindings_share_home_slot(*result, *seed, promotion_facts))
}

pub(super) fn bindings_share_home_slot(
    result: CarryBinding,
    seed: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    promotion_facts.compacts_home_slots()
        || binding_home_slot(result, promotion_facts)
            .zip(binding_home_slot(seed, promotion_facts))
            .is_some_and(|(result, seed)| result == seed)
}

pub(super) fn binding_home_slot(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match binding {
        CarryBinding::Param(param) => Some(HomeSlotKey::new(param.index(), 0)),
        CarryBinding::Local(local) => promotion_facts.local_home_slot(local),
        CarryBinding::Temp(temp) => promotion_facts.home_slot(temp),
    }
}

pub(super) fn rewrite_is_private_and_uncaptured(
    region_index: usize,
    rewrites: &BTreeMap<CarryBinding, CarryBinding>,
    result_index: &RegionResultIndex<'_>,
) -> bool {
    rewrites
        .values()
        .all(|seed| result_index.is_private_after(*seed, region_index))
}

pub(super) fn apply_rewrites(
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
