//! 这个文件识别普通 HIR 值活跃性看不到的物理槽 root 生命周期。
//!
//! fixed call result、已逃逸 table allocation，以及已跨显式 GC 的 lookup result，即使没有
//! HIR 读取，也会在同一 stack home 被覆盖前继续充当 VM GC root。copy 共享值 identity，
//! 但每个目标 home 都是独立 root transaction；同一 parallel overwrite 可终止多个 home，
//! 消费者只能把 producer 与同 home 的精确覆盖配对。
//! 分析只在单个 block 内追踪；只有 nested structure 不写 active home，且没有 opaque transfer
//! 或 cleanup 边界时才允许穿过。消费者可以保留已配对的两次 materialization，也可以在
//! 更窄的改写仍保持同一覆盖事务时，连同 owner 已证明的 physical home 一起消费该 pair。
//! 潜在求值事件与分支覆盖值的 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId, ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::temp_touch::{collect_temp_reads_by_stmt, stmt_consumes_temps_only_in_control_head};
use super::visit::{HirVisitor, visit_stmts};

struct ActiveCallRoot {
    root_index: usize,
    aliases: BTreeSet<TempId>,
    observed: bool,
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct LookupValueId(usize);

struct ActiveLookupGcHome {
    value_id: LookupValueId,
    root_index: usize,
    aliases: BTreeSet<TempId>,
    eligible: bool,
    crossed_gc_fence: bool,
}

struct ActiveAllocationRoot {
    root_index: usize,
    aliases: BTreeSet<TempId>,
    homes: BTreeSet<HomeSlotKey>,
    def_indices: BTreeSet<usize>,
    escaped: bool,
    eligible: bool,
}

struct ExactNilHomeOverwrite {
    temps: BTreeSet<TempId>,
    home: HomeSlotKey,
    eligible: bool,
}

struct ExactBranchHomeOverwrite {
    temps: BTreeSet<TempId>,
    home: HomeSlotKey,
    eligible: bool,
}

struct ExactMultiCallRootTarget {
    temp: TempId,
    home: HomeSlotKey,
}

#[derive(Default)]
pub(super) struct CallRootLifetimeIndices {
    roots: BTreeSet<usize>,
    root_homes: BTreeMap<usize, BTreeSet<HomeSlotKey>>,
    roots_by_overwrite: BTreeMap<usize, Vec<CallRootOverwritePair>>,
    root_by_protected: BTreeMap<usize, usize>,
}

#[derive(Clone, Copy)]
pub(super) struct CallRootOverwritePair {
    root_index: usize,
    home: HomeSlotKey,
}

#[derive(Default)]
pub(super) struct LookupGcRootLifetimeIndices {
    roots: BTreeSet<usize>,
    roots_by_overwrite: BTreeMap<usize, Vec<LookupGcRootOverwritePair>>,
}

#[derive(Clone, Copy)]
pub(super) struct LookupGcRootOverwritePair {
    root_index: usize,
    home: HomeSlotKey,
}

impl CallRootOverwritePair {
    pub(super) fn root_index(self) -> usize {
        self.root_index
    }

    pub(super) fn home(self) -> HomeSlotKey {
        self.home
    }
}

impl CallRootLifetimeIndices {
    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn root_homes(&self, index: usize) -> impl Iterator<Item = HomeSlotKey> + '_ {
        self.root_homes.get(&index).into_iter().flatten().copied()
    }

    pub(super) fn overwrite_pair_for_home(
        &self,
        index: usize,
        home: HomeSlotKey,
    ) -> Option<CallRootOverwritePair> {
        self.roots_by_overwrite
            .get(&index)?
            .iter()
            .find(|pair| pair.home == home)
            .copied()
    }

    pub(super) fn overwrite_pairs(
        &self,
        index: usize,
    ) -> impl Iterator<Item = CallRootOverwritePair> + '_ {
        self.roots_by_overwrite
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn unambiguous_root_for_overwrite(&self, index: usize) -> Option<usize> {
        let [pair] = self.roots_by_overwrite.get(&index)?.as_slice() else {
            return None;
        };
        Some(pair.root_index)
    }

    pub(super) fn root_for_protected(&self, index: usize) -> Option<usize> {
        self.root_by_protected.get(&index).copied()
    }

    pub(super) fn marked_stmts(&self, stmt_count: usize) -> Vec<bool> {
        let mut marked = vec![false; stmt_count];
        for index in self.roots.iter().chain(self.roots_by_overwrite.keys()) {
            marked[*index] = true;
        }
        marked
    }
}

impl LookupGcRootLifetimeIndices {
    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn overwrite_pair_for_home(
        &self,
        index: usize,
        home: HomeSlotKey,
    ) -> Option<LookupGcRootOverwritePair> {
        self.roots_by_overwrite
            .get(&index)?
            .iter()
            .find(|pair| pair.home == home)
            .copied()
    }

    pub(super) fn overwrite_pairs(
        &self,
        index: usize,
    ) -> impl Iterator<Item = LookupGcRootOverwritePair> + '_ {
        self.roots_by_overwrite
            .get(&index)
            .into_iter()
            .flatten()
            .copied()
    }

    pub(super) fn mark_stmts(&self, marked: &mut [bool]) {
        for index in self.roots.iter().chain(self.roots_by_overwrite.keys()) {
            marked[*index] = true;
        }
    }
}

impl LookupGcRootOverwritePair {
    pub(super) fn root_index(self) -> usize {
        self.root_index
    }

    pub(super) fn home(self) -> HomeSlotKey {
        self.home
    }
}

pub(super) fn collect_call_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    observe_potential_events: bool,
    mut producer_temp_is_eligible: impl FnMut(TempId) -> bool,
    mut overwrite_temp_is_eligible: impl FnMut(TempId) -> bool,
) -> CallRootLifetimeIndices {
    let uses = TempUseEvents::new(stmts);
    let mut active = BTreeMap::<HomeSlotKey, ActiveCallRoot>::new();
    let mut active_allocations = Vec::<ActiveAllocationRoot>::new();
    // Lua 编译器会用 literal nil 的纯 temp copy 清除同 home 的 allocation root；只沿这条
    // 无副作用链传播 nil 事实，其余写入必须先让旧事实失效。
    let mut known_nil_temps = BTreeSet::<TempId>::new();
    let mut lifetimes = CallRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        if uses.is_gc_fence(index) {
            preserve_active_call_roots(&mut active, &mut lifetimes);
        } else if observe_potential_events && stmt_may_observe_gc_roots(stmt, safety) {
            // A potential user-code/GC event matters only if a later same-home overwrite proves
            // the end of this transaction. Unlike an explicit collection fence, this does not
            // by itself justify materializing every still-active call result.
            for root in active.values_mut() {
                root.observed = true;
            }
        }
        let reads = uses.reads_at(index);
        for root in active.values_mut() {
            if reads.is_some_and(|reads| root.aliases.iter().any(|temp| reads.contains(temp))) {
                // A read still needs the same-local overwrite pairing, but a loop predicate or
                // a direct `if temp`/`if not temp` test only consumes the value as control flow.
                // Treating those forwarding reads as observations materializes ordinary loop
                // snapshots as locals. Compound one-shot tests (for example `temp == 1`) stay
                // observed so the call/result boundary remains readable. An explicit collection
                // fence after any copy still upgrades the root below.
                let is_loop_control = matches!(
                    stmt,
                    HirStmt::While(_)
                        | HirStmt::Repeat(_)
                        | HirStmt::NumericFor(_)
                        | HirStmt::GenericFor(_)
                );
                if (!is_loop_control
                    && !stmt_is_direct_if_control_read(stmt, &root.aliases)
                    && !stmt_is_transparent_temp_copy(stmt, &root.aliases))
                    || uses.has_gc_fence_after(index)
                {
                    root.observed = true;
                }
            }
        }
        let escaped_temps = direct_table_assignment_temps(stmt);
        for root in &mut active_allocations {
            root.escaped |= root
                .aliases
                .iter()
                .any(|alias| escaped_temps.contains(alias));
        }
        let Some((temp, value)) = scalar_temp_definition(stmt) else {
            forget_written_known_nil_temps(stmt, &mut known_nil_temps);
            if let Some(targets) =
                exact_multi_call_root_targets(stmt, facts, &mut producer_temp_is_eligible)
            {
                let target_homes = targets
                    .iter()
                    .map(|target| target.home)
                    .collect::<BTreeSet<_>>();
                for target in &targets {
                    if let Some(root) = active.remove(&target.home) {
                        record_call_root_overwrite(
                            root,
                            index,
                            target.home,
                            true,
                            &uses,
                            &mut lifetimes,
                        );
                    }
                }
                for root in active.values_mut() {
                    for target in &targets {
                        root.aliases.remove(&target.temp);
                    }
                }
                remove_allocation_homes(&mut active_allocations, &target_homes, facts);
                for target in targets {
                    active.insert(
                        target.home,
                        ActiveCallRoot {
                            root_index: index,
                            aliases: BTreeSet::from([target.temp]),
                            observed: false,
                        },
                    );
                }
                continue;
            }
            if let Some(overwrites) =
                exact_multi_nil_temp_overwrites(stmt, facts, &mut overwrite_temp_is_eligible)
            {
                for ExactNilHomeOverwrite {
                    temps,
                    home,
                    eligible,
                } in overwrites
                {
                    known_nil_temps.extend(temps.iter().copied());
                    if let Some(root) = active.remove(&home) {
                        record_call_root_overwrite(
                            root,
                            index,
                            home,
                            eligible,
                            &uses,
                            &mut lifetimes,
                        );
                    }
                    let mut allocation_state = AllocationRootState {
                        active: &mut active_allocations,
                        lifetimes: &mut lifetimes,
                        uses: &uses,
                        facts,
                    };
                    for temp in temps {
                        update_allocation_roots(
                            &mut allocation_state,
                            index,
                            temp,
                            &HirExpr::Nil,
                            true,
                            home,
                            eligible,
                        );
                    }
                }
                continue;
            }
            if let Some(overwrite) = definite_gc_inert_branch_home_overwrite(
                stmt,
                facts,
                &mut overwrite_temp_is_eligible,
                safety,
            ) {
                if let Some(root) = active.remove(&overwrite.home) {
                    record_call_root_overwrite(
                        root,
                        index,
                        overwrite.home,
                        overwrite.eligible,
                        &uses,
                        &mut lifetimes,
                    );
                }
                terminate_allocation_home(
                    &mut active_allocations,
                    &mut lifetimes,
                    &uses,
                    facts,
                    index,
                    overwrite.home,
                    overwrite.eligible,
                );
                continue;
            }
            let writes = StackWriteSummary::for_stmt(stmt, facts);
            if writes.has_boundary || writes.has_unknown_home {
                active.clear();
                active_allocations.clear();
            } else {
                active.retain(|slot, _| !writes.homes.contains(slot));
                for root in active.values_mut() {
                    root.aliases.retain(|temp| {
                        facts
                            .trusted_temp_home_slot(*temp)
                            .is_none_or(|slot| !writes.homes.contains(&slot))
                    });
                }
                remove_allocation_homes(&mut active_allocations, &writes.homes, facts);
            }
            continue;
        };
        let value_is_known_nil = matches!(value, HirExpr::Nil)
            || matches!(value, HirExpr::TempRef(source) if known_nil_temps.contains(source));
        known_nil_temps.remove(&temp);
        if value_is_known_nil {
            known_nil_temps.insert(temp);
        }
        let Some(slot) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            active_allocations.clear();
            continue;
        };

        let producer_eligible = producer_temp_is_eligible(temp);
        let overwrite_eligible = overwrite_temp_is_eligible(temp);
        let mut allocation_state = AllocationRootState {
            active: &mut active_allocations,
            lifetimes: &mut lifetimes,
            uses: &uses,
            facts,
        };
        update_allocation_roots(
            &mut allocation_state,
            index,
            temp,
            value,
            value_is_known_nil,
            slot,
            producer_eligible,
        );
        let same_value_in_target_home = matches!(value, HirExpr::TempRef(source)
            if active
                .get(&slot)
                .is_some_and(|root| root.aliases.contains(source)));
        for root in active.values_mut() {
            root.aliases.remove(&temp);
        }

        if matches!(value, HirExpr::Call(_))
            && let Some(write_homes) = facts.trusted_immediate_move_write_homes(temp)
        {
            let extra_write_homes = write_homes
                .iter()
                .copied()
                .filter(|home| *home != slot)
                .collect::<BTreeSet<_>>();
            for write_home in &extra_write_homes {
                if let Some(root) = active.remove(write_home) {
                    record_call_root_overwrite(
                        root,
                        index,
                        *write_home,
                        overwrite_eligible,
                        &uses,
                        &mut lifetimes,
                    );
                }
            }
            remove_allocation_homes(&mut active_allocations, &extra_write_homes, facts);
        }

        // Copying the active value back into its own home leaves the same GC root in place.
        // Record the new SSA name as another alias so a later logical read can prove that the
        // physical home was not the value's only surviving root.
        if same_value_in_target_home {
            active
                .get_mut(&slot)
                .expect("same-home active call root must exist")
                .aliases
                .insert(temp);
            continue;
        }

        if let Some(root) = active.remove(&slot) {
            record_call_root_overwrite(
                root,
                index,
                slot,
                overwrite_eligible,
                &uses,
                &mut lifetimes,
            );
        }

        if let HirExpr::TempRef(source) = value {
            for root in active.values_mut() {
                if root.aliases.contains(source) {
                    root.aliases.insert(temp);
                }
            }
            continue;
        }

        if producer_eligible && matches!(value, HirExpr::Call(_)) {
            active.insert(
                slot,
                ActiveCallRoot {
                    root_index: index,
                    aliases: BTreeSet::from([temp]),
                    observed: false,
                },
            );
        }
    }

    lifetimes
}

/// 只识别与显式 `collectgarbage` 相关的 lookup 物理 root。
///
/// Call 的观察、allocation owner 与相邻 overwrite 合同保持在既有 collector 中；这里不把
/// 普通 lookup 一概提升为 source local。标量与无求值 multi-nil 只按同 home 精确配对；
/// 无 overwrite 的 block-end 路径仍有下方标出的终止事实缺陷，不能视为已完成证明。
pub(super) fn collect_lookup_gc_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    mut temp_is_eligible: impl FnMut(TempId) -> bool,
) -> LookupGcRootLifetimeIndices {
    let uses = TempUseEvents::new(stmts);
    if uses.gc_fence_indices.is_empty() {
        return LookupGcRootLifetimeIndices::default();
    }
    let mut active = BTreeMap::<HomeSlotKey, ActiveLookupGcHome>::new();
    let mut value_by_temp = BTreeMap::<TempId, LookupValueId>::new();
    let mut next_value_id = 0;
    let mut lifetimes = LookupGcRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        if uses.is_gc_fence(index) {
            for root in active.values_mut() {
                root.crossed_gc_fence = true;
            }
        }

        let Some((temp, value)) = scalar_temp_definition(stmt) else {
            if matches!(stmt, HirStmt::Return(_)) {
                preserve_lookup_roots_to_scope_end(&active, &mut lifetimes);
                active.clear();
                value_by_temp.clear();
                continue;
            }
            if let Some(overwrites) =
                exact_multi_nil_temp_overwrites(stmt, facts, &mut temp_is_eligible)
            {
                for overwrite in &overwrites {
                    for temp in &overwrite.temps {
                        value_by_temp.remove(temp);
                        for root in active.values_mut() {
                            root.aliases.remove(temp);
                        }
                    }
                }
                for overwrite in overwrites {
                    if let Some(root) = active.remove(&overwrite.home) {
                        for alias in &root.aliases {
                            value_by_temp.remove(alias);
                        }
                        record_lookup_root_overwrite(
                            root,
                            index,
                            overwrite.home,
                            overwrite.eligible,
                            &uses,
                            facts,
                            &mut lifetimes,
                        );
                    }
                }
                continue;
            }
            if let Some(overwrite) =
                definite_gc_inert_branch_home_overwrite(stmt, facts, &mut temp_is_eligible, safety)
            {
                for temp in &overwrite.temps {
                    value_by_temp.remove(temp);
                    for root in active.values_mut() {
                        root.aliases.remove(temp);
                    }
                }
                if let Some(mut root) = active.remove(&overwrite.home) {
                    for alias in &root.aliases {
                        value_by_temp.remove(alias);
                    }
                    // The VM releases this lookup home on every arm before the later GC. Mark
                    // that future observation here; ordinary scalar/copy overwrites stay on the
                    // narrower crossed-fence contract to avoid materializing mechanical chains.
                    root.crossed_gc_fence |= uses.has_gc_fence_after(index);
                    record_lookup_root_overwrite(
                        root,
                        index,
                        overwrite.home,
                        overwrite.eligible,
                        &uses,
                        facts,
                        &mut lifetimes,
                    );
                }
                continue;
            }
            // 分析停用[ProofIncomplete]：非 GC-inert 分支覆盖会同时开始新的资源生命周期；
            // 当前 collector 没有结构化 successor root 状态，不能只登记旧 root 的终止 pair。
            // 分析停用[ProofIncomplete]：一般 parallel assignment 缺少各 RHS 求值与物理 target 提交顺序事实；当前只配对无 tail、全 trusted temp、RHS 全 nil 的无求值形状。
            let writes = StackWriteSummary::for_stmt(stmt, facts);
            if writes.has_boundary || writes.has_unknown_home {
                active.clear();
                value_by_temp.clear();
            } else {
                active.retain(|home, _| !writes.homes.contains(home));
                value_by_temp.retain(|temp, _| {
                    facts
                        .trusted_temp_home_slot(*temp)
                        .is_none_or(|home| !writes.homes.contains(&home))
                });
            }
            continue;
        };
        let Some(home) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            value_by_temp.clear();
            continue;
        };
        let eligible = temp_is_eligible(temp);
        let incoming_value = match value {
            HirExpr::TableAccess(_) => {
                let value_id = LookupValueId(next_value_id);
                next_value_id += 1;
                Some(value_id)
            }
            HirExpr::TempRef(source) => value_by_temp.get(source).copied(),
            _ => None,
        };
        let continues_same_home = incoming_value.is_some_and(|value_id| {
            active
                .get(&home)
                .is_some_and(|root| root.value_id == value_id)
        });
        for root in active.values_mut() {
            root.aliases.remove(&temp);
        }
        value_by_temp.remove(&temp);

        if continues_same_home {
            let root = active
                .get_mut(&home)
                .expect("same-home active lookup root must exist");
            root.aliases.insert(temp);
            root.eligible &= eligible;
            value_by_temp.insert(temp, root.value_id);
            continue;
        }

        if let Some(root) = active.remove(&home) {
            for alias in &root.aliases {
                value_by_temp.remove(alias);
            }
            record_lookup_root_overwrite(root, index, home, eligible, &uses, facts, &mut lifetimes);
        }

        if let Some(value_id) = incoming_value {
            value_by_temp.insert(temp, value_id);
            active.insert(
                home,
                ActiveLookupGcHome {
                    value_id,
                    root_index: index,
                    aliases: BTreeSet::from([temp]),
                    eligible,
                    crossed_gc_fence: false,
                },
            );
        }
    }

    preserve_lookup_roots_to_scope_end(&active, &mut lifetimes);
    lifetimes
}

fn record_lookup_root_overwrite(
    root: ActiveLookupGcHome,
    index: usize,
    home: HomeSlotKey,
    overwrite_is_eligible: bool,
    uses: &TempUseEvents,
    facts: &ProtoPromotionFacts,
    lifetimes: &mut LookupGcRootLifetimeIndices,
) {
    if root.crossed_gc_fence
        && root.eligible
        && overwrite_is_eligible
        && !root
            .aliases
            .iter()
            .filter(|alias| facts.trusted_temp_home_slot(**alias) == Some(home))
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        lifetimes.roots.insert(root.root_index);
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(LookupGcRootOverwritePair {
                root_index: root.root_index,
                home,
            });
    }
}

fn preserve_lookup_roots_to_scope_end(
    active: &BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    lifetimes: &mut LookupGcRootLifetimeIndices,
) {
    // 证明缺陷[PotentialUnsoundness:Lifetime]：普通 child block 末尾没有 stack-top/跨块 overwrite 事实；当前把它当 VM root 终点，物化后的词法生命周期可能早于或晚于真实 home 终点。
    lifetimes.roots.extend(
        active
            .values()
            .filter(|root| root.eligible && root.crossed_gc_fence)
            .map(|root| root.root_index),
    );
}

fn exact_multi_nil_temp_overwrites(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<Vec<ExactNilHomeOverwrite>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() < 2
        || assign.targets.len() != assign.values.fixed.len()
        || assign.values.tail.is_some()
        || !assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
    {
        return None;
    }
    let mut overwrites = BTreeMap::<HomeSlotKey, ExactNilHomeOverwrite>::new();
    for target in &assign.targets {
        let HirLValue::Temp(temp) = target else {
            return None;
        };
        let home = facts.trusted_temp_home_slot(*temp)?;
        let eligible = temp_is_eligible(*temp);
        let overwrite = overwrites
            .entry(home)
            .or_insert_with(|| ExactNilHomeOverwrite {
                temps: BTreeSet::new(),
                home,
                eligible: true,
            });
        overwrite.temps.insert(*temp);
        overwrite.eligible &= eligible;
    }
    // Literal nil 没有求值事件；同 home 的全部 target 是同一次物理覆盖事务，并共同
    // 承接相同的 nil 后态。资格按组取交集，避免只提升其中一部分 identity-sensitive temp。
    Some(overwrites.into_values().collect())
}

fn exact_multi_call_root_targets(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<Vec<ExactMultiCallRootTarget>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let tail = assign.values.tail.as_ref()?;
    if assign.targets.len() < 2
        || !assign.values.fixed.is_empty()
        || tail.exact_width() != Some(assign.targets.len())
        || !matches!(tail.as_expr(), HirExpr::Call(_))
    {
        return None;
    }

    let mut temp_homes = Vec::with_capacity(assign.targets.len());
    let mut distinct_homes = BTreeSet::new();
    for target in &assign.targets {
        let HirLValue::Temp(temp) = target else {
            return None;
        };
        let home = facts.trusted_temp_home_slot(*temp)?;
        if !distinct_homes.insert(home) {
            return None;
        }
        temp_homes.push((*temp, home));
    }

    if !temp_homes.iter().all(|(temp, _)| temp_is_eligible(*temp)) {
        return None;
    }

    Some(
        temp_homes
            .into_iter()
            .map(|(temp, home)| ExactMultiCallRootTarget { temp, home })
            .collect(),
    )
}

fn definite_gc_inert_branch_home_overwrite(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
    safety: HirExprSafety,
) -> Option<ExactBranchHomeOverwrite> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let else_block = if_stmt.else_block.as_ref()?;
    let (then_temp, then_value) = single_scalar_temp_write(&if_stmt.then_block)?;
    let (else_temp, else_value) = single_scalar_temp_write(else_block)?;
    if !safety.result_is_gc_inert(then_value) || !safety.result_is_gc_inert(else_value) {
        return None;
    }
    let then_home = facts.trusted_temp_home_slot(then_temp)?;
    let else_home = facts.trusted_temp_home_slot(else_temp)?;
    (then_home == else_home).then(|| ExactBranchHomeOverwrite {
        temps: BTreeSet::from([then_temp, else_temp]),
        home: then_home,
        eligible: temp_is_eligible(then_temp) && temp_is_eligible(else_temp),
    })
}

fn single_scalar_temp_write(block: &HirBlock) -> Option<(TempId, &HirExpr)> {
    let [HirStmt::Assign(assign)] = block.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Temp(temp)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((*temp, value))
}

fn stmt_is_transparent_temp_copy(stmt: &HirStmt, aliases: &BTreeSet<TempId>) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    matches!(
        (assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
        ([HirLValue::Temp(_)], [HirExpr::TempRef(source)], None)
            if aliases.contains(source)
    )
}

fn stmt_is_direct_if_control_read(stmt: &HirStmt, aliases: &BTreeSet<TempId>) -> bool {
    let HirStmt::If(if_stmt) = stmt else {
        return false;
    };
    if !stmt_consumes_temps_only_in_control_head(stmt, aliases) {
        return false;
    }
    match &if_stmt.cond {
        HirExpr::TempRef(temp) => aliases.contains(temp),
        HirExpr::Unary(unary) => {
            matches!(&unary.expr, HirExpr::TempRef(temp) if aliases.contains(temp))
        }
        _ => false,
    }
}

fn record_call_root_overwrite(
    root: ActiveCallRoot,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
    uses: &TempUseEvents,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    if eligible
        && root.observed
        && !root
            .aliases
            .iter()
            .any(|alias| uses.has_live_read_after(*alias, index))
    {
        lifetimes.roots.insert(root.root_index);
        lifetimes
            .root_homes
            .entry(root.root_index)
            .or_default()
            .insert(home);
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(CallRootOverwritePair {
                root_index: root.root_index,
                home,
            });
    }
}

fn preserve_active_call_roots(
    active: &mut BTreeMap<HomeSlotKey, ActiveCallRoot>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    for (home, root) in active.iter_mut() {
        // Any value still occupying its physical home while this statement may run user code
        // or GC is a root, even if ordinary value liveness ended after an earlier read.
        root.observed = true;
        lifetimes.roots.insert(root.root_index);
        lifetimes
            .root_homes
            .entry(root.root_index)
            .or_default()
            .insert(*home);
    }
}

fn stmt_may_observe_gc_roots(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let mut collector = GcRootObservationCollector {
        found: false,
        safety,
    };
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

struct GcRootObservationCollector {
    found: bool,
    safety: HirExprSafety,
}

impl HirVisitor for GcRootObservationCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::Close(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        // The shared discard-safety boundary already classifies dynamic environment/table
        // access, metamethod-capable operators, calls, and allocating expressions as eventful;
        // residual diagnostics stay conservative instead of being treated as executable no-ops.
        self.found |= !self.safety.is_discard_safe_without_residual(expr);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {
        // CallStmt exposes a HirCallExpr directly instead of wrapping it in HirExpr::Call.
        self.found = true;
    }
}

struct TempUseEvents {
    reads: BTreeMap<TempId, Vec<usize>>,
    reads_by_stmt: Vec<BTreeSet<TempId>>,
    writes: BTreeMap<TempId, Vec<usize>>,
    gc_fence_indices: BTreeSet<usize>,
}

impl TempUseEvents {
    fn new(stmts: &[HirStmt]) -> Self {
        let reads_by_stmt = collect_temp_reads_by_stmt(stmts);
        let mut reads = BTreeMap::<TempId, Vec<usize>>::new();
        for (index, temps) in reads_by_stmt.iter().enumerate() {
            for temp in temps {
                reads.entry(*temp).or_default().push(index);
            }
        }

        let mut writes = BTreeMap::<TempId, Vec<usize>>::new();
        for (index, stmt) in stmts.iter().enumerate() {
            let mut collector = TempWriteCollector::default();
            visit_stmts(std::slice::from_ref(stmt), &mut collector);
            for temp in collector.temps {
                writes.entry(temp).or_default().push(index);
            }
        }
        Self {
            reads,
            reads_by_stmt,
            writes,
            gc_fence_indices: collect_gc_fence_indices(stmts),
        }
    }

    fn has_live_read_after(&self, temp: TempId, index: usize) -> bool {
        let next_read = next_event_after(self.reads.get(&temp), index);
        let next_write = next_event_after(self.writes.get(&temp), index);
        next_read.is_some_and(|read| next_write.is_none_or(|write| read <= write))
    }

    fn reads_at(&self, index: usize) -> Option<&BTreeSet<TempId>> {
        self.reads_by_stmt.get(index)
    }

    fn has_gc_fence_after(&self, index: usize) -> bool {
        self.gc_fence_indices.range((index + 1)..).next().is_some()
    }

    fn is_gc_fence(&self, index: usize) -> bool {
        self.gc_fence_indices.contains(&index)
    }
}

pub(super) fn collect_gc_fence_indices(stmts: &[HirStmt]) -> BTreeSet<usize> {
    let mut temp_aliases = BTreeSet::new();
    let mut local_aliases = BTreeSet::new();
    let mut fences = BTreeSet::new();

    for (index, stmt) in stmts.iter().enumerate() {
        let mut visitor = GcFenceCollector {
            temp_aliases: &temp_aliases,
            local_aliases: &local_aliases,
            found: false,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut visitor);
        if visitor.found {
            fences.insert(index);
        }

        match stmt {
            HirStmt::Assign(assign) => {
                if let [target] = assign.targets.as_slice() {
                    match target {
                        HirLValue::Temp(temp) => {
                            temp_aliases.remove(temp);
                            if value_is_collectgarbage(&assign.values) {
                                temp_aliases.insert(*temp);
                            }
                        }
                        HirLValue::Local(local) => {
                            local_aliases.remove(local);
                            if value_is_collectgarbage(&assign.values) {
                                local_aliases.insert(*local);
                            }
                        }
                        _ => {}
                    }
                }
            }
            HirStmt::LocalDecl(decl) => {
                if let ([binding], [value], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    local_aliases.remove(binding);
                    if matches!(value, HirExpr::GlobalRef(global) if global.name == "collectgarbage")
                    {
                        local_aliases.insert(*binding);
                    }
                }
            }
            _ => {}
        }
    }
    fences
}

fn value_is_collectgarbage(values: &crate::hir::common::HirValuePack) -> bool {
    matches!(
        (values.fixed.as_slice(), &values.tail),
        ([HirExpr::GlobalRef(global)], None) if global.name == "collectgarbage"
    )
}

struct GcFenceCollector<'a> {
    temp_aliases: &'a BTreeSet<TempId>,
    local_aliases: &'a BTreeSet<LocalId>,
    found: bool,
}

impl HirVisitor for GcFenceCollector<'_> {
    fn visit_call(&mut self, call: &HirCallExpr) {
        self.found |= matches!(
            &call.callee,
            HirExpr::GlobalRef(global) if global.name == "collectgarbage"
        ) || matches!(&call.callee, HirExpr::TempRef(temp) if self.temp_aliases.contains(temp))
            || matches!(&call.callee, HirExpr::LocalRef(local) if self.local_aliases.contains(local));
    }
}

fn next_event_after(events: Option<&Vec<usize>>, index: usize) -> Option<usize> {
    let events = events?;
    events
        .get(events.partition_point(|event| *event <= index))
        .copied()
}

#[derive(Default)]
struct TempWriteCollector {
    temps: BTreeSet<TempId>,
}

impl HirVisitor for TempWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Temp(temp) = lvalue {
            self.temps.insert(*temp);
        }
    }
}

fn forget_written_known_nil_temps(stmt: &HirStmt, known_nil_temps: &mut BTreeSet<TempId>) {
    let mut collector = TempWriteCollector::default();
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    for temp in collector.temps {
        known_nil_temps.remove(&temp);
    }
}

fn scalar_temp_definition(stmt: &HirStmt) -> Option<(TempId, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::Temp(temp)] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    assign.values.tail.is_none().then_some((*temp, value))
}

fn direct_table_assignment_temps(stmt: &HirStmt) -> BTreeSet<TempId> {
    let HirStmt::Assign(assign) = stmt else {
        return BTreeSet::new();
    };
    if !assign
        .targets
        .iter()
        .any(|target| matches!(target, HirLValue::TableAccess(_)))
    {
        return BTreeSet::new();
    }
    assign
        .values
        .fixed
        .iter()
        .filter_map(|value| match value {
            HirExpr::TempRef(temp) => Some(*temp),
            _ => None,
        })
        .collect()
}

struct AllocationRootState<'a> {
    active: &'a mut Vec<ActiveAllocationRoot>,
    lifetimes: &'a mut CallRootLifetimeIndices,
    uses: &'a TempUseEvents,
    facts: &'a ProtoPromotionFacts,
}

fn update_allocation_roots(
    state: &mut AllocationRootState<'_>,
    index: usize,
    temp: TempId,
    value: &HirExpr,
    value_is_known_nil: bool,
    slot: HomeSlotKey,
    eligible: bool,
) {
    let source_root = match value {
        HirExpr::TempRef(source) => state
            .active
            .iter()
            .position(|root| root.aliases.contains(source)),
        _ => None,
    };

    for (root_index, root) in state.active.iter_mut().enumerate() {
        if source_root == Some(root_index) {
            // A scalar copy creates another physical root for the same allocation. The target
            // may be a different register; keep both homes until a later write clears one.
            root.aliases.insert(temp);
            root.homes.insert(slot);
            root.def_indices.insert(index);
            root.eligible &= eligible;
            continue;
        }

        root.aliases.remove(&temp);
        if root.homes.remove(&slot) {
            if value_is_known_nil {
                record_allocation_root_overwrite(
                    root,
                    index,
                    slot,
                    eligible,
                    state.uses,
                    state.lifetimes,
                );
            }
            root.aliases.retain(|alias| {
                state
                    .facts
                    .trusted_temp_home_slot(*alias)
                    .is_none_or(|alias_slot| alias_slot != slot)
            });
        }
    }

    state.active.retain(|root| !root.homes.is_empty());

    if eligible && matches!(value, HirExpr::TableConstructor(_)) {
        state.active.push(ActiveAllocationRoot {
            root_index: index,
            aliases: BTreeSet::from([temp]),
            homes: BTreeSet::from([slot]),
            def_indices: BTreeSet::from([index]),
            escaped: false,
            eligible,
        });
    }
}

fn terminate_allocation_home(
    active: &mut Vec<ActiveAllocationRoot>,
    lifetimes: &mut CallRootLifetimeIndices,
    uses: &TempUseEvents,
    facts: &ProtoPromotionFacts,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
) {
    // Caller has already proved every branch arm writes a GC-inert value, so this overwrite
    // terminates the old allocation root without starting an untracked collectable owner.
    for root in active.iter_mut() {
        if root.homes.remove(&home) {
            record_allocation_root_overwrite(root, index, home, eligible, uses, lifetimes);
            root.aliases.retain(|alias| {
                facts
                    .trusted_temp_home_slot(*alias)
                    .is_none_or(|alias_home| alias_home != home)
            });
        }
    }
    active.retain(|root| !root.homes.is_empty());
}

fn record_allocation_root_overwrite(
    root: &ActiveAllocationRoot,
    index: usize,
    home: HomeSlotKey,
    eligible: bool,
    uses: &TempUseEvents,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    if root.escaped
        && root.eligible
        && eligible
        && root
            .aliases
            .iter()
            .all(|alias| !uses.has_live_read_after(*alias, index))
    {
        lifetimes.roots.extend(root.def_indices.iter().copied());
        for def_index in &root.def_indices {
            lifetimes
                .root_by_protected
                .insert(*def_index, root.root_index);
        }
        lifetimes
            .roots_by_overwrite
            .entry(index)
            .or_default()
            .push(CallRootOverwritePair {
                root_index: root.root_index,
                home,
            });
    }
}

fn remove_allocation_homes(
    active: &mut Vec<ActiveAllocationRoot>,
    homes: &BTreeSet<HomeSlotKey>,
    facts: &ProtoPromotionFacts,
) {
    for root in active.iter_mut() {
        root.homes.retain(|home| !homes.contains(home));
        root.aliases.retain(|alias| {
            facts
                .trusted_temp_home_slot(*alias)
                .is_none_or(|home| !homes.contains(&home))
        });
    }
    active.retain(|root| !root.homes.is_empty());
}

struct StackWriteSummary {
    homes: BTreeSet<HomeSlotKey>,
    has_unknown_home: bool,
    has_boundary: bool,
}

impl StackWriteSummary {
    fn for_stmt(stmt: &HirStmt, facts: &ProtoPromotionFacts) -> Self {
        let mut summary = Self {
            homes: BTreeSet::new(),
            has_unknown_home: false,
            has_boundary: false,
        };
        let mut collector = StackWriteCollector {
            facts,
            summary: &mut summary,
        };
        visit_stmts(std::slice::from_ref(stmt), &mut collector);
        summary
    }

    fn note_home(&mut self, home: Option<HomeSlotKey>) {
        match home {
            Some(home) => {
                self.homes.insert(home);
            }
            None => self.has_unknown_home = true,
        }
    }
}

struct StackWriteCollector<'a> {
    facts: &'a ProtoPromotionFacts,
    summary: &'a mut StackWriteSummary,
}

impl HirVisitor for StackWriteCollector<'_> {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(local_decl) => {
                for local in &local_decl.bindings {
                    self.note_local(*local);
                }
            }
            HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => self.summary.has_boundary = true,
            _ => {}
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if matches!(expr, HirExpr::Decision(_) | HirExpr::Unresolved(_)) {
            self.summary.has_boundary = true;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        match lvalue {
            HirLValue::Param(param) => self.note_param(*param),
            HirLValue::Temp(temp) => self.summary.note_home(self.facts.home_slot(*temp)),
            HirLValue::Local(local) => self.note_local(*local),
            HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => {}
        }
    }
}

impl StackWriteCollector<'_> {
    fn note_param(&mut self, param: ParamId) {
        self.summary
            .note_home(self.facts.trusted_param_home_slot(param));
    }

    fn note_local(&mut self, local: LocalId) {
        self.summary
            .note_home(self.facts.trusted_local_home_slot(local));
    }
}
