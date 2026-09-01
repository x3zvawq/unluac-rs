//! 这个文件识别普通 HIR 值活跃性看不到的物理槽 root 生命周期。
//!
//! fixed call result（包括已物化 local）、已逃逸 table allocation，以及已跨后续观察点的
//! table/global lookup result，即使没有 HIR 读取，也会在同一 stack home 被覆盖前继续充当
//! VM GC root。
//! copy 共享值 identity，
//! 但每个目标 home 都是独立 root transaction；同一 parallel overwrite 可终止多个 home，
//! 消费者只能把 producer 与同 home 的精确覆盖配对。
//! 分析只在单个 block 内追踪；只有 nested structure 不写 active home，且没有 opaque transfer
//! 或 cleanup 边界时才允许穿过。消费者可以保留已配对的两次 materialization，也可以在
//! 更窄的改写仍保持同一覆盖事务时，连同 owner 已证明的 physical home 一起消费该 pair。
//! 潜在求值事件与分支覆盖值的 GC 惰性统一消费入口按目标方言构造的表达式安全上下文。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{
    HirBinaryOpKind, HirBlock, HirCallExpr, HirExpr, HirLValue, HirStmt, HirUnaryOpKind, LocalId,
    ParamId, TempId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::temp_touch::{collect_temp_reads_by_stmt, stmt_consumes_temps_only_in_control_head};
use super::visit::{HirVisitor, visit_call, visit_expr, visit_stmts};

struct ActiveCallRoot {
    value_id: CallValueId,
    root_index: usize,
    aliases: BTreeSet<TempId>,
    observed: bool,
    explicit_fence_only: bool,
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct CallValueId(usize);

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct LookupValueId(usize);

struct ActiveLookupGcHome {
    value_id: LookupValueId,
    root_index: usize,
    aliases: BTreeSet<TempId>,
    eligible: bool,
    crossed_observation: bool,
    /// 该 home 由原始 lookup 写入；跨 home 的机械 copy 不是 return 后缀要保留的独立 owner。
    direct_lookup_home: bool,
    /// low CFG 已证明该原始 home 在观察事件后仍活到 frame end。
    scope_end_copy_root: bool,
    /// 所有动态路径都到 frame end，不需要同步提交更早的 overwrite endpoint。
    pure_scope_end_copy_root: bool,
    /// 该 identity 来自 GlobalRef；当前只消费 pure scope-end low proof，不扩张旧的
    /// TableAccess overwrite matcher。
    global_lookup: bool,
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

struct ExactHomeOverwrite {
    temps: BTreeSet<TempId>,
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
    handoff_roots: BTreeSet<TempId>,
}

/// 收集已经物化成 HIR local、但在最后一次显式读取后仍跨过潜在用户代码/GC 事件的
/// fixed call result。
///
/// 当前或后续语句仍有同一 value epoch 的读取时，已有 binding/use owner 会保留该 local；
/// 这里专门补足最后一次读取已经结束、但物理槽仍保活的后缀。这样不会阻断安全的
/// `local x = a:m(); x:n()` 链化，而 `local x = a:m(); x:n(); side()` 会保留词法 root。
pub(super) fn collect_call_result_local_roots(
    stmts: &[HirStmt],
    trailing_condition: Option<&HirExpr>,
    safety: HirExprSafety,
) -> BTreeSet<LocalId> {
    let uses = LocalUseEvents::new(stmts, trailing_condition);
    let explicit_fences = collect_gc_fence_indices(stmts);
    let mut active = BTreeSet::<LocalId>::new();
    let mut roots = BTreeSet::<LocalId>::new();

    for (index, stmt) in stmts.iter().enumerate() {
        if explicit_fences.contains(&index) {
            // 显式 GC 是强观察点；沿用既有合同，不依赖后续源码读取来证明 root。
            roots.extend(active.iter().copied());
        } else if stmt_may_observe_gc_roots(stmt, safety) {
            roots.extend(
                active
                    .iter()
                    .copied()
                    .filter(|local| !uses.has_live_read_from(*local, index)),
            );
        }

        match stmt {
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::Local(local) = target {
                        active.remove(local);
                    }
                }
                if let ([HirLValue::Local(local)], [HirExpr::Call(_)], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) {
                    active.insert(*local);
                }
            }
            HirStmt::LocalDecl(decl) => {
                for local in &decl.bindings {
                    active.remove(local);
                }
                if let ([local], [HirExpr::Call(_)], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) {
                    active.insert(*local);
                }
            }
            _ => {}
        }
    }

    if trailing_condition.is_some_and(|condition| expr_may_observe_gc_roots(condition, safety)) {
        let condition_index = stmts.len();
        roots.extend(
            active
                .iter()
                .copied()
                .filter(|local| !uses.has_live_read_from(*local, condition_index)),
        );
    }

    roots
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
    pub(super) fn into_handoff_roots(self) -> BTreeSet<TempId> {
        self.handoff_roots
    }

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
    let mut next_call_value_id = 0;
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
            observe_active_call_values(&mut active, None);
        }
        let reads = uses.reads_at(index);
        let read_observations = active
            .iter()
            .filter(|(_, root)| {
                reads.is_some_and(|reads| root.aliases.iter().any(|temp| reads.contains(temp)))
            })
            .filter_map(|(home, root)| {
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
                let current_read_is_gc_inert_grouped_overwrite =
                    !stmt_may_observe_gc_roots(stmt, safety) && {
                        let mut every_temp_is_eligible = |_| true;
                        definite_grouped_home_overwrite(
                            stmt,
                            *home,
                            facts,
                            &mut every_temp_is_eligible,
                        )
                        .is_some()
                    };
                ((!is_loop_control
                    && !stmt_is_direct_if_control_read(stmt, &root.aliases)
                    && !stmt_is_transparent_temp_copy(stmt, &root.aliases)
                    && !current_read_is_gc_inert_grouped_overwrite)
                    || uses.has_gc_fence_after(index))
                .then_some(root.value_id)
            })
            .collect::<BTreeSet<_>>();
        observe_active_call_values(&mut active, Some(&read_observations));
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
                    let value_id = CallValueId(next_call_value_id);
                    next_call_value_id += 1;
                    active.insert(
                        target.home,
                        ActiveCallRoot {
                            value_id,
                            root_index: index,
                            aliases: BTreeSet::from([target.temp]),
                            observed: false,
                            explicit_fence_only: false,
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
                            home,
                            eligible,
                        );
                    }
                }
                continue;
            }
            let mut proven_homes = BTreeSet::new();
            let active_homes = active
                .keys()
                .copied()
                .chain(
                    active_allocations
                        .iter()
                        .flat_map(|root| root.homes.iter().copied()),
                )
                .collect::<BTreeSet<_>>();
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, &active_homes);
            for home in active_homes {
                if !grouped_assignment_is_complete {
                    break;
                }
                let Some(overwrite) = definite_grouped_home_overwrite(
                    stmt,
                    home,
                    facts,
                    &mut overwrite_temp_is_eligible,
                ) else {
                    continue;
                };
                proven_homes.insert(home);
                let active_root_is_read = active.get(&home).is_some_and(|root| {
                    reads
                        .is_some_and(|reads| root.aliases.iter().any(|alias| reads.contains(alias)))
                });
                for temp in &overwrite.temps {
                    for root in active.values_mut() {
                        root.aliases.remove(temp);
                    }
                }
                if let Some(root) = active.remove(&home)
                    && !active_root_is_read
                {
                    record_call_root_overwrite(
                        root,
                        index,
                        home,
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
                    home,
                    overwrite.eligible,
                );
            }
            let mut writes = StackWriteSummary::for_stmt(stmt, facts);
            writes.homes.retain(|home| !proven_homes.contains(home));
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
            let copied_value_id = active
                .values()
                .find(|root| root.aliases.contains(source))
                .map(|root| root.value_id);
            if let Some(value_id) = copied_value_id {
                let copied_root_aliases = active
                    .values()
                    .filter(|root| root.value_id == value_id)
                    .flat_map(|root| root.aliases.iter().copied())
                    .chain(std::iter::once(temp))
                    .collect::<BTreeSet<_>>();
                for root in active.values_mut() {
                    if root.value_id == value_id {
                        root.aliases.insert(temp);
                    }
                }
                if !producer_eligible {
                    continue;
                }
                // A cross-home copy starts an independent physical root transaction. The
                // source home can be overwritten before a later GC fence while this target
                // home still retains the call result, so alias propagation alone is not enough.
                active.insert(
                    slot,
                    ActiveCallRoot {
                        value_id,
                        root_index: index,
                        aliases: copied_root_aliases,
                        observed: false,
                        // Transparent compiler forwarding can normally be reconstructed inside
                        // its consuming expression. Only an explicit collection fence proves
                        // that the otherwise unread target home needs a standalone source owner.
                        explicit_fence_only: true,
                    },
                );
            }
            continue;
        }

        if producer_eligible && matches!(value, HirExpr::Call(_)) {
            let value_id = CallValueId(next_call_value_id);
            next_call_value_id += 1;
            active.insert(
                slot,
                ActiveCallRoot {
                    value_id,
                    root_index: index,
                    aliases: BTreeSet::from([temp]),
                    observed: false,
                    explicit_fence_only: false,
                },
            );
        }
    }

    lifetimes
}

/// 识别跨后续用户代码/GC 事件，或 return 表达式内部后续事件的 lookup 物理 root。
///
/// Call 的观察、allocation owner 与相邻 overwrite 合同保持在既有 collector 中；这里不把
/// 普通 lookup 一概提升为 source local。GlobalRef 只在 low CFG 已经证明所有路径都活到 scope
/// end，且 HIR 的最后一次 identity 读取后仍有观察点时，才需要独立物化；TableAccess 的标量
/// 与无求值 multi-nil 仍沿既有同-home 精确配对。没有可见 overwrite 时，跨过显式 GC/普通
/// 用户事件，或在 return 子表达式中先被消费、随后又跨过用户事件的 lookup，由当前 HIR
/// block 的词法 local 保活到 block end。block 外的 successor 不属于该 local 的可见区间，
/// 因此无需猜测跨块 home 复用。
pub(super) fn collect_lookup_gc_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    safety: HirExprSafety,
    mut temp_is_eligible: impl FnMut(TempId) -> bool,
) -> LookupGcRootLifetimeIndices {
    let uses = TempUseEvents::new(stmts);
    if uses.gc_fence_indices.is_empty()
        && !stmts.iter().any(|stmt| matches!(stmt, HirStmt::Return(_)))
    {
        return LookupGcRootLifetimeIndices::default();
    }
    let definitions = stmts
        .iter()
        .filter_map(scalar_temp_definition)
        .collect::<BTreeMap<_, _>>();
    let reference_captured_temps = super::mention::stmts_reference_captured_bindings(stmts).temps;
    let mut active = BTreeMap::<HomeSlotKey, ActiveLookupGcHome>::new();
    let mut value_by_temp = BTreeMap::<TempId, LookupValueId>::new();
    let mut global_lookup_values = BTreeSet::<LookupValueId>::new();
    let mut next_value_id = 0;
    let mut lifetimes = LookupGcRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        let live_read_values = value_by_temp
            .iter()
            .filter(|(temp, _)| uses.has_live_read_from(**temp, index))
            .map(|(_, value)| *value)
            .collect::<BTreeSet<_>>();
        if uses.is_gc_fence(index) {
            for root in active.values_mut() {
                if (!root.global_lookup || root.pure_scope_end_copy_root)
                    && !live_read_values.contains(&root.value_id)
                {
                    root.crossed_observation = true;
                }
            }
        } else if stmt_may_observe_gc_roots(stmt, safety) {
            for root in active.values_mut() {
                if root.pure_scope_end_copy_root && !live_read_values.contains(&root.value_id) {
                    root.crossed_observation = true;
                }
            }
        }

        let Some((temp, value)) = scalar_temp_definition(stmt) else {
            if let HirStmt::Return(return_stmt) = stmt {
                observe_lookup_return_post_use_roots(
                    &return_stmt.values,
                    &definitions,
                    &value_by_temp,
                    &mut active,
                    safety,
                );
                preserve_lookup_roots_to_scope_end(&active, &mut lifetimes);
                active.clear();
                value_by_temp.clear();
                continue;
            }
            if let HirStmt::ErrNil(err_nil) = stmt
                && let HirExpr::TempRef(temp) = &err_nil.value
                && let Some(value_id) = value_by_temp.remove(temp)
            {
                // ERRNNIL 的正常后继已经证明该 lookup 结果为 nil；它不再可能承担 GC root。
                // 只终止同一 value identity，不能把同时活跃的其它 home 一并清空。
                active.retain(|_, root| root.value_id != value_id);
                value_by_temp.retain(|_, value| *value != value_id);
                continue;
            }
            if let Some((value_id, handoff_root)) = nil_guarded_global_lookup_handoff(
                index,
                stmt,
                &active,
                &value_by_temp,
                &reference_captured_temps,
                &uses,
                facts,
            ) {
                // `source ~= nil` 的分支已经先把同一 identity 交给另一个 reference-captured
                // physical home；另一路 source 为 nil，本来就没有待保活对象。原 lookup
                // home 因而不再是后续观察点所需的独立 root。这个证明必须留在 HIR：AST
                // 只会看到两个 local，无法恢复分支对应的 VM home 事务（regress_36）。
                active.retain(|_, root| root.value_id != value_id);
                value_by_temp.retain(|_, value| *value != value_id);
                lifetimes.handoff_roots.insert(handoff_root);
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
            let mut proven_homes = BTreeSet::new();
            let active_homes = active.keys().copied().collect::<Vec<_>>();
            let active_home_set = active_homes.iter().copied().collect::<BTreeSet<_>>();
            let grouped_assignment_is_complete =
                grouped_assignment_targets_are_active(stmt, facts, &active_home_set);
            for home in active_homes {
                if !grouped_assignment_is_complete {
                    break;
                }
                let Some(overwrite) =
                    definite_grouped_home_overwrite(stmt, home, facts, &mut temp_is_eligible)
                else {
                    continue;
                };
                proven_homes.insert(home);
                for temp in &overwrite.temps {
                    value_by_temp.remove(temp);
                    for root in active.values_mut() {
                        root.aliases.remove(temp);
                    }
                }
                let Some(mut root) = active.remove(&home) else {
                    continue;
                };
                for alias in &root.aliases {
                    value_by_temp.remove(alias);
                }
                // Grouped assignment evaluates every RHS and branch/block prefix while the old
                // physical home is still owned by this local. Each proven path then commits a
                // target for the same home, so the old lookup can terminate at this statement.
                root.crossed_observation |= uses.has_gc_fence_after(index);
                record_lookup_root_overwrite(
                    root,
                    index,
                    home,
                    overwrite.eligible,
                    &uses,
                    facts,
                    &mut lifetimes,
                );
            }
            let mut writes = StackWriteSummary::for_stmt(stmt, facts);
            writes.homes.retain(|home| !proven_homes.contains(home));
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
            HirExpr::GlobalRef(_) if facts.is_pure_scope_end_copy_root_temp(temp) => {
                let value_id = LookupValueId(next_value_id);
                next_value_id += 1;
                global_lookup_values.insert(value_id);
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
                    crossed_observation: false,
                    direct_lookup_home: matches!(
                        value,
                        HirExpr::TableAccess(_) | HirExpr::GlobalRef(_)
                    ),
                    scope_end_copy_root: facts.is_scope_end_copy_root_temp(temp),
                    pure_scope_end_copy_root: facts.is_pure_scope_end_copy_root_temp(temp),
                    global_lookup: global_lookup_values.contains(&value_id),
                },
            );
        }
    }

    preserve_lookup_roots_to_scope_end(&active, &mut lifetimes);
    lifetimes
}

/// 识别 nil fallback 前缀里的条件 root handoff。
///
/// 只接受 `lookup ~= nil` 一侧在任何潜在观察前，以纯 copy 把同一 identity 写入另一个
/// physical home；该 target 必须在 join 后仍以同一 trusted home 被 reference capture，因而
/// 不能作为 dead temp 消失。nil 一侧不需要 root；non-nil 一侧把 PhysicalRoot provenance
/// 转交给这个 join owner。普通 callee copy 没有 capture owner，因此不会把
/// `global; copy; call; gc` 错认成 handoff（regress_419）。
fn nil_guarded_global_lookup_handoff(
    index: usize,
    stmt: &HirStmt,
    active: &BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    value_by_temp: &BTreeMap<TempId, LookupValueId>,
    reference_captured_temps: &BTreeSet<TempId>,
    uses: &TempUseEvents,
    facts: &ProtoPromotionFacts,
) -> Option<(LookupValueId, TempId)> {
    let HirStmt::If(if_stmt) = stmt else {
        return None;
    };
    let (checked_temp, non_nil_block) = match &if_stmt.cond {
        HirExpr::Binary(binary) if binary.op == HirBinaryOpKind::Eq => {
            let temp = nil_compared_temp(&binary.lhs, &binary.rhs)?;
            (temp, if_stmt.else_block.as_ref()?)
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            let HirExpr::Binary(binary) = &unary.expr else {
                return None;
            };
            if binary.op != HirBinaryOpKind::Eq {
                return None;
            }
            let temp = nil_compared_temp(&binary.lhs, &binary.rhs)?;
            (temp, &if_stmt.then_block)
        }
        _ => return None,
    };
    let value_id = value_by_temp.get(&checked_temp).copied()?;
    let (root_home, _) = active.iter().find(|(_, root)| {
        root.value_id == value_id
            && root.direct_lookup_home
            && root.global_lookup
            && root.pure_scope_end_copy_root
    })?;

    let mut aliases = value_by_temp
        .iter()
        .filter_map(|(temp, value)| (*value == value_id).then_some(*temp))
        .collect::<BTreeSet<_>>();
    let mut handoff_owner = None;
    for branch_stmt in &non_nil_block.stmts {
        let (target, value) = scalar_temp_definition(branch_stmt)?;
        let HirExpr::TempRef(source) = value else {
            return None;
        };
        if !aliases.contains(source) {
            return None;
        }
        aliases.insert(target);
        let target_home = facts.trusted_temp_home_slot(target)?;
        if reference_captured_temps.contains(&target)
            && uses.has_live_read_after(target, index)
            && target_home != *root_home
        {
            handoff_owner = Some(target);
        }
    }
    handoff_owner.map(|owner| (value_id, owner))
}

fn nil_compared_temp(lhs: &HirExpr, rhs: &HirExpr) -> Option<TempId> {
    match (lhs, rhs) {
        (HirExpr::TempRef(temp), HirExpr::Nil) | (HirExpr::Nil, HirExpr::TempRef(temp)) => {
            Some(*temp)
        }
        _ => None,
    }
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
    if !root.global_lookup
        && root.crossed_observation
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
    // collector 按 HirBlock 独立运行，locals pass 也把 producer 提升为同一 block 内的词法
    // local。active 说明本 block 内没有已证明的同-home overwrite；一旦离开 block，源码
    // local 的作用域自然终止，所以无需也不能把 parent successor 的 home 复用算进这里。
    // regress_396 覆盖 child-if 后立即复用该 home 的边界。
    lifetimes.roots.extend(
        active
            .values()
            .filter(|root| {
                root.eligible
                    && root.crossed_observation
                    && (!root.global_lookup || root.pure_scope_end_copy_root)
            })
            .map(|root| root.root_index),
    );
}

/// 将 return 表达式里“值已经被子表达式消费、随后仍跨过潜在用户代码/GC 事件”的
/// lookup transaction 转成显式 root 观察事实。
///
/// 普通二元/一元/call 的当前 operands 在 operator/call 执行期间仍由表达式临时槽持有；
/// 因此当前节点自身的事件只要求保留更早已经消费的 lookup identity。逻辑短路、
/// constructor、closure 与 Decision 另有条件执行或强引用 handoff，当前证明不跨层猜测。
fn observe_lookup_return_post_use_roots(
    values: &crate::hir::common::HirValuePack,
    definitions: &BTreeMap<TempId, &HirExpr>,
    value_by_temp: &BTreeMap<TempId, LookupValueId>,
    active: &mut BTreeMap<HomeSlotKey, ActiveLookupGcHome>,
    safety: HirExprSafety,
) {
    let mut resolving = BTreeSet::new();
    let Some(flow) = values
        .iter()
        .try_fold(ReturnLookupFlow::default(), |flow, value| {
            Some(flow.then(return_lookup_flow(
                value,
                definitions,
                value_by_temp,
                safety,
                &mut resolving,
            )?))
        })
    else {
        return;
    };

    for root in active.values_mut() {
        if root.direct_lookup_home
            && root.scope_end_copy_root
            && flow.needs_independent_root.contains(&root.value_id)
        {
            root.crossed_observation = true;
        }
    }
}

#[derive(Default)]
struct ReturnLookupFlow {
    handed_roots: BTreeSet<LookupValueId>,
    released_roots: BTreeSet<LookupValueId>,
    needs_independent_root: BTreeSet<LookupValueId>,
    has_observation: bool,
}

impl ReturnLookupFlow {
    fn lookup(value: LookupValueId) -> Self {
        Self {
            handed_roots: BTreeSet::from([value]),
            ..Self::default()
        }
    }

    fn observation() -> Self {
        Self {
            has_observation: true,
            ..Self::default()
        }
    }

    fn then(mut self, next: Self) -> Self {
        if next.has_observation {
            self.needs_independent_root
                .extend(self.released_roots.iter().copied());
        }
        self.handed_roots.extend(next.handed_roots);
        self.released_roots.extend(next.released_roots);
        self.needs_independent_root
            .extend(next.needs_independent_root);
        self.has_observation |= next.has_observation;
        self
    }

    fn consume_result(mut self, observes: bool) -> Self {
        if observes {
            self.needs_independent_root
                .extend(self.released_roots.iter().copied());
            self.has_observation = true;
        }
        self.released_roots
            .extend(std::mem::take(&mut self.handed_roots));
        self
    }
}

fn return_lookup_flow(
    expr: &HirExpr,
    definitions: &BTreeMap<TempId, &HirExpr>,
    value_by_temp: &BTreeMap<TempId, LookupValueId>,
    safety: HirExprSafety,
    resolving: &mut BTreeSet<TempId>,
) -> Option<ReturnLookupFlow> {
    match expr {
        HirExpr::TempRef(temp) => {
            if let Some(value) = value_by_temp.get(temp).copied() {
                return Some(ReturnLookupFlow::lookup(value));
            }
            let value = definitions.get(temp).copied()?;
            if !resolving.insert(*temp) {
                return None;
            }
            let flow = return_lookup_flow(value, definitions, value_by_temp, safety, resolving);
            resolving.remove(temp);
            flow
        }
        HirExpr::GlobalRef(_) => Some(ReturnLookupFlow::observation()),
        HirExpr::TableAccess(access) => Some(
            return_lookup_flow(&access.base, definitions, value_by_temp, safety, resolving)?
                .then(return_lookup_flow(
                    &access.key,
                    definitions,
                    value_by_temp,
                    safety,
                    resolving,
                )?)
                .consume_result(true),
        ),
        HirExpr::Unary(unary) => Some(
            return_lookup_flow(&unary.expr, definitions, value_by_temp, safety, resolving)?
                .consume_result(safety.unary_operator_may_observe_gc_roots(unary.op)),
        ),
        HirExpr::Binary(binary) => Some(
            return_lookup_flow(&binary.lhs, definitions, value_by_temp, safety, resolving)?
                .then(return_lookup_flow(
                    &binary.rhs,
                    definitions,
                    value_by_temp,
                    safety,
                    resolving,
                )?)
                .consume_result(safety.binary_operator_may_observe_gc_roots(
                    binary.op,
                    &binary.lhs,
                    &binary.rhs,
                )),
        ),
        HirExpr::Call(call) => {
            let flow = call.args.iter().try_fold(
                return_lookup_flow(&call.callee, definitions, value_by_temp, safety, resolving)?,
                |flow, arg| {
                    Some(flow.then(return_lookup_flow(
                        arg,
                        definitions,
                        value_by_temp,
                        safety,
                        resolving,
                    )?))
                },
            )?;
            Some(flow.consume_result(true))
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::Vector(_)
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::VarArg => Some(ReturnLookupFlow::default()),
        HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => None,
    }
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
        let possible_homes = facts.possible_temp_home_slots(*temp)?;
        if possible_homes.is_empty() {
            // Synthetic home-free targets participate in the HIR parallel assignment but do not
            // write a physical VM cell. They therefore cannot prevent the exact physical members
            // of the same nil transaction from closing their preceding root epochs.
            continue;
        }
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
    (!overwrites.is_empty()).then(|| overwrites.into_values().collect())
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

fn definite_grouped_home_overwrite(
    stmt: &HirStmt,
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    temp_is_eligible: &mut impl FnMut(TempId) -> bool,
) -> Option<ExactHomeOverwrite> {
    let temps = match stmt {
        HirStmt::Assign(assign) if assign.targets.len() > 1 => {
            let writes = StackWriteSummary::for_stmt(stmt, facts);
            if writes.has_boundary
                || writes.has_unknown_home
                || !writes.homes.contains(&home)
                || !assign.targets.iter().all(|target| {
                    matches!(target, HirLValue::Temp(temp) if facts.trusted_temp_home_slot(*temp).is_some())
                })
            {
                return None;
            }
            assign
                .targets
                .iter()
                .filter_map(|target| {
                    let HirLValue::Temp(temp) = target else {
                        return None;
                    };
                    (facts.trusted_temp_home_slot(*temp) == Some(home)).then_some(*temp)
                })
                .collect::<BTreeSet<_>>()
        }
        HirStmt::If(if_stmt) => {
            let else_block = if_stmt.else_block.as_ref()?;
            let then_temps = definite_block_home_overwrite(&if_stmt.then_block, home, facts)?;
            let else_temps = definite_block_home_overwrite(else_block, home, facts)?;
            then_temps.union(&else_temps).copied().collect()
        }
        HirStmt::Block(block) => definite_block_home_overwrite(block, home, facts)?,
        _ => return None,
    };
    if temps.is_empty() {
        return None;
    }
    let eligible = temps.iter().copied().all(temp_is_eligible);
    Some(ExactHomeOverwrite { temps, eligible })
}

fn grouped_assignment_targets_are_active(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    active_homes: &BTreeSet<HomeSlotKey>,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return true;
    };
    if assign.targets.len() <= 1 {
        return true;
    }
    let Some(target_homes) = assign
        .targets
        .iter()
        .map(|target| {
            let HirLValue::Temp(temp) = target else {
                return None;
            };
            facts.trusted_temp_home_slot(*temp)
        })
        .collect::<Option<BTreeSet<_>>>()
    else {
        return false;
    };
    target_homes.len() == assign.targets.len()
        && target_homes.iter().all(|home| active_homes.contains(home))
}

fn definite_block_home_overwrite(
    block: &HirBlock,
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> Option<BTreeSet<TempId>> {
    let (first_index, first_temp) = block.stmts.iter().enumerate().find_map(|(index, stmt)| {
        let (temp, _) = scalar_temp_write(stmt)?;
        (facts.trusted_temp_home_slot(temp) == Some(home)).then_some((index, temp))
    })?;
    if !stmts_preserve_home(&block.stmts[..first_index], home, facts)
        || !stmts_rewrite_home_only_through_scalar_temps(
            &block.stmts[(first_index + 1)..],
            home,
            facts,
        )
    {
        return None;
    }
    Some(BTreeSet::from([first_temp]))
}

fn scalar_temp_write(stmt: &HirStmt) -> Option<(TempId, &HirExpr)> {
    let HirStmt::Assign(assign) = stmt else {
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

fn stmts_preserve_home(stmts: &[HirStmt], home: HomeSlotKey, facts: &ProtoPromotionFacts) -> bool {
    let writes = StackWriteSummary::for_stmts(stmts, facts);
    !writes.has_boundary && !writes.has_unknown_home && !writes.homes.contains(&home)
}

fn stmts_rewrite_home_only_through_scalar_temps(
    stmts: &[HirStmt],
    home: HomeSlotKey,
    facts: &ProtoPromotionFacts,
) -> bool {
    stmts.iter().all(|stmt| {
        let writes = StackWriteSummary::for_stmt(stmt, facts);
        if writes.has_boundary || writes.has_unknown_home {
            return false;
        }
        !writes.homes.contains(&home)
            || scalar_temp_write(stmt)
                .is_some_and(|(temp, _)| facts.trusted_temp_home_slot(temp) == Some(home))
    })
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

pub(super) fn scope_end_copy_roots_needing_materialization(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
) -> BTreeSet<TempId> {
    let mut collector = ScopeEndRootCollector {
        roots: BTreeSet::new(),
        facts,
    };
    collector.collect_generic_producer_roots(stmts);
    visit_stmts(stmts, &mut collector);
    collector.roots
}

struct ScopeEndRootCollector<'a> {
    roots: BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
}

impl ScopeEndRootCollector<'_> {
    fn collect_generic_producer_roots(&mut self, stmts: &[HirStmt]) {
        let copy_sources = stmts
            .iter()
            .filter_map(|stmt| {
                let HirStmt::Assign(assign) = stmt else {
                    return None;
                };
                match (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) {
                    ([HirLValue::Temp(target)], [HirExpr::TempRef(source)], None) => {
                        Some((*target, *source))
                    }
                    _ => None,
                }
            })
            .collect::<BTreeMap<_, _>>();
        for (index, stmt) in stmts.iter().enumerate() {
            let HirStmt::Assign(assign) = stmt else {
                continue;
            };
            let Some(call) = assign.values.iter().find_map(|value| match value {
                HirExpr::Call(call) => Some(call.as_ref()),
                _ => None,
            }) else {
                continue;
            };
            let targets = assign
                .targets
                .iter()
                .filter_map(|target| match target {
                    HirLValue::Temp(temp) => Some(*temp),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            if targets.len() != assign.targets.len() {
                continue;
            }
            let mut generic_for = None;
            for next in stmts[index + 1..].iter().take(5) {
                match next {
                    HirStmt::Assign(_) => {}
                    HirStmt::GenericFor(owner) => {
                        generic_for = Some(owner.as_ref());
                        break;
                    }
                    _ => break,
                }
            }
            let Some(generic_for) = generic_for else {
                continue;
            };
            let consumed = targets.iter().all(|target| {
                generic_for
                    .iterator
                    .fixed
                    .iter()
                    .any(|value| matches!(value, HirExpr::TempRef(temp) if temp == target))
            });
            if !consumed {
                continue;
            }
            let mut refs = ScopeRootRefCollector {
                roots: &mut self.roots,
                facts: self.facts,
                copy_sources: &copy_sources,
            };
            visit_call(call, &mut refs);
        }
    }
}

struct ScopeRootRefCollector<'a> {
    roots: &'a mut BTreeSet<TempId>,
    facts: &'a ProtoPromotionFacts,
    copy_sources: &'a BTreeMap<TempId, TempId>,
}

impl HirVisitor for ScopeRootRefCollector<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        let HirExpr::TempRef(temp) = expr else {
            return;
        };
        let mut current = *temp;
        let mut seen = BTreeSet::new();
        while seen.insert(current) {
            if self.facts.is_scope_end_copy_root_temp(current) {
                self.roots.insert(current);
                break;
            }
            let Some(source) = self.copy_sources.get(&current).copied() else {
                break;
            };
            current = source;
        }
    }
}

impl HirVisitor for ScopeEndRootCollector<'_> {
    fn visit_block(&mut self, block: &HirBlock) {
        self.collect_generic_producer_roots(&block.stmts);
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::If(if_stmt) = stmt else {
            return;
        };
        let temp = match &if_stmt.cond {
            HirExpr::TempRef(temp) => Some(*temp),
            HirExpr::Unary(unary) => match &unary.expr {
                HirExpr::TempRef(temp) => Some(*temp),
                _ => None,
            },
            _ => None,
        };
        if let Some(temp) = temp
            && self.facts.is_scope_end_copy_root_temp(temp)
        {
            self.roots.insert(temp);
        }
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
    let representatives = active_call_value_representatives(active, None, true);
    for home in representatives.into_values() {
        let root = active
            .get_mut(&home)
            .expect("active call representative must retain its home");
        // One live home is enough to retain a shared result at this observation point. If that
        // home is overwritten, a later observation can select another still-active transaction.
        root.observed = true;
        lifetimes.roots.insert(root.root_index);
        lifetimes
            .root_homes
            .entry(root.root_index)
            .or_default()
            .insert(home);
    }
}

fn observe_active_call_values(
    active: &mut BTreeMap<HomeSlotKey, ActiveCallRoot>,
    values: Option<&BTreeSet<CallValueId>>,
) {
    let representatives = active_call_value_representatives(active, values, false);
    for home in representatives.into_values() {
        active
            .get_mut(&home)
            .expect("active call representative must retain its home")
            .observed = true;
    }
}

fn active_call_value_representatives(
    active: &BTreeMap<HomeSlotKey, ActiveCallRoot>,
    values: Option<&BTreeSet<CallValueId>>,
    include_explicit_fence_only: bool,
) -> BTreeMap<CallValueId, HomeSlotKey> {
    let mut representatives = BTreeMap::<CallValueId, HomeSlotKey>::new();
    for (home, root) in active {
        if (!include_explicit_fence_only && root.explicit_fence_only)
            || values.is_some_and(|values| !values.contains(&root.value_id))
        {
            continue;
        }
        representatives
            .entry(root.value_id)
            .and_modify(|representative_home| {
                let representative = active
                    .get(representative_home)
                    .expect("selected call representative must remain active");
                if root.observed && !representative.observed {
                    *representative_home = *home;
                }
            })
            .or_insert(*home);
    }
    representatives
}

pub(super) fn stmt_may_observe_gc_roots(stmt: &HirStmt, safety: HirExprSafety) -> bool {
    let mut collector = GcRootObservationCollector {
        found: false,
        safety,
    };
    visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.found
}

fn expr_may_observe_gc_roots(expr: &HirExpr, safety: HirExprSafety) -> bool {
    let mut collector = GcRootObservationCollector {
        found: false,
        safety,
    };
    visit_expr(expr, &mut collector);
    collector.found
}

struct LocalUseEvents {
    reads: BTreeMap<LocalId, Vec<usize>>,
    writes: BTreeMap<LocalId, Vec<usize>>,
}

impl LocalUseEvents {
    fn new(stmts: &[HirStmt], trailing_condition: Option<&HirExpr>) -> Self {
        let mut reads = BTreeMap::<LocalId, Vec<usize>>::new();
        let mut writes = BTreeMap::<LocalId, Vec<usize>>::new();
        for (index, stmt) in stmts.iter().enumerate() {
            let mut collector = LocalUseCollector::default();
            visit_stmts(std::slice::from_ref(stmt), &mut collector);
            for local in collector.reads {
                reads.entry(local).or_default().push(index);
            }
            for local in collector.writes {
                writes.entry(local).or_default().push(index);
            }
        }
        if let Some(condition) = trailing_condition {
            let mut collector = LocalUseCollector::default();
            visit_expr(condition, &mut collector);
            for local in collector.reads {
                reads.entry(local).or_default().push(stmts.len());
            }
        }
        Self { reads, writes }
    }

    fn has_live_read_from(&self, local: LocalId, index: usize) -> bool {
        let next_read = next_event_at_or_after(self.reads.get(&local), index);
        let next_write = next_event_at_or_after(self.writes.get(&local), index);
        next_read.is_some_and(|read| next_write.is_none_or(|write| read <= write))
    }
}

#[derive(Default)]
struct LocalUseCollector {
    reads: BTreeSet<LocalId>,
    writes: BTreeSet<LocalId>,
}

impl HirVisitor for LocalUseCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::LocalDecl(decl) = stmt {
            self.writes.extend(decl.bindings.iter().copied());
        }
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::LocalRef(local) = expr {
            self.reads.insert(*local);
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        if let HirLValue::Local(local) = lvalue {
            self.writes.insert(*local);
        }
    }
}

struct GcRootObservationCollector {
    found: bool,
    safety: HirExprSafety,
}

impl HirVisitor for GcRootObservationCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::GlobalDecl(_) | HirStmt::Close(_));
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

    fn has_live_read_from(&self, temp: TempId, index: usize) -> bool {
        let next_read = next_event_at_or_after(self.reads.get(&temp), index);
        let next_write = next_event_at_or_after(self.writes.get(&temp), index);
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

fn next_event_at_or_after(events: Option<&Vec<usize>>, index: usize) -> Option<usize> {
    let events = events?;
    events
        .get(events.partition_point(|event| *event < index))
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
            // Any scalar definition commits a new value to the trusted home after evaluating
            // its RHS. Literal nil is special only for nil-fact propagation above; a lookup,
            // primitive, or call is an equally exact end to the preceding allocation root.
            record_allocation_root_overwrite(
                root,
                index,
                slot,
                eligible,
                state.uses,
                state.lifetimes,
            );
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
    // The caller has proved that every path commits this home through targets which are mapped
    // to the old physical-root local. The successor value therefore remains owned by that same
    // local even when it is collectable; this helper only closes the preceding allocation epoch.
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
        Self::for_stmts(std::slice::from_ref(stmt), facts)
    }

    fn for_stmts(stmts: &[HirStmt], facts: &ProtoPromotionFacts) -> Self {
        let mut summary = Self {
            homes: BTreeSet::new(),
            has_unknown_home: false,
            has_boundary: false,
        };
        let mut collector = StackWriteCollector {
            facts,
            summary: &mut summary,
        };
        visit_stmts(stmts, &mut collector);
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
            | HirStmt::GlobalDecl(_)
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
