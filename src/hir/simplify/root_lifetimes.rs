//! Identify the narrow physical-slot lifetime that HIR value liveness misses.
//!
//! A fixed call result remains a VM GC root until the same stack home is overwritten, even when
//! no HIR expression reads that result. The analysis stays local to one block. Nested structure
//! may be crossed only when it has no write to the active home and no opaque transfer or cleanup
//! boundary. Consumers preserve both materializations in each proven pair.

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirCallExpr, HirExpr, HirLValue, HirStmt, LocalId, ParamId, TempId};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::temp_touch::{collect_temp_reads_by_stmt, stmt_consumes_temps_only_in_control_head};
use super::visit::{HirVisitor, visit_stmts};

struct ActiveCallRoot {
    root_index: usize,
    aliases: BTreeSet<TempId>,
    observed: bool,
}

struct ActiveAllocationRoot {
    root_index: usize,
    aliases: BTreeSet<TempId>,
    homes: BTreeSet<HomeSlotKey>,
    def_indices: BTreeSet<usize>,
    escaped: bool,
    eligible: bool,
}

#[derive(Default)]
pub(super) struct CallRootLifetimeIndices {
    roots: BTreeSet<usize>,
    root_by_overwrite: BTreeMap<usize, usize>,
    root_by_protected: BTreeMap<usize, usize>,
}

impl CallRootLifetimeIndices {
    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn root_for_overwrite(&self, index: usize) -> Option<usize> {
        self.root_by_overwrite.get(&index).copied()
    }

    pub(super) fn root_for_protected(&self, index: usize) -> Option<usize> {
        self.root_by_protected.get(&index).copied()
    }

    pub(super) fn marked_stmts(&self, stmt_count: usize) -> Vec<bool> {
        let mut marked = vec![false; stmt_count];
        for index in self.roots.iter().chain(self.root_by_overwrite.keys()) {
            marked[*index] = true;
        }
        marked
    }
}

pub(super) fn collect_call_root_lifetimes(
    stmts: &[HirStmt],
    facts: &ProtoPromotionFacts,
    mut temp_is_eligible: impl FnMut(TempId) -> bool,
) -> CallRootLifetimeIndices {
    let uses = TempUseEvents::new(stmts);
    let mut active = BTreeMap::<HomeSlotKey, ActiveCallRoot>::new();
    let mut active_allocations = Vec::<ActiveAllocationRoot>::new();
    let mut lifetimes = CallRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        if uses.is_gc_fence(index) {
            preserve_active_call_roots(&mut active, &mut lifetimes);
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
        let Some(slot) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            active_allocations.clear();
            continue;
        };

        let eligible = temp_is_eligible(temp);
        let mut allocation_state = AllocationRootState {
            active: &mut active_allocations,
            lifetimes: &mut lifetimes,
            uses: &uses,
            facts,
        };
        update_allocation_roots(&mut allocation_state, index, temp, value, slot, eligible);
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
                    record_call_root_overwrite(root, index, eligible, &uses, &mut lifetimes);
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
            record_call_root_overwrite(root, index, eligible, &uses, &mut lifetimes);
        }

        if let HirExpr::TempRef(source) = value {
            for root in active.values_mut() {
                if root.aliases.contains(source) {
                    root.aliases.insert(temp);
                }
            }
            continue;
        }

        if eligible && matches!(value, HirExpr::Call(_)) {
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
        lifetimes.root_by_overwrite.insert(index, root.root_index);
    }
}

fn preserve_active_call_roots(
    active: &mut BTreeMap<HomeSlotKey, ActiveCallRoot>,
    lifetimes: &mut CallRootLifetimeIndices,
) {
    for root in active.values_mut() {
        // Any value still occupying its physical home at an explicit collection point is a
        // root, even if ordinary value liveness ended after an earlier read.
        root.observed = true;
        lifetimes.roots.insert(root.root_index);
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
            if matches!(value, HirExpr::Nil)
                && root.escaped
                && root.eligible
                && eligible
                && root
                    .aliases
                    .iter()
                    .all(|alias| !state.uses.has_live_read_after(*alias, index))
            {
                state
                    .lifetimes
                    .roots
                    .extend(root.def_indices.iter().copied());
                for def_index in &root.def_indices {
                    state
                        .lifetimes
                        .root_by_protected
                        .insert(*def_index, root.root_index);
                }
                state
                    .lifetimes
                    .root_by_overwrite
                    .insert(index, root.root_index);
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
