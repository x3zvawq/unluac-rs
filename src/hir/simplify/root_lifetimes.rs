//! Identify the narrow physical-slot lifetime that HIR value liveness misses.
//!
//! A fixed call result remains a VM GC root until the same stack home is overwritten, even when
//! no HIR expression reads that result. The analysis stays local to one block. Nested structure
//! may be crossed only when it has no write to the active home and no opaque transfer or cleanup
//! boundary. Consumers preserve both materializations in each proven pair.

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, HirStmt, LocalId, ParamId, TempId};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

use super::temp_touch::collect_temp_reads_by_stmt;
use super::visit::{HirVisitor, visit_stmts};

struct ActiveCallRoot {
    root_index: usize,
    aliases: BTreeSet<TempId>,
}

#[derive(Default)]
pub(super) struct CallRootLifetimeIndices {
    roots: BTreeSet<usize>,
    root_by_overwrite: BTreeMap<usize, usize>,
}

impl CallRootLifetimeIndices {
    pub(super) fn is_root(&self, index: usize) -> bool {
        self.roots.contains(&index)
    }

    pub(super) fn root_for_overwrite(&self, index: usize) -> Option<usize> {
        self.root_by_overwrite.get(&index).copied()
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
    let mut lifetimes = CallRootLifetimeIndices::default();

    for (index, stmt) in stmts.iter().enumerate() {
        let Some((temp, value)) = scalar_temp_definition(stmt) else {
            let writes = StackWriteSummary::for_stmt(stmt, facts);
            if writes.has_boundary || writes.has_unknown_home {
                active.clear();
            } else {
                active.retain(|slot, _| !writes.homes.contains(slot));
                for root in active.values_mut() {
                    root.aliases.retain(|temp| {
                        facts
                            .trusted_temp_home_slot(*temp)
                            .is_none_or(|slot| !writes.homes.contains(&slot))
                    });
                }
            }
            continue;
        };
        let Some(slot) = facts.trusted_temp_home_slot(temp) else {
            active.clear();
            continue;
        };

        let eligible = temp_is_eligible(temp);
        let same_value_in_target_home = matches!(value, HirExpr::TempRef(source)
            if active
                .get(&slot)
                .is_some_and(|root| root.aliases.contains(source)));
        for root in active.values_mut() {
            root.aliases.remove(&temp);
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

        if let Some(root) = active.remove(&slot)
            && eligible
            && !root
                .aliases
                .iter()
                .any(|alias| uses.has_live_read_after(*alias, index))
        {
            lifetimes.roots.insert(root.root_index);
            lifetimes.root_by_overwrite.insert(index, root.root_index);
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
                },
            );
        }
    }

    lifetimes
}

struct TempUseEvents {
    reads: BTreeMap<TempId, Vec<usize>>,
    writes: BTreeMap<TempId, Vec<usize>>,
}

impl TempUseEvents {
    fn new(stmts: &[HirStmt]) -> Self {
        let mut reads = BTreeMap::<TempId, Vec<usize>>::new();
        for (index, temps) in collect_temp_reads_by_stmt(stmts).into_iter().enumerate() {
            for temp in temps {
                reads.entry(temp).or_default().push(index);
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
        Self { reads, writes }
    }

    fn has_live_read_after(&self, temp: TempId, index: usize) -> bool {
        let next_read = next_event_after(self.reads.get(&temp), index);
        let next_write = next_event_after(self.writes.get(&temp), index);
        next_read.is_some_and(|read| next_write.is_none_or(|write| read <= write))
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
