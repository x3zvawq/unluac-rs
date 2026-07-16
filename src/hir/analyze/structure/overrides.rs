//! 这个文件集中管理 structured body lowering 里的 override 状态。
//!
//! `entry_overrides / phi_overrides / suppressed_*` 都属于“结构恢复过程中对 block
//! 入口和 phi 物化的临时裁剪决定”，不应该再散落成几份裸 map/set 让各个 pass 自己揉。
//! 这里把它们收成一个局部 owner，后续继续调整 override 规则时，只需要改这一层。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, TempId};
use crate::structure::{BlockRef, PhiId};
use crate::transformer::{InstrRef, Reg};

use super::rewrites::{expr_has_temp_ref_in, rewrite_expr_temps};

#[derive(Debug, Default)]
pub(super) struct BlockOverrideState {
    entry_exprs: BTreeMap<Reg, HirExpr>,
    carried_entry_exprs: BTreeMap<Reg, HirExpr>,
    entry_temp_exprs: BTreeMap<TempId, HirExpr>,
    phi_exprs: BTreeMap<PhiId, HirExpr>,
}

impl BlockOverrideState {
    fn is_empty(&self) -> bool {
        self.entry_exprs.is_empty()
            && self.carried_entry_exprs.is_empty()
            && self.entry_temp_exprs.is_empty()
            && self.phi_exprs.is_empty()
    }
}

#[derive(Debug)]
enum OverrideUndo {
    EntryExpr(BlockRef, Reg, Option<HirExpr>),
    CarriedEntryExpr(BlockRef, Reg, Option<HirExpr>),
    EntryTempExpr(BlockRef, TempId, Option<HirExpr>),
    PhiExpr(BlockRef, PhiId, Option<HirExpr>),
    PhiTempAlias(TempId, Option<HirExpr>),
    DefTarget(TempId, Option<HirLValue>),
    SuppressedPhiInserted(PhiId),
    SuppressedPhiRemoved(PhiId),
    SuppressedInstrInserted(InstrRef),
}

#[derive(Debug, Default)]
pub(super) struct StructureOverrideState {
    by_block: BTreeMap<BlockRef, BlockOverrideState>,
    phi_temp_aliases: BTreeMap<TempId, HirExpr>,
    def_targets: BTreeMap<TempId, HirLValue>,
    suppressed_phis: BTreeSet<PhiId>,
    suppressed_instrs: BTreeSet<InstrRef>,
    undo: Vec<OverrideUndo>,
}

impl StructureOverrideState {
    pub(super) fn checkpoint(&self) -> usize {
        self.undo.len()
    }

    pub(super) fn rollback(&mut self, checkpoint: usize) {
        while self.undo.len() > checkpoint {
            match self
                .undo
                .pop()
                .expect("override rollback length should be valid")
            {
                OverrideUndo::EntryExpr(block, reg, old) => {
                    restore_map_entry(
                        &mut self.by_block,
                        block,
                        old,
                        |state| &mut state.entry_exprs,
                        reg,
                    );
                }
                OverrideUndo::CarriedEntryExpr(block, reg, old) => {
                    restore_map_entry(
                        &mut self.by_block,
                        block,
                        old,
                        |state| &mut state.carried_entry_exprs,
                        reg,
                    );
                }
                OverrideUndo::EntryTempExpr(block, temp, old) => {
                    restore_map_entry(
                        &mut self.by_block,
                        block,
                        old,
                        |state| &mut state.entry_temp_exprs,
                        temp,
                    );
                }
                OverrideUndo::PhiExpr(block, phi_id, old) => {
                    restore_map_entry(
                        &mut self.by_block,
                        block,
                        old,
                        |state| &mut state.phi_exprs,
                        phi_id,
                    );
                }
                OverrideUndo::PhiTempAlias(temp, Some(old)) => {
                    self.phi_temp_aliases.insert(temp, old);
                }
                OverrideUndo::PhiTempAlias(temp, None) => {
                    self.phi_temp_aliases.remove(&temp);
                }
                OverrideUndo::DefTarget(temp, Some(old)) => {
                    self.def_targets.insert(temp, old);
                }
                OverrideUndo::DefTarget(temp, None) => {
                    self.def_targets.remove(&temp);
                }
                OverrideUndo::SuppressedPhiInserted(phi_id) => {
                    self.suppressed_phis.remove(&phi_id);
                }
                OverrideUndo::SuppressedPhiRemoved(phi_id) => {
                    self.suppressed_phis.insert(phi_id);
                }
                OverrideUndo::SuppressedInstrInserted(instr_ref) => {
                    self.suppressed_instrs.remove(&instr_ref);
                }
            }
        }
    }

    pub(super) fn block_entry_expr(&self, block: BlockRef, reg: Reg) -> Option<&HirExpr> {
        self.by_block.get(&block)?.entry_exprs.get(&reg)
    }

    pub(super) fn block_phi_exprs(&self, block: BlockRef) -> Option<&BTreeMap<PhiId, HirExpr>> {
        self.by_block
            .get(&block)
            .and_then(|state| (!state.phi_exprs.is_empty()).then_some(&state.phi_exprs))
    }

    pub(super) fn carried_entry_expr(&self, block: BlockRef, reg: Reg) -> Option<&HirExpr> {
        self.by_block.get(&block)?.carried_entry_exprs.get(&reg)
    }

    pub(super) fn block_entry_temp_exprs(
        &self,
        block: BlockRef,
    ) -> Option<&BTreeMap<TempId, HirExpr>> {
        self.by_block.get(&block).and_then(|state| {
            (!state.entry_temp_exprs.is_empty()).then_some(&state.entry_temp_exprs)
        })
    }

    pub(super) fn phi_temp_aliases(&self) -> &BTreeMap<TempId, HirExpr> {
        &self.phi_temp_aliases
    }

    pub(super) fn def_targets(&self) -> &BTreeMap<TempId, HirLValue> {
        &self.def_targets
    }

    pub(super) fn insert_def_target(&mut self, temp: TempId, target: HirLValue) -> bool {
        if self.def_targets.get(&temp) == Some(&target) {
            return true;
        }
        if self.def_targets.contains_key(&temp) {
            return false;
        }
        let old = self.def_targets.insert(temp, target);
        self.undo.push(OverrideUndo::DefTarget(temp, old));
        true
    }

    pub(super) fn alias_phi_temp(&mut self, temp: TempId, mut expr: HirExpr) -> bool {
        // owner 本身就是该 temp 时，def target 已经直接写入它；不需要额外 alias，
        // 但这不是跨 Phi 环，仍允许原 Phi 物化被结构 owner 接管。
        if expr == HirExpr::TempRef(temp) {
            if let Some(old) = self.phi_temp_aliases.remove(&temp) {
                self.undo.push(OverrideUndo::PhiTempAlias(temp, Some(old)));
            }
            return true;
        }
        rewrite_expr_temps(&mut expr, &self.phi_temp_aliases);
        if expr_has_temp_ref_in(&expr, &BTreeSet::from([temp])) {
            return false;
        }
        if self.phi_temp_aliases.get(&temp) != Some(&expr) {
            let old = self.phi_temp_aliases.insert(temp, expr);
            self.undo.push(OverrideUndo::PhiTempAlias(temp, old));
        }
        true
    }

    pub(super) fn insert_entry_expr(
        &mut self,
        block: BlockRef,
        reg: Reg,
        expr: HirExpr,
        source_temp: Option<TempId>,
        carries_through_block: bool,
    ) -> bool {
        let state = self.by_block.entry(block).or_default();
        let conflicts = state.entry_exprs.get(&reg).is_some_and(|old| old != &expr)
            || carries_through_block
                && state
                    .carried_entry_exprs
                    .get(&reg)
                    .is_some_and(|old| old != &expr)
            || source_temp.is_some_and(|temp| {
                state
                    .entry_temp_exprs
                    .get(&temp)
                    .is_some_and(|old| old != &expr)
            });
        if conflicts {
            return false;
        }
        let entry_changed = state.entry_exprs.get(&reg) != Some(&expr);
        let carried_changed =
            carries_through_block && state.carried_entry_exprs.get(&reg) != Some(&expr);
        let source_changed =
            source_temp.is_some_and(|temp| state.entry_temp_exprs.get(&temp) != Some(&expr));
        if entry_changed {
            let old = state.entry_exprs.insert(reg, expr.clone());
            self.undo.push(OverrideUndo::EntryExpr(block, reg, old));
        }
        if carried_changed {
            let old = state.carried_entry_exprs.insert(reg, expr.clone());
            self.undo
                .push(OverrideUndo::CarriedEntryExpr(block, reg, old));
        }
        if source_changed {
            let temp = source_temp.expect("changed source entry should have a temp");
            let old = state.entry_temp_exprs.insert(temp, expr);
            self.undo
                .push(OverrideUndo::EntryTempExpr(block, temp, old));
        }
        entry_changed || carried_changed || source_changed
    }

    pub(super) fn insert_phi_expr(&mut self, block: BlockRef, phi_id: PhiId, expr: HirExpr) {
        let phi_exprs = &mut self.by_block.entry(block).or_default().phi_exprs;
        if phi_exprs.get(&phi_id) == Some(&expr) {
            return;
        }
        let old = phi_exprs.insert(phi_id, expr);
        self.undo.push(OverrideUndo::PhiExpr(block, phi_id, old));
    }

    pub(super) fn suppress_phi(&mut self, phi_id: PhiId) {
        if self.suppressed_phis.insert(phi_id) {
            self.undo.push(OverrideUndo::SuppressedPhiInserted(phi_id));
        }
    }

    pub(super) fn unsuppress_phi(&mut self, phi_id: PhiId) {
        if self.suppressed_phis.remove(&phi_id) {
            self.undo.push(OverrideUndo::SuppressedPhiRemoved(phi_id));
        }
    }

    pub(super) fn suppress_instrs(&mut self, instrs: impl IntoIterator<Item = InstrRef>) {
        for instr_ref in instrs {
            if self.suppressed_instrs.insert(instr_ref) {
                self.undo
                    .push(OverrideUndo::SuppressedInstrInserted(instr_ref));
            }
        }
    }

    pub(super) fn instr_is_suppressed(&self, instr_ref: InstrRef) -> bool {
        self.suppressed_instrs.contains(&instr_ref)
    }

    pub(super) fn phi_is_suppressed_for_block(&self, block: BlockRef, phi_id: PhiId) -> bool {
        self.suppressed_phis.contains(&phi_id)
            || self
                .block_phi_exprs(block)
                .is_some_and(|phi_exprs| phi_exprs.contains_key(&phi_id))
    }
}

fn restore_map_entry<K: Ord, V>(
    by_block: &mut BTreeMap<BlockRef, BlockOverrideState>,
    block: BlockRef,
    old: Option<V>,
    field: impl FnOnce(&mut BlockOverrideState) -> &mut BTreeMap<K, V>,
    key: K,
) {
    let state = by_block.entry(block).or_default();
    match old {
        Some(value) => {
            field(state).insert(key, value);
        }
        None => {
            field(state).remove(&key);
        }
    }
    if state.is_empty() {
        by_block.remove(&block);
    }
}
