//! 这个文件集中管理 structured body lowering 里的 override 状态。
//!
//! `entry_overrides / phi_overrides / suppressed_*` 都属于“结构恢复过程中对 block
//! 入口和 phi 物化的临时裁剪决定”，不应该再散落成几份裸 map/set 让各个 pass 自己揉。
//! 这里把它们收成一个局部 owner，后续继续调整 override 规则时，只需要改这一层。

use std::collections::{BTreeMap, BTreeSet};

use crate::cfg::{BlockRef, PhiId};
use crate::hir::common::{HirExpr, TempId};
use crate::transformer::{InstrRef, Reg};

#[derive(Debug, Clone, Default)]
pub(super) struct BlockOverrideState {
    entry_exprs: BTreeMap<Reg, HirExpr>,
    carried_entry_exprs: BTreeMap<Reg, HirExpr>,
    entry_temp_exprs: BTreeMap<TempId, HirExpr>,
    phi_exprs: BTreeMap<PhiId, HirExpr>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct StructureOverrideState {
    by_block: BTreeMap<BlockRef, BlockOverrideState>,
    suppressed_phis: BTreeSet<PhiId>,
    suppressed_instrs: BTreeSet<InstrRef>,
}

impl StructureOverrideState {
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

    pub(super) fn insert_entry_expr(
        &mut self,
        block: BlockRef,
        reg: Reg,
        expr: HirExpr,
        source_temp: Option<TempId>,
        carries_through_block: bool,
    ) {
        let state = self.by_block.entry(block).or_default();
        state.entry_exprs.insert(reg, expr.clone());
        if carries_through_block {
            state.carried_entry_exprs.insert(reg, expr.clone());
        }
        if let Some(temp) = source_temp {
            state.entry_temp_exprs.insert(temp, expr);
        }
    }

    pub(super) fn insert_phi_expr(&mut self, block: BlockRef, phi_id: PhiId, expr: HirExpr) {
        self.by_block
            .entry(block)
            .or_default()
            .phi_exprs
            .insert(phi_id, expr);
    }

    pub(super) fn suppress_phi(&mut self, phi_id: PhiId) {
        self.suppressed_phis.insert(phi_id);
    }

    pub(super) fn unsuppress_phi(&mut self, phi_id: PhiId) {
        self.suppressed_phis.remove(&phi_id);
    }

    pub(super) fn suppress_instrs(&mut self, instrs: impl IntoIterator<Item = InstrRef>) {
        self.suppressed_instrs.extend(instrs);
    }

    pub(super) fn instr_is_suppressed(&self, instr_ref: InstrRef) -> bool {
        self.suppressed_instrs.contains(&instr_ref)
    }

    pub(super) fn suppressed_phis_for_block(&self, block: BlockRef) -> BTreeSet<PhiId> {
        let mut suppressed = self.suppressed_phis.clone();
        if let Some(phi_exprs) = self.block_phi_exprs(block) {
            suppressed.extend(phi_exprs.keys().copied());
        }
        suppressed
    }
}
