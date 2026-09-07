//! carried-local pass 的 binding 表示与 rewrite 工具。
//!
//! 主模块负责识别 handoff 是否能把后半段状态认回原 binding；这个模块统一表示
//! param/local/temp，提供精确 `(slot, close epoch)` 查询，并把 binding 引用批量改写到目标；
//! rewrite 同时把异槽或未知来源污染传播到目标 provenance。它不判断某个控制流 handoff
//! 是否安全，也不把 local compaction 策略冒充物理同槽证明。例如上层先证明 `t3` 与
//! `l1` 是同一机械状态，再用这里的 rewrite 把 `t3` 引用收回 `l1`。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, HirStmt, LocalId, ParamId, TempId};
use crate::hir::promotion::{HomeSlotKey, HomeSlots, ProtoPromotionFacts};

use super::super::walk::HirRewritePass;

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(in crate::hir::simplify) enum CarryBinding {
    Param(ParamId),
    Local(LocalId),
    Temp(TempId),
}

impl CarryBinding {
    pub(in crate::hir::simplify) const fn local(self) -> Option<LocalId> {
        match self {
            Self::Local(local) => Some(local),
            Self::Param(_) | Self::Temp(_) => None,
        }
    }
}

pub(super) fn binding_home_slot(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match binding {
        CarryBinding::Param(param) => promotion_facts.trusted_param_home_slot(param),
        CarryBinding::Local(local) => promotion_facts.trusted_local_home_slot(local),
        CarryBinding::Temp(temp) => promotion_facts.trusted_temp_home_slot(temp),
    }
}

fn possible_binding_home_slots(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlots<'_>> {
    match binding {
        CarryBinding::Param(param) => promotion_facts.possible_param_home_slots(param),
        CarryBinding::Local(local) => promotion_facts.possible_local_home_slots(local),
        CarryBinding::Temp(temp) => promotion_facts.possible_temp_home_slots(temp),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum BindingHomeOverlap {
    Disjoint,
    Overlap,
    /// `ProtoPromotionFacts` lacks a complete possible-home set for at least one binding.
    Unknown,
}

pub(super) fn binding_home_overlap(
    left: CarryBinding,
    right: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> BindingHomeOverlap {
    if left == right {
        return BindingHomeOverlap::Overlap;
    }
    let (Some(left), Some(right)) = (
        possible_binding_home_slots(left, promotion_facts),
        possible_binding_home_slots(right, promotion_facts),
    ) else {
        return BindingHomeOverlap::Unknown;
    };
    if left.is_disjoint(&right) {
        BindingHomeOverlap::Disjoint
    } else {
        BindingHomeOverlap::Overlap
    }
}

pub(super) fn bindings_share_exact_home_slot(
    left: CarryBinding,
    right: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    binding_home_slot(left, promotion_facts)
        .zip(binding_home_slot(right, promotion_facts))
        .is_some_and(|(left, right)| left == right)
}

pub(super) fn bindings_may_share_raw_home_slot(
    left: CarryBinding,
    right: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    // Identity gates are conservative on genuinely incomplete provenance, but an invalidated
    // single-home fact is not itself a permanent barrier when its complete finite union survives.
    !matches!(
        binding_home_overlap(left, right, promotion_facts),
        BindingHomeOverlap::Disjoint
    )
}

pub(super) trait BindingProtection {
    fn contains(&self, binding: &CarryBinding) -> bool;
}

impl BindingProtection for BTreeSet<CarryBinding> {
    fn contains(&self, binding: &CarryBinding) -> bool {
        BTreeSet::contains(self, binding)
    }
}

pub(super) fn carry_binding_from_expr(expr: &HirExpr) -> Option<CarryBinding> {
    match expr {
        HirExpr::ParamRef(param) => Some(CarryBinding::Param(*param)),
        HirExpr::LocalRef(local) => Some(CarryBinding::Local(*local)),
        HirExpr::TempRef(temp) => Some(CarryBinding::Temp(*temp)),
        _ => None,
    }
}

pub(super) fn carry_binding_from_lvalue(lvalue: &HirLValue) -> Option<CarryBinding> {
    match lvalue {
        HirLValue::Param(param) => Some(CarryBinding::Param(*param)),
        HirLValue::Local(local) => Some(CarryBinding::Local(*local)),
        HirLValue::Temp(temp) => Some(CarryBinding::Temp(*temp)),
        HirLValue::Upvalue(_) | HirLValue::Global(_) | HirLValue::TableAccess(_) => None,
    }
}

pub(in crate::hir::simplify) fn single_binding_copy(
    stmt: &HirStmt,
) -> Option<(CarryBinding, CarryBinding)> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([target], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    Some((
        carry_binding_from_lvalue(target)?,
        carry_binding_from_expr(value)?,
    ))
}

pub(super) fn carry_binding_from_capture(binding: crate::hir::HirBinding) -> Option<CarryBinding> {
    use crate::hir::HirBinding;
    match binding {
        HirBinding::Param(id) => Some(CarryBinding::Param(id)),
        HirBinding::Local(id) => Some(CarryBinding::Local(id)),
        HirBinding::Temp(id) => Some(CarryBinding::Temp(id)),
        HirBinding::Upvalue(_) => None,
    }
}

fn carry_capture_binding(binding: CarryBinding) -> crate::hir::HirBinding {
    use crate::hir::HirBinding;
    match binding {
        CarryBinding::Param(id) => HirBinding::Param(id),
        CarryBinding::Local(id) => HirBinding::Local(id),
        CarryBinding::Temp(id) => HirBinding::Temp(id),
    }
}

fn carry_binding_expr(binding: CarryBinding) -> HirExpr {
    match binding {
        CarryBinding::Param(param) => HirExpr::ParamRef(param),
        CarryBinding::Local(local) => HirExpr::LocalRef(local),
        CarryBinding::Temp(temp) => HirExpr::TempRef(temp),
    }
}

fn carry_binding_lvalue(binding: CarryBinding) -> HirLValue {
    match binding {
        CarryBinding::Param(param) => HirLValue::Param(param),
        CarryBinding::Local(local) => HirLValue::Local(local),
        CarryBinding::Temp(temp) => HirLValue::Temp(temp),
    }
}

#[derive(Clone, Copy)]
pub(super) struct TempBindingRewrite {
    pub(super) from: TempId,
    pub(super) to: CarryBinding,
}

pub(super) struct BindingClassRewritePass<'a> {
    pub(super) rewrites: BTreeMap<CarryBinding, CarryBinding>,
    pub(super) promotion_facts: &'a mut ProtoPromotionFacts,
}

impl BindingClassRewritePass<'_> {
    fn rewrite_binding(&mut self, binding: CarryBinding) -> Option<CarryBinding> {
        let rewritten = self.rewrites.get(&binding).copied()?;
        record_binding_merge(binding, rewritten, self.promotion_facts);
        Some(rewritten)
    }
}

impl HirRewritePass for BindingClassRewritePass<'_> {
    fn rewrite_capture(&mut self, capture: &mut crate::hir::HirCapture) -> bool {
        let Some(binding) = carry_binding_from_capture(capture.binding) else {
            return false;
        };
        let Some(rewrite) = self.rewrite_binding(binding) else {
            return false;
        };
        capture.binding = carry_capture_binding(rewrite);
        true
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let Some(binding) = carry_binding_from_expr(expr) else {
            return false;
        };
        let Some(rewrite) = self.rewrite_binding(binding) else {
            return false;
        };
        *expr = carry_binding_expr(rewrite);
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let Some(binding) = carry_binding_from_lvalue(lvalue) else {
            return false;
        };
        let Some(rewrite) = self.rewrite_binding(binding) else {
            return false;
        };
        *lvalue = carry_binding_lvalue(rewrite);
        true
    }
}

pub(super) struct TempToBindingPass<'a> {
    pub(super) rewrites: Vec<TempBindingRewrite>,
    pub(super) promotion_facts: &'a mut ProtoPromotionFacts,
}

impl TempToBindingPass<'_> {
    fn binding_for_temp(&mut self, temp: TempId) -> Option<CarryBinding> {
        let rewritten = self
            .rewrites
            .iter()
            .find_map(|rewrite| (rewrite.from == temp).then_some(rewrite.to))?;
        record_binding_merge(CarryBinding::Temp(temp), rewritten, self.promotion_facts);
        Some(rewritten)
    }
}

pub(super) fn record_binding_merge(
    source: CarryBinding,
    target: CarryBinding,
    promotion_facts: &mut ProtoPromotionFacts,
) {
    if source == target {
        return;
    }
    let source_definition_write_homes = match source {
        CarryBinding::Param(param) => {
            promotion_facts.supplemental_param_definition_write_homes(param)
        }
        CarryBinding::Local(local) => {
            promotion_facts.supplemental_local_definition_write_homes(local)
        }
        CarryBinding::Temp(temp) => promotion_facts.supplemental_temp_definition_write_homes(temp),
    };
    match target {
        CarryBinding::Param(param) => {
            promotion_facts.merge_param_definition_write_homes(param, source_definition_write_homes)
        }
        CarryBinding::Local(local) => {
            promotion_facts.merge_local_definition_write_homes(local, source_definition_write_homes)
        }
        CarryBinding::Temp(temp) => {
            promotion_facts.merge_temp_definition_write_homes(temp, source_definition_write_homes)
        }
    }
    let source_home = binding_home_slot(source, promotion_facts);
    let target_home = binding_home_slot(target, promotion_facts);
    if source_home.is_some() && source_home == target_home {
        return;
    }
    let source_homes =
        possible_binding_home_slots(source, promotion_facts).map(|homes| homes.into_owned());
    match target {
        CarryBinding::Param(param) => promotion_facts.record_param_home_merge(param, source_homes),
        CarryBinding::Local(local) => promotion_facts.record_local_home_merge(local, source_homes),
        CarryBinding::Temp(temp) => promotion_facts.record_temp_home_merge(temp, source_homes),
    }
}

impl HirRewritePass for TempToBindingPass<'_> {
    fn rewrite_capture(&mut self, capture: &mut crate::hir::HirCapture) -> bool {
        let crate::hir::HirBinding::Temp(temp) = capture.binding else {
            return false;
        };
        let Some(binding) = self.binding_for_temp(temp) else {
            return false;
        };
        capture.binding = carry_capture_binding(binding);
        true
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        let HirExpr::TempRef(temp) = expr else {
            return false;
        };
        let Some(binding) = self.binding_for_temp(*temp) else {
            return false;
        };
        *expr = match binding {
            CarryBinding::Param(param) => HirExpr::ParamRef(param),
            CarryBinding::Local(local) => HirExpr::LocalRef(local),
            CarryBinding::Temp(temp) => HirExpr::TempRef(temp),
        };
        true
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        let HirLValue::Temp(temp) = lvalue else {
            return false;
        };
        let Some(binding) = self.binding_for_temp(*temp) else {
            return false;
        };
        *lvalue = match binding {
            CarryBinding::Param(param) => HirLValue::Param(param),
            CarryBinding::Local(local) => HirLValue::Local(local),
            CarryBinding::Temp(temp) => HirLValue::Temp(temp),
        };
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_merge_propagates_finite_possible_home_union() {
        let source = TempId(0);
        let target = TempId(1);
        let source_home = HomeSlotKey::new(0, 0);
        let target_home = HomeSlotKey::new(1, 0);
        let mut facts = ProtoPromotionFacts::default();
        facts.record_temp_home_slot_for_test(source, source_home);
        facts.record_temp_home_slot_for_test(target, target_home);

        record_binding_merge(
            CarryBinding::Temp(source),
            CarryBinding::Temp(target),
            &mut facts,
        );

        assert_eq!(facts.trusted_temp_home_slot(target), None);
        assert_eq!(
            facts.possible_temp_home_slots(target).as_deref(),
            Some(&BTreeSet::from([source_home, target_home]))
        );
    }
}
