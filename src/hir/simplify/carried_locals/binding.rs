//! carried-local pass 的 binding 表示与 rewrite 工具。
//!
//! 主模块负责识别 handoff 是否能把后半段状态认回原 binding；这个模块统一表示
//! param/local/temp，提供精确 `(slot, close epoch)` 查询，并把 binding 引用批量改写到目标；
//! rewrite 同时把异槽或未知来源污染传播到目标 provenance。它不判断某个控制流 handoff
//! 是否安全，也不把 local compaction 策略冒充物理同槽证明。例如上层先证明 `t3` 与
//! `l1` 是同一机械状态，再用这里的 rewrite 把 `t3` 引用收回 `l1`。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, HirStmt, LocalId, ParamId, TempId};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

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

fn raw_binding_home_slot(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> Option<HomeSlotKey> {
    match binding {
        CarryBinding::Param(param) => Some(HomeSlotKey::new(param.index(), 0)),
        CarryBinding::Local(local) => promotion_facts.local_home_slot(local),
        CarryBinding::Temp(temp) => promotion_facts.home_slot(temp),
    }
}

pub(super) fn binding_home_slot_provenance_is_invalid(
    binding: CarryBinding,
    promotion_facts: &ProtoPromotionFacts,
) -> bool {
    match binding {
        CarryBinding::Param(param) => promotion_facts.param_home_was_invalidated(param),
        CarryBinding::Local(local) => promotion_facts.local_home_was_invalidated(local),
        CarryBinding::Temp(temp) => promotion_facts.temp_home_was_invalidated(temp),
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
    if binding_home_slot_provenance_is_invalid(left, promotion_facts)
        || binding_home_slot_provenance_is_invalid(right, promotion_facts)
    {
        return true;
    }
    match (
        raw_binding_home_slot(left, promotion_facts),
        raw_binding_home_slot(right, promotion_facts),
    ) {
        (Some(left), Some(right)) => left == right,
        _ => true,
    }
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
    let source_home = binding_home_slot(source, promotion_facts);
    let target_home = binding_home_slot(target, promotion_facts);
    if source_home.is_some() && source_home == target_home {
        return;
    }
    match target {
        CarryBinding::Param(param) => promotion_facts.invalidate_param_home(param),
        CarryBinding::Local(local) => promotion_facts.invalidate_local_home(local),
        CarryBinding::Temp(temp) => promotion_facts.invalidate_temp_home(temp),
    }
}

impl HirRewritePass for TempToBindingPass<'_> {
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
