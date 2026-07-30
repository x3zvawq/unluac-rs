//! carried-local pass 的 binding 表示与 rewrite 工具。
//!
//! 主模块负责识别 handoff 是否能把后半段状态认回原 binding；这个模块只提供
//! `local/temp` 二元 binding 的统一表示，以及把 temp/local 引用批量改写到目标 binding
//! 的 rewrite pass。这里不判断 handoff 是否安全。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirExpr, HirLValue, LocalId, ParamId, TempId};

use super::super::walk::HirRewritePass;

#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum CarryBinding {
    Param(ParamId),
    Local(LocalId),
    Temp(TempId),
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

pub(super) struct BindingClassRewritePass {
    pub(super) rewrites: BTreeMap<CarryBinding, CarryBinding>,
}

impl BindingClassRewritePass {
    fn rewrite_binding(&self, binding: CarryBinding) -> Option<CarryBinding> {
        self.rewrites.get(&binding).copied()
    }
}

impl HirRewritePass for BindingClassRewritePass {
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

pub(super) struct TempToBindingPass {
    pub(super) rewrites: Vec<TempBindingRewrite>,
}

impl TempToBindingPass {
    fn binding_for_temp(&self, temp: TempId) -> Option<CarryBinding> {
        self.rewrites
            .iter()
            .find_map(|rewrite| (rewrite.from == temp).then_some(rewrite.to))
    }
}

impl HirRewritePass for TempToBindingPass {
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
