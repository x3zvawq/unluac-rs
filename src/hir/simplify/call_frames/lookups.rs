//! 完整 PUC 源码帧中的多层索引与算术准备。
//!
//! 每次访问消费 Promotion 的原结果和输入布局，共享 builder 仍拥有 Def 写域、事件顺序
//! 及声明身份。例 `root.nodes[keys[2]].value` 先在当前槽逐层读取 base，再在其上一槽
//! 读取动态 key，最后原位覆盖；不能把动态键的原暂存槽或中间表快照交给 AST 猜测。

use super::*;
use crate::hir::common::HirTableAccess;

impl FrameBuilder<'_> {
    pub(super) fn puc_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let layout = self.facts.native_table_read_layout(access)?;
        let result = HomeSlotKey::new(slot, 0);
        if self.facts.table_read_result_home(access) != Some(result)
            || self.native?.barred.contains(&result)
            || self.native?.closed.contains(&result)
        {
            return None;
        }
        let direct_base = self
            .direct_home(&access.base)
            .is_some_and(|home| home == layout.base && home.slot() < self.base);
        if !direct_base && layout.base != result {
            // 候选拒绝[ProofIncomplete]：高槽 base 必须在当前结果槽完成，不能省略不同槽快照。
            return None;
        }
        let base = self.puc_operand(&access.base, before, slot)?;
        let key = if let Some(home) = layout.key {
            let direct_key = self
                .direct_home(&access.key)
                .is_some_and(|key| key == home && key.slot() < self.base);
            let key_slot = slot + usize::from(!direct_base);
            if !direct_key && home != HomeSlotKey::new(key_slot, 0) {
                return None;
            }
            self.puc_operand(&access.key, before, key_slot)?
        } else {
            if !self.native?.constants_fit_rk
                || !matches!(
                    access.key,
                    HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                )
            {
                return None;
            }
            access.key.clone()
        };
        Some(HirExpr::TableAccess(Box::new(HirTableAccess {
            base,
            key,
            sources: access.sources.clone(),
            metamethod_free: access.metamethod_free,
            method_setup_protocol: access.method_setup_protocol,
        })))
    }

    /// 新增帧内操作逐层核对原输入；旧的简单字段入口不承担嵌套准备证明。
    pub(super) fn puc_operand(
        &mut self,
        value: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        match value {
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => None,
            HirExpr::TableAccess(access) => self.puc_lookup(access, before, slot),
            HirExpr::GlobalRef(global)
                if self.facts.global_read_frame(global, self.dialect)
                    != Some(HomeSlotKey::new(slot, 0)) =>
            {
                None
            }
            HirExpr::UpvalueRef(_) => None,
            _ => {
                let previous = std::mem::replace(&mut self.puc_operand, true);
                let rebuilt = self.expr(value, before, slot, None, false, true, None);
                self.puc_operand = previous;
                let rebuilt = rebuilt?;
                // 当前树中的字面量不能代替原寄存器准备写，包括被 LocalRef 包住的 LOADK。
                (!matches!(
                    rebuilt,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                ))
                .then_some(rebuilt)
            }
        }
    }

    pub(super) fn puc_arithmetic(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let result = HomeSlotKey::new(slot, 0);
        if !self.native?.constants_fit_rk
            || self.facts.operation_result_home(binary.source_site?) != Some(result)
            || self.native?.barred.contains(&result)
            || self.native?.closed.contains(&result)
        {
            return None;
        }
        let layout = self.facts.native_binary_layout(binary)?;
        let direct = |value: &HirExpr, home| {
            self.direct_home(value)
                .is_some_and(|actual| Some(actual) == home && actual.slot() < self.base)
        };
        let lhs_low = direct(&binary.lhs, layout.lhs);
        let rhs_low = direct(&binary.rhs, layout.rhs);
        let constant = |value: &HirExpr| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_));
        let lhs = if layout.lhs.is_none() && constant(&binary.lhs) {
            binary.lhs.clone()
        } else {
            if !lhs_low && layout.lhs != Some(result) {
                return None;
            }
            self.puc_operand(&binary.lhs, before, slot)?
        };
        let rhs_slot = slot + usize::from(!lhs_low && layout.lhs.is_some());
        let rhs = if layout.rhs.is_none() && constant(&binary.rhs) {
            binary.rhs.clone()
        } else {
            if !rhs_low && layout.rhs != Some(HomeSlotKey::new(rhs_slot, 0)) {
                return None;
            }
            self.puc_operand(&binary.rhs, before, rhs_slot)?
        };
        Some(HirExpr::Binary(Box::new(
            crate::hir::common::HirBinaryExpr {
                lhs,
                rhs,
                source_site: binary.source_site,
                op: binary.op,
            },
        )))
    }
}
