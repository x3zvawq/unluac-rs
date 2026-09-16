//! 在完整源码帧中恢复索引、比较和算术输入准备。
//!
//! 消费 Promotion 的原结果及操作数布局，由共享 FrameBuilder 验证 Def 写域、
//! 事件顺序和声明身份，不从表达式外形推断暂存槽或根退休权限。
//! 例如 root.nodes[keys[2]].value 必须保持 base 与动态 key 的原求值次序和覆盖点；
//! 各 VM 的内嵌常量及寄存器操作数在对应路径中核对。

use super::*;
use crate::hir::common::HirTableAccess;

impl FrameBuilder<'_> {
    /// Luau 先保留 Boolean 目标，再计算 RK 算术，最后为有序比较准备常量。
    /// 返回算术操作数所在侧；LocalRef 仍交共享 builder 按原 Def 和事件游标消费。
    pub(super) fn luau_arithmetic_comparison_operand(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<bool> {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        if self.dialect != DecompileDialect::Luau || !matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
            return None;
        }
        let layout = self.facts.native_binary_layout(binary)?;
        [
            (true, &binary.lhs, layout.lhs, &binary.rhs, layout.rhs),
            (false, &binary.rhs, layout.rhs, &binary.lhs, layout.lhs),
        ]
        .into_iter()
        .find_map(|(left, value, original, constant, constant_home)| {
            if original != Some(HomeSlotKey::new(slot + 1, 0))
                || !matches!(constant, HirExpr::Integer(_) | HirExpr::Number(_))
                || if binary.op == Eq {
                    !left || constant_home.is_some()
                } else {
                    constant_home != Some(HomeSlotKey::new(slot + 2, 0))
                }
            {
                return None;
            }
            let value = match value {
                HirExpr::LocalRef(local) => {
                    scalar_local(self.run[self.definition(*local, before)?])?.1
                }
                value => value,
            };
            let HirExpr::Binary(arithmetic) = value else {
                return None;
            };
            (numeric_rk_arithmetic(arithmetic)
                && self.direct_rk_arithmetic(arithmetic, slot + 1).is_some())
            .then_some(left)
        })
    }

    /// 比较参数的物化位置来自当前 Boolean 值树或原单比较 phi，不从 operand 槽猜结果。
    fn jit_boolean_result_matches(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        self.dialect == DecompileDialect::Luajit
            && (self.boolean_frame == Some(slot)
                || self
                    .facts
                    .comparison_result_temp(binary)
                    .is_some_and(|result| {
                        self.facts.trusted_temp_home_slot(result) == Some(HomeSlotKey::new(slot, 0))
                    }))
    }

    /// JIT 有序关系的数字常量占寄存器，Eq 的常量则内嵌。已有 RI operand 先在结果槽
    /// 求值时，常量必须位于相邻后一槽；例如 `2 <= bits % 4` 保留 MOD 后的 LOADK。
    pub(super) fn jit_scalar_comparison(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        if !self.jit_boolean_result_matches(binary, slot)
            || !matches!(binary.op, Eq | Lt | Le | Gt | Ge)
        {
            return false;
        }
        let Some(layout) = self.facts.native_binary_layout(binary) else {
            return false;
        };
        let home = HomeSlotKey::new(slot, 0);
        let operand = |value: &HirExpr, original| {
            if self
                .direct_home(value)
                .is_some_and(|low| low.slot() < self.base && original == Some(low))
            {
                return Some(false);
            }
            (original == Some(home)
                && matches!(value, HirExpr::Binary(arithmetic)
                    if numeric_rk_arithmetic(arithmetic) && self.direct_rk_arithmetic(arithmetic, slot).is_some()))
                .then_some(true)
        };
        let numeric = |value: &HirExpr| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_));
        if binary.op == Eq {
            return operand(&binary.lhs, layout.lhs).is_some()
                && layout.rhs.is_none()
                && matches!(
                    binary.rhs,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                );
        }
        [
            (&binary.lhs, layout.lhs, &binary.rhs, layout.rhs),
            (&binary.rhs, layout.rhs, &binary.lhs, layout.lhs),
        ]
        .into_iter()
        .any(|(value, original, constant, constant_home)| {
            numeric(constant)
                && operand(value, original).is_some_and(|scratch| {
                    constant_home == Some(HomeSlotKey::new(slot + usize::from(scratch), 0))
                })
        })
    }

    /// JIT 比较参数复用首个 lookup 的槽；第二个 lookup 才占其相邻后一槽。
    /// `assert(t[1] == value and t[2] == nil)` 保留原 TGETB、低槽读取与 Boolean 写回；
    /// 不消费 run 中的新 producer，也不把动态键或先前 COPY 当作直接读取。
    pub(super) fn jit_lookup_comparison(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        if !self.jit_boolean_result_matches(binary, slot)
            || binary.op != crate::hir::common::HirBinaryOpKind::Eq
        {
            return false;
        }
        let Some(layout) = self.facts.native_binary_layout(binary) else {
            return false;
        };
        let lookup = |value: &HirExpr, home: HomeSlotKey| {
            let HirExpr::TableAccess(access) = value else {
                return false;
            };
            let key_fits = match &access.key {
                HirExpr::Integer(0..=255) => true,
                HirExpr::String(_) => self.native.is_some_and(|context| context.constants_fit_rk),
                _ => false,
            };
            key_fits
                && self.native.is_some_and(|context| !context.closed.contains(&home))
                // JIT 只有 ByReference capture，消费原操作时点的开放引用事实；
                // 后缀新 binding 的同槽 capture 不能回溯禁止此处原写。
                && access
                    .sources
                    .try_for_each_known(|source| {
                        self.facts
                            .operation_result_reference_unaliased(source)
                            .then_some(())
                    })
                    .is_some()
                && self.facts.table_read_result_home(access) == Some(home)
                && self
                    .facts
                    .native_table_read_layout(access)
                    .is_some_and(|layout| {
                        layout.key.is_none()
                            && layout.base.slot() < self.base
                            && self.direct_home(&access.base) == Some(layout.base)
                    })
        };
        let home = HomeSlotKey::new(slot, 0);
        if layout.lhs != Some(home) || !lookup(&binary.lhs, home) {
            return false;
        }
        match &binary.rhs {
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => self
                .direct_home(&binary.rhs)
                .is_some_and(|home| home.slot() < self.base && layout.rhs == Some(home)),
            HirExpr::TableAccess(_) => {
                let home = HomeSlotKey::new(slot + 1, 0);
                layout.rhs == Some(home) && lookup(&binary.rhs, home)
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => layout.rhs.is_none(),
            _ => false,
        }
    }

    /// 原 OR 的两臂在同槽合流；备用分配不消费 run 中的无条件 producer。
    pub(super) fn luau_table_or_empty(
        &mut self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        self.luau_table_or_empty_layout(logical, before, slot)?;
        let lhs = self.expr(&logical.lhs, before, slot, None, false, true, None)?;
        Some(HirExpr::LogicalOr(Box::new(
            crate::hir::common::HirLogicalExpr {
                lhs,
                rhs: logical.rhs.clone(),
            },
        )))
    }

    pub(super) fn luau_table_or_empty_layout(
        &self,
        logical: &crate::hir::common::HirLogicalExpr,
        before: usize,
        slot: usize,
    ) -> Option<()> {
        let context = self.native?;
        let home = HomeSlotKey::new(slot, 0);
        let input = match &logical.lhs {
            HirExpr::LocalRef(local) => scalar_local(self.run[self.definition(*local, before)?])?.1,
            input => input,
        };
        let (HirExpr::TableAccess(access), HirExpr::TableConstructor(table)) =
            (input, &logical.rhs)
        else {
            return None;
        };
        let (
            crate::hir::common::HirOperationSources::Single(input),
            crate::hir::common::HirOperationSources::Single(alternative),
        ) = (&access.sources, &table.sources)
        else {
            return None;
        };
        let layout = self.facts.native_table_read_layout(access)?;
        if self.dialect != DecompileDialect::Luau
            || self.facts.short_circuit_table_home(*input, *alternative) != Some(home)
            || context.barred.contains(&home)
            || context.closed.contains(&home)
            || layout.key.is_some()
            || layout.base.slot() >= self.base
            || self.direct_home(&access.base) != Some(layout.base)
            || !matches!(&access.key, HirExpr::String(key) if key.as_utf8().is_some_and(|key| self.dialect.is_identifier_name(key)))
            || !matches!(table.allocation, HirTableAllocation::Luau(allocation)
                if allocation.array_capacity == 0 && allocation.hash_capacity == 0)
            || !table.fields.is_empty()
            || table.trailing_multivalue.is_some()
        {
            return None;
        }
        Some(())
    }

    /// Luau 的整数索引先保留结果，再由 compileExprAuto 在高一槽调用 base；
    /// 外层具名字段在临时结果槽原位继续读取。只消费原嵌入键和完整单结果 CALL，
    /// 动态键也先保留结果，低槽 base 后在高一槽准备键；原 RK 算术须逐项核对输入和输出。
    pub(super) fn luau_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let result = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_table_read_layout(access)?;
        if self.dialect != DecompileDialect::Luau
            || self.facts.table_read_result_home(access) != Some(result)
            || context.barred.contains(&result)
            || context.closed.contains(&result)
        {
            return None;
        }
        let direct = self
            .direct_home(&access.base)
            .is_some_and(|home| home == layout.base && home.slot() < self.base);
        if let Some(key_home) = layout.key {
            if !direct || key_home != HomeSlotKey::new(slot + 1, 0) {
                return None;
            }
            let HirExpr::Binary(key) = &access.key else {
                return None;
            };
            if !numeric_rk_arithmetic(key) {
                return None;
            }
            let key = self.direct_rk_arithmetic(key, slot + 1)?;
            return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                key,
                ..access.clone()
            })));
        }
        let base = match &access.key {
            HirExpr::String(_) if direct => access.base.clone(),
            HirExpr::String(key)
                if layout.base == result
                    && key
                        .as_utf8()
                        .is_some_and(|name| self.dialect.is_identifier_name(name)) =>
            {
                let HirExpr::TableAccess(inner) = &access.base else {
                    return None;
                };
                self.luau_lookup(inner, before, slot)?
            }
            HirExpr::Integer(key) if (1..=256).contains(key) => {
                if direct {
                    access.base.clone()
                } else {
                    if layout.base != HomeSlotKey::new(slot + 1, 0) {
                        return None;
                    }
                    let value =
                        self.expr(&access.base, before, slot + 1, None, false, true, None)?;
                    if !matches!(value, HirExpr::Call(_)) {
                        return None;
                    }
                    value
                }
            }
            _ => return None,
        };
        Some(HirExpr::TableAccess(Box::new(HirTableAccess {
            base,
            ..access.clone()
        })))
    }

    /// JIT/Luau 的原 RK 指令直接读取低槽并写同一 scratch；调用方限定数字 RK 算术。
    pub(super) fn direct_rk_arithmetic(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let result = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_binary_layout(binary)?;
        if !context.constants_fit_rk
            || self.facts.operation_result_home(binary.source_site?) != Some(result)
            || context.barred.contains(&result)
            || context.closed.contains(&result)
            || layout.rhs.is_some()
            || !self
                .direct_home(&binary.lhs)
                .is_some_and(|home| home.slot() < self.base && layout.lhs == Some(home))
        {
            // 候选拒绝[ProofIncomplete]：需要原 RI 操作、同槽结果和原低槽读取；
            // 常量准备、其它 operand scratch 或开放结果 cell 不由该协议覆盖。
            return None;
        }
        // 不展开低槽 producer；原 RI 指令直接读取它，元方法与先前返回项的顺序不变。
        Some(HirExpr::Binary(Box::new(binary.clone())))
    }

    pub(super) fn register_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let layout = self.facts.native_table_read_layout(access)?;
        let result = HomeSlotKey::new(slot, 0);
        // 未来同槽 capture 不能反向阻止这次读取；只有原操作尚未打开 ByRef 时才可借证。
        // 当前声明/捕获身份及后继窗口仍由完整帧的原子 preview 验证。
        if self.facts.table_read_result_home(access) != Some(result)
            || (self.native?.barred.contains(&result)
                && !matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if self.facts.operation_result_reference_unaliased(source)))
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
        let base = self.register_operand(&access.base, before, slot)?;
        let key = if let Some(home) = layout.key {
            let direct_key = self
                .direct_home(&access.key)
                .is_some_and(|key| key == home && key.slot() < self.base);
            let key_slot = slot + usize::from(!direct_base);
            if !direct_key && home != HomeSlotKey::new(key_slot, 0) {
                return None;
            }
            self.register_operand(&access.key, before, key_slot)?
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
    pub(super) fn register_operand(
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
            HirExpr::TableAccess(access) => self.register_lookup(access, before, slot),
            HirExpr::GlobalRef(global)
                if self.facts.global_read_frame(global, self.dialect)
                    != Some(HomeSlotKey::new(slot, 0)) =>
            {
                None
            }
            HirExpr::UpvalueRef(_) => None,
            _ => {
                let previous = std::mem::replace(&mut self.register_operand, true);
                let rebuilt = self.expr(value, before, slot, None, false, true, None);
                self.register_operand = previous;
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
            self.register_operand(&binary.lhs, before, slot)?
        };
        let rhs_slot = slot + usize::from(!lhs_low && layout.lhs.is_some());
        let rhs = if layout.rhs.is_none() && constant(&binary.rhs) {
            binary.rhs.clone()
        } else {
            if !rhs_low && layout.rhs != Some(HomeSlotKey::new(rhs_slot, 0)) {
                return None;
            }
            self.register_operand(&binary.rhs, before, rhs_slot)?
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
