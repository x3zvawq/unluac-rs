//! 在完整源码帧中恢复索引、比较和算术输入准备。
//!
//! 消费 Promotion 的原定义与布局，由共享 FrameBuilder 验证事件顺序和声明身份。

use super::*;
use crate::hir::common::HirTableAccess;

impl FrameBuilder<'_> {
    /// Luau 先保留 Boolean 目标，再计算 RK 算术，最后准备比较右值。
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
        let operand_slot = self.boolean_operand_start(slot);
        [
            (true, &binary.lhs, layout.lhs, &binary.rhs, layout.rhs),
            (false, &binary.rhs, layout.rhs, &binary.lhs, layout.lhs),
        ]
        .into_iter()
        .find_map(|(left, value, original, constant, constant_home)| {
            let other_matches = match constant {
                HirExpr::Integer(_) | HirExpr::Number(_) => {
                    if binary.op == Eq {
                        left && constant_home
                            .is_none_or(|home| home == HomeSlotKey::new(operand_slot + 1, 0))
                    } else {
                        constant_home == Some(HomeSlotKey::new(operand_slot + 1, 0))
                    }
                }
                HirExpr::TableAccess(access) => {
                    left && constant_home == Some(HomeSlotKey::new(operand_slot + 1, 0))
                        && self.luau_comparison_table_read(access, operand_slot + 1)
                }
                HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => self
                    .direct_home(constant)
                    .is_some_and(|home| home.slot() < self.base && constant_home == Some(home)),
                _ => false,
            };
            if original != Some(HomeSlotKey::new(operand_slot, 0)) || !other_matches {
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
            // 这里只选择原算术结果；输入准备、写域和消费事件由随后的 expr 验证，
            // 不能要求它预先属于“低槽与常量”的更窄协议。
            (numeric_rk_arithmetic(arithmetic)
                && self.facts.operation_result_home(arithmetic.source_site?)
                    == Some(HomeSlotKey::new(operand_slot, 0)))
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
        let operand = |index, value: &HirExpr, original| {
            if self
                .facts
                .direct_binary_operand_home(binary, index)
                .is_some_and(|low| low.slot() < self.base && original == Some(low))
            {
                return Some(false);
            }
            if matches!(value, HirExpr::UpvalueRef(_))
                && original == Some(home)
                && self
                    .facts
                    .comparison_read_preparation(binary, value)
                    .is_some_and(|(_, preparation)| preparation == home)
            {
                return Some(true);
            }
            (original == Some(home)
                && matches!(value, HirExpr::Binary(arithmetic)
                    if numeric_rk_arithmetic(arithmetic) && self.direct_numeric_arithmetic(arithmetic, slot).is_some()))
                .then_some(true)
        };
        let numeric = |value: &HirExpr| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_));
        // 两个既有低槽值的相等/有序比较均不占 operand scratch；保留原方向和
        // 可能的比较元方法，并由 Boolean frame 核对结果的物化位置。
        if operand(0, &binary.lhs, layout.lhs) == Some(false)
            && operand(1, &binary.rhs, layout.rhs) == Some(false)
        {
            return true;
        }
        if binary.op == Eq {
            return operand(0, &binary.lhs, layout.lhs).is_some()
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
            (0, &binary.lhs, layout.lhs, &binary.rhs, layout.rhs),
            (1, &binary.rhs, layout.rhs, &binary.lhs, layout.lhs),
        ]
        .into_iter()
        .any(|(index, value, original, constant, constant_home)| {
            numeric(constant)
                && operand(index, value, original).is_some_and(|scratch| {
                    constant_home == Some(HomeSlotKey::new(slot + usize::from(scratch), 0))
                })
        })
    }

    /// JIT 比较参数复用首个 lookup 的槽；第二个 lookup 才占其相邻后一槽。
    /// `assert(t[1] == value and t[2] == nil)` 保留原 TGETB、低槽读取与 Boolean 写回；
    /// 不消费 run 中的新 producer；动态键须由原输入准备证明，不能借先前 COPY 的槽。
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
        let lookup = |value: &HirExpr, home: HomeSlotKey| matches!(value, HirExpr::TableAccess(access) if self.jit_direct_lookup(access, home));
        let home = HomeSlotKey::new(slot, 0);
        // 既有低槽位于左侧时不准备新值，右侧 TGET 独占 Boolean scratch；
        // 不交换比较方向，也不把右侧读取移到前一个短路条件之外。
        if self
            .direct_home(&binary.lhs)
            .is_some_and(|low| low.slot() < self.base && layout.lhs == Some(low))
        {
            return layout.rhs == Some(home) && lookup(&binary.rhs, home);
        }
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

    /// 原 TGET 读取低槽或同槽上值 base；键保留原布局，结果写原 scratch。
    pub(super) fn jit_direct_lookup(&self, access: &HirTableAccess, home: HomeSlotKey) -> bool {
        let key_fits = match &access.key {
            HirExpr::Integer(0..=255) => true,
            HirExpr::String(_) => self.native.is_some_and(|context| context.constants_fit_rk),
            _ => false,
        };
        self.native.is_some_and(|context| !context.closed.contains(&home))
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
                    ((layout.base.slot() < self.base
                        && self.facts.table_read_base_home(access) == Some(layout.base))
                        // GETUPVAL 与 TGET 同槽接续；依赖证书绑定到此次读取，
                        // 不给同名上值或不同槽的提前快照借用该准备位置。
                        || (layout.base == home
                            && matches!(access.base, HirExpr::UpvalueRef(_))
                            && matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                                if self.facts.operation_input_preparation(source, &access.base)
                                    .is_some_and(|(_, base)| base == home))))
                        && match layout.key {
                            None => key_fits,
                            Some(key) => (key.slot() < self.base
                                && self.direct_home(&access.key) == Some(key))
                                || matches!(access.key, HirExpr::UpvalueRef(_))
                                    && key == home
                                    && self.facts.table_key_preparation(access) == Some(key),
                        }
                })
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
                preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
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
            || self.facts.table_read_base_home(access) != Some(layout.base)
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
    /// 动态键也先保留结果：现成 base 直接读取，复合 base 与 key 依次在高槽准备；
    /// 原 RK 算术须逐项核对输入和输出。
    pub(super) fn luau_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let result = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_table_read_layout(access)?;
        // 未来复用此槽的 capture 不回溯到当前 GETTABLE；每个原读取 Def 在执行时
        // 均须未被引用捕获，实际后续使用仍由完整事务的 binding/前缀预览保护。
        if self.dialect != DecompileDialect::Luau
            || self.facts.table_read_result_home(access) != Some(result)
            || (context.barred.contains(&result)
                && access
                    .sources
                    .try_for_each_known(|source| {
                        self.facts
                            .operation_result_reference_unaliased(source)
                            .then_some(())
                    })
                    .is_none())
            || context.closed.contains(&result)
        {
            return None;
        }
        if context.expanded_callees.is_some() && layout.base == HomeSlotKey::new(slot + 2, 0) {
            return self
                .expanded_index(access, before, slot)
                .map(|(call, _)| HirExpr::Call(Box::new(call)));
        }
        let direct = self
            .facts
            .table_read_base_home(access)
            .is_some_and(|home| home == layout.base && home.slot() < self.base);
        if let Some(key_home) = layout.key {
            if crate::value_semantics::table::TableExpression::table_integer_key(&access.key)
                .is_some_and(|key| (1..=256).contains(&key))
                && layout.base == HomeSlotKey::new(slot + 1, 0)
                && key_home == HomeSlotKey::new(slot + 2, 0)
            {
                // O0 在 CALL 单结果之后显式加载整数键；保留结果、base、key 三槽，
                // 不能套用 GETTABLEN 的两槽布局，也不能提前读取调用结果。
                let base = self.expr(&access.base, before, slot + 1, None, false, true, None)?;
                if !matches!(base, HirExpr::Call(_)) {
                    return None;
                }
                return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                    base,
                    ..access.clone()
                })));
            }
            if !direct {
                // Luau 为动态索引保留结果槽，再依次准备 base 与 key；key 回调
                // 可以改写 base 的来源，不能在 key 之后重新读取它。
                if layout.base != HomeSlotKey::new(slot + 1, 0)
                    || key_home != HomeSlotKey::new(slot + 2, 0)
                {
                    return None;
                }
                let base = self.register_operand(&access.base, before, slot + 1)?;
                let key = self.register_operand(&access.key, before, slot + 2)?;
                return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                    base,
                    key,
                    ..access.clone()
                })));
            }
            if key_home != HomeSlotKey::new(slot + 1, 0) {
                return None;
            }
            // 动态 key 的结果槽在 GETTABLE 结果上方；共享 operand builder
            // 继续核对算术、LEN 等原操作的输入，不能按表达式形状假定可移动。
            let key = self.register_operand(&access.key, before, slot + 1)?;
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
                if let HirExpr::TableAccess(inner) = &access.base {
                    self.luau_lookup(inner, before, slot)?
                } else {
                    // CALL 的单结果可在同槽继续 GETTABLEKS；仍按完整调用帧
                    // 消费准备，不能把任意高槽 base 当成可省略的快照。
                    let value = self.expr(&access.base, before, slot, None, false, true, None)?;
                    if !matches!(value, HirExpr::Call(_)) {
                        return None;
                    }
                    value
                }
            }
            HirExpr::Integer(key) if (1..=256).contains(key) => {
                if direct {
                    access.base.clone()
                } else {
                    // generic-for 已预留整个控制帧；嵌套数字索引的 base 从当前
                    // freereg 准备，不能误用参数结果槽的紧邻位置覆盖控制槽。
                    let scratch = self.declaration_reserved_top.unwrap_or(0).max(slot + 1);
                    if layout.base != HomeSlotKey::new(scratch, 0) {
                        return None;
                    }
                    // 未提升的 base 已由 HIR 保留精确 Temp 身份；随原 home 一起
                    // 交给共享定义/写域检查，不能在递归入口丢掉这个 producer。
                    let producer = match access.base {
                        HirExpr::TempRef(temp) => Some(temp),
                        _ => None,
                    };
                    let value =
                        self.expr(&access.base, before, scratch, None, false, true, producer)?;
                    if !matches!(value, HirExpr::Call(_) | HirExpr::TableAccess(_))
                        && !matches!(&value, HirExpr::GlobalRef(global)
                            if self.facts.global_read_frame(global, self.dialect) == Some(layout.base))
                    {
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

    /// 数值算术直接读取低槽并写同一 scratch；Luau 可在高一槽准备常量。
    pub(super) fn direct_numeric_arithmetic(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let source = binary.source_site?;
        let result = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_binary_layout(binary)?;
        if self.facts.operation_result_home(source) != Some(result)
            || context.barred.contains(&result)
            || context.closed.contains(&result)
            || ![
                (&binary.lhs, layout.lhs, &binary.rhs, layout.rhs),
                (&binary.rhs, layout.rhs, &binary.lhs, layout.lhs),
            ]
            .into_iter()
            .enumerate()
            .any(|(side, (value, original, constant, constant_home))| {
                (if constant_home.is_none() {
                    context.constants_fit_rk
                } else {
                    // O0 的 RHS 和位于左侧的常量都可能显式准备；另一侧是低槽
                    // binding 时，LOADK 仍占结果上一槽。左常量还须由 use→Def
                    // 确认该次准备，不能通过交换操作数绕过它或改变元方法方向。
                    self.dialect == DecompileDialect::Luau
                        && constant_home == Some(HomeSlotKey::new(slot + 1, 0))
                        && (side == 0
                            || self
                                .facts
                                .operation_input_preparation(source, constant)
                                .map(|(_, home)| home)
                                == constant_home)
                }) && matches!(constant, HirExpr::Integer(_) | HirExpr::Number(_))
                    && self
                        .direct_home(value)
                        .is_some_and(|home| home.slot() < self.base && original == Some(home))
            })
        {
            // 候选拒绝[ProofIncomplete]：需要同槽结果、原低槽读取，以及内嵌或相邻的
            // 数值常量准备；其它 operand scratch 或开放结果 cell 不由该协议覆盖。
            return None;
        }
        // 不展开低槽 producer，元方法与先前返回项的顺序不变。
        Some(HirExpr::Binary(Box::new(binary.clone())))
    }

    /// Luau 直接读取低槽操作数，或在结果上方准备输入；常量按原 RK/LOADK 布局重发。
    pub(super) fn luau_prepared_arithmetic(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let home = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_binary_layout(binary)?;
        let direct = |value: &HirExpr, original| {
            self.direct_home(value)
                .is_some_and(|input| input.slot() < self.base && original == Some(input))
        };
        let lhs_low = direct(&binary.lhs, layout.lhs);
        let rhs_low = direct(&binary.rhs, layout.rhs);
        let rhs_constant = matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
            && (layout.rhs.is_none()
                || self
                    .facts
                    .operation_input_preparation(binary.source_site?, &binary.rhs)
                    .is_some_and(|(_, prepared)| {
                        Some(prepared) == layout.rhs
                            && prepared == HomeSlotKey::new(slot + 1 + usize::from(!lhs_low), 0)
                    }));
        if self.dialect != DecompileDialect::Luau
            || !self.native?.constants_fit_rk
            || (self.native?.barred.contains(&home)
                && !self
                    .facts
                    .operation_result_reference_unaliased(binary.source_site?))
            || self.native?.closed.contains(&home)
            || self.facts.operation_result_home(binary.source_site?) != Some(home)
            || (!lhs_low && layout.lhs != Some(HomeSlotKey::new(slot + 1, 0)))
            || (!rhs_low
                && !rhs_constant
                && layout.rhs != Some(HomeSlotKey::new(slot + 1 + usize::from(!lhs_low), 0)))
        {
            return None;
        }
        // 低槽只借用同一绑定，不展开 producer。复合左侧仍逐层重发原 scratch，
        // 保持每次元方法的顺序与覆盖点，不能将它提前写进最终结果槽。
        let prepared_lhs = match &binary.lhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .map_or(&binary.lhs, |(_, value)| value),
            value => value,
        };
        let lhs = if lhs_low {
            binary.lhs.clone()
        } else if matches!(prepared_lhs, HirExpr::UpvalueRef(_)) {
            // GETUPVAL 的身份来自本次运算的 use→Def；不能将同名 cell 的另一读取
            // 当成准备值，也不跨过原算术的观察边界重新读取。
            let (producer, prepared) = self
                .facts
                .operation_input_preparation(binary.source_site?, prepared_lhs)?;
            if prepared != HomeSlotKey::new(slot + 1, 0) {
                return None;
            }
            let previous = std::mem::replace(&mut self.register_operand, false);
            let rebuilt = self.expr(
                &binary.lhs,
                before,
                slot + 1,
                None,
                false,
                true,
                Some(producer),
            );
            self.register_operand = previous;
            rebuilt?
        } else {
            self.binary_register_operand(binary, 0, before, slot + 1)?
        };
        let rhs = if rhs_low || rhs_constant {
            binary.rhs.clone()
        } else {
            self.binary_register_operand(binary, 1, before, slot + 1 + usize::from(!lhs_low))?
        };
        Some(HirExpr::Binary(Box::new(
            crate::hir::common::HirBinaryExpr {
                lhs,
                rhs,
                ..binary.clone()
            },
        )))
    }

    /// 原算术 use 读取的 phi 将 MOVE 预写交给完整操作数，不让内部值树先截断准备区。
    fn binary_register_operand(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let value = [&binary.lhs, &binary.rhs][operand];
        if let Some(result) = self.facts.binary_value_operand(binary, operand)
            && self.facts.copy_value_prewrite(result).is_some()
        {
            let previous = std::mem::replace(&mut self.register_operand, true);
            let rebuilt = self.expr(value, before, slot, None, false, true, Some(result));
            self.register_operand = previous;
            rebuilt
        } else {
            self.register_operand(value, before, slot)
        }
    }

    /// 已树化的全局字段不消费外部 producer；只在原同槽 GETGLOBAL/GETTABLE
    /// 布局可完整重发时供已完成数组的只读证明使用。
    pub(super) fn completed_global_lookup(&self, value: &HirExpr, slot: usize) -> bool {
        let HirExpr::TableAccess(access) = value else {
            return false;
        };
        let HirExpr::GlobalRef(global) = &access.base else {
            return false;
        };
        let Some(context) = self.native else {
            return false;
        };
        let home = HomeSlotKey::new(slot, 0);
        self.literal_uses_rk(&access.key, Some((&access.sources, false))) == Some(true)
            && !context.closed.contains(&home)
            && self.facts.global_read_frame(global, self.dialect) == Some(home)
            && self.facts.table_read_result_home(access) == Some(home)
            && self
                .facts
                .native_table_read_layout(access)
                .is_some_and(|layout| layout.base == home && layout.key.is_none())
            && matches!(&access.key, HirExpr::String(key)
                if self.dialect != DecompileDialect::Luau
                    || key.as_utf8().is_some_and(|key| self.dialect.is_identifier_name(key)))
            && (!context.barred.contains(&home)
                || access
                    .sources
                    .try_for_each_known(|source| {
                        self.facts
                            .operation_result_reference_unaliased(source)
                            .then_some(())
                    })
                    .is_some())
    }

    pub(super) fn register_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        if let Some(home) = self.facts.upvalue_table_read_frame(access) {
            // GETTABUP 已直接读取原 cell 和原键，不存在需要重放的 base 寄存器。
            // 算术/赋值仍在完整帧内消费该结果，不能因此移动读取或消除写回后的再读。
            return (home == HomeSlotKey::new(slot, 0)
                && self.native?.constants_fit_rk
                && !self.native?.closed.contains(&home))
            .then(|| HirExpr::TableAccess(Box::new(access.clone())));
        }
        let layout = self.facts.native_table_read_layout(access)?;
        if self.dialect == DecompileDialect::Luau
            && self.native?.expanded_callees.is_some()
            && layout.base == HomeSlotKey::new(slot + 2, 0)
        {
            return self
                .expanded_index(access, before, slot)
                .map(|(call, _)| HirExpr::Call(Box::new(call)));
        }
        let result = self.facts.table_read_result_home(access)?;
        // 未来同槽 capture 不能反向阻止这次读取；只有原操作尚未打开 ByRef 时才可借证。
        // 当前声明/捕获身份及后继窗口仍由完整帧的原子 preview 验证。
        if result.slot() != slot
            || (self.native?.barred.contains(&result)
                && !matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if self.facts.operation_result_reference_unaliased(source)))
            || self.native?.closed.contains(&result)
        {
            return None;
        }
        let direct_base = self
            .facts
            .table_read_base_home(access)
            .is_some_and(|home| home == layout.base && home.slot() < self.base);
        // PUC 的计算左值预留 base 槽，key 的 CALL 可先借该槽，再把字段结果写到 key 槽；
        // indexed owner 会在 key 完成后重发原目标读取，不能把中间 CALL 固定成声明。
        let indexed_base = self.indexed_key_base == Some(layout.base.slot())
            && result == HomeSlotKey::new(layout.base.slot() + 1, 0)
            && layout.key.is_none();
        if !direct_base && layout.base != result && !indexed_base {
            // 候选拒绝[ProofIncomplete]：高槽 base 必须在当前结果槽完成，不能省略不同槽快照。
            return None;
        }
        let base = if direct_base {
            access.base.clone()
        } else if let Some(home) = self.prepared_upvalue_lookup_base(access) {
            if home != layout.base {
                return None;
            }
            // GETUPVAL 的单次 Def 仍在原 base 槽准备；不能将同名上值当成既有低槽。
            access.base.clone()
        } else if let HirExpr::TempRef(temp) = access.base {
            if self.facts.table_read_base_value(access) != Some(temp) {
                return None;
            }
            let previous = std::mem::replace(&mut self.register_operand, true);
            let base = self.expr(
                &access.base,
                before,
                layout.base.slot(),
                None,
                false,
                true,
                Some(temp),
            );
            self.register_operand = previous;
            base?
        } else if let HirExpr::LocalRef(local) = access.base
            && self
                .definition(local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .is_some_and(|(_, value)| matches!(value, HirExpr::UpvalueRef(_)))
        {
            // 尚未树化的 GETUPVAL 也是原 base 准备；按这次 use 的 Def 消费，
            // 不能要求它先通过禁止裸上值的通用寄存器 operand 入口。
            let producer = self.facts.table_read_base_value(access)?;
            let previous = std::mem::replace(&mut self.register_operand, false);
            let base = self.expr(
                &access.base,
                before,
                layout.base.slot(),
                None,
                false,
                true,
                Some(producer),
            );
            self.register_operand = previous;
            base?
        } else {
            self.register_operand(
                &access.base,
                before,
                if indexed_base {
                    layout.base.slot()
                } else {
                    slot
                },
            )?
        };
        let key = if let Some(home) = layout.key {
            let direct_key = self
                .direct_home(&access.key)
                .is_some_and(|key| key == home && key.slot() < self.base);
            let key_slot =
                slot + usize::from(!direct_base || self.dialect == DecompileDialect::Luau);
            if !direct_key && home.slot() != key_slot {
                return None;
            }
            if self.dialect == DecompileDialect::Luau
                && tables::literal_rk(&access.key)
                && self.facts.table_key_preparation(access) == Some(home)
            {
                // O0 在结果上方显式加载原字面键；该 use→Def 不能被当作可省略的 RK。
                access.key.clone()
            } else if matches!(access.key, HirExpr::UpvalueRef(_))
                && !matches!(
                    self.dialect,
                    DecompileDialect::Luau | DecompileDialect::Luajit
                )
                && self.facts.table_key_preparation(access) == Some(home)
            {
                // 原 GETUPVAL 只供本次索引使用，仍在 key_slot 重发；base 已在上方验证。
                access.key.clone()
            } else if let Some((producer, preparation)) =
                self.facts.table_key_value_preparation(access)
                && preparation == home
                && {
                    let prepared = match &access.key {
                        HirExpr::LocalRef(local) => {
                            self.definition(*local, before).and_then(|index| {
                                scalar_local(self.run[index]).map(|(_, value)| value)
                            })
                        }
                        value => Some(value),
                    };
                    prepared.is_some_and(|value| {
                        tables::literal_rk(value)
                            && self.literal_uses_rk(value, Some((&access.sources, false)))
                                == Some(false)
                    })
                }
            {
                // 池满后的 key 仍在原高槽 LOADK/LOADBOOL；沿唯一 use→Def
                // 消费尚未树化的准备 local，不把它误判成应保留的普通 COPY。
                self.expr(
                    &access.key,
                    before,
                    key_slot,
                    None,
                    false,
                    true,
                    Some(producer),
                )?
            } else {
                self.register_operand(&access.key, before, key_slot)?
            }
        } else {
            if self.literal_uses_rk(&access.key, Some((&access.sources, false))) != Some(true)
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

    /// 原 GETUPVAL→GETTABLE 的 base 准备；直接 GETTABUP 没有这个寄存器输入。
    pub(super) fn prepared_upvalue_lookup_base(
        &self,
        access: &HirTableAccess,
    ) -> Option<HomeSlotKey> {
        if !matches!(access.base, HirExpr::UpvalueRef(_)) {
            return None;
        }
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        self.facts
            .operation_input_preparation(source, &access.base)
            .map(|(_, home)| home)
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
                if self
                    .facts
                    .global_read_frame(global, self.dialect)
                    .is_none_or(|home| home.slot() != slot) =>
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

    /// PUC/JIT 在结果槽准备复合左值，相邻槽准备右值；逐层核对原读写与事件。
    pub(super) fn register_arithmetic(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let result = self.facts.operation_result_home(binary.source_site?)?;
        if result.slot() != slot
            || (self.native?.barred.contains(&result)
                && !self
                    .facts
                    .operation_result_reference_unaliased(binary.source_site?))
            || self.native?.closed.contains(&result)
        {
            return None;
        }
        let layout = self.facts.native_binary_layout(binary)?;
        let sources = crate::hir::common::HirOperationSources::Single(binary.source_site?);
        let direct = |value: &HirExpr, home| {
            self.direct_home(value)
                .is_some_and(|actual| Some(actual) == home && actual.slot() < self.base)
        };
        let lhs_low = direct(&binary.lhs, layout.lhs);
        let rhs_low = direct(&binary.rhs, layout.rhs);
        let constant = |value: &HirExpr| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_));
        let lhs = if layout.lhs.is_none() && constant(&binary.lhs) {
            if self.literal_uses_rk(&binary.lhs, Some((&sources, false))) != Some(true) {
                return None;
            }
            binary.lhs.clone()
        } else {
            if !lhs_low && layout.lhs != Some(result) {
                return None;
            }
            let prepared = match &binary.lhs {
                HirExpr::LocalRef(local) => self
                    .definition(*local, before)
                    .and_then(|index| scalar_local(self.run[index]))
                    .map_or(&binary.lhs, |(_, value)| value),
                value => value,
            };
            if matches!(
                prepared,
                HirExpr::UpvalueRef(_) | HirExpr::Integer(_) | HirExpr::Number(_)
            ) && !lhs_low
            {
                // 上值和字面量没有独立的表达式来源；用原 use→Def 证明输入在
                // 结果槽准备。尤其 0 / 0 不可折叠，左侧仍须重发原 LOADI。
                let (producer, home) = self
                    .facts
                    .operation_input_preparation(binary.source_site?, prepared)?;
                if home != result {
                    return None;
                }
                // 准备写可能已提升成匿名 Local；消费同一个原输入 Def 的声明，
                // 不能让通用寄存器操作数入口把这份已证明的读取重新拒绝。
                let previous = std::mem::replace(&mut self.register_operand, false);
                let rebuilt =
                    self.expr(&binary.lhs, before, slot, None, false, true, Some(producer));
                self.register_operand = previous;
                rebuilt?
            } else {
                self.register_operand(&binary.lhs, before, slot)?
            }
        };
        let rhs_slot = slot + usize::from(!lhs_low && layout.lhs.is_some());
        let rhs = if layout.rhs.is_none() && constant(&binary.rhs) {
            if self.literal_uses_rk(&binary.rhs, Some((&sources, true))) != Some(true) {
                return None;
            }
            binary.rhs.clone()
        } else {
            if !rhs_low && layout.rhs != Some(HomeSlotKey::new(rhs_slot, 0)) {
                return None;
            }
            let prepared = match &binary.rhs {
                HirExpr::LocalRef(local) => self
                    .definition(*local, before)
                    .and_then(|index| scalar_local(self.run[index]))
                    .map_or(&binary.rhs, |(_, value)| value),
                value => value,
            };
            if !rhs_low
                && constant(prepared)
                && matches!(
                    self.dialect,
                    DecompileDialect::Lua51 | DecompileDialect::Lua52 | DecompileDialect::Lua53
                )
            {
                if self.literal_uses_rk(prepared, Some((&sources, true))) != Some(false) {
                    return None;
                }
                let (producer, home) = self
                    .facts
                    .operation_input_preparation(binary.source_site?, prepared)?;
                if Some(home) != layout.rhs {
                    return None;
                }
                let previous = std::mem::replace(&mut self.register_operand, false);
                let rebuilt = self.expr(
                    &binary.rhs,
                    before,
                    rhs_slot,
                    None,
                    false,
                    true,
                    Some(producer),
                );
                self.register_operand = previous;
                rebuilt?
            } else {
                self.register_operand(&binary.rhs, before, rhs_slot)?
            }
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
