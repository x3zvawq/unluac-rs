//! 在完整源码帧中恢复索引、比较和算术输入准备。
//!
//! 消费 Promotion 的原定义与布局，由共享 FrameBuilder 验证事件顺序和声明身份。

use super::*;
use crate::hir::common::HirTableAccess;

impl FrameBuilder<'_> {
    /// Luau 先保留 Boolean 目标，再准备算术、上值或单值 VARARG，最后准备比较右值。
    /// 返回操作数所在侧及读取 Def；LocalRef 仍由共享 builder 按事件游标消费。
    pub(super) fn luau_prepared_comparison_operand(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<(bool, Option<crate::hir::common::TempId>)> {
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
                HirExpr::String(_) | HirExpr::Nil | HirExpr::Boolean(_) => {
                    binary.op == Eq && left && constant_home.is_none()
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
            match value {
                HirExpr::Call(call) => {
                    let producer = self.expanded_call_result(call)?;
                    (self.facts.binary_value_operand(binary, usize::from(!left)) == Some(producer)
                        && self.facts.trusted_temp_home_slot(producer)
                            == Some(HomeSlotKey::new(operand_slot, 0)))
                    .then_some((left, Some(producer)))
                }
                HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
                    let producer = self.facts.binary_phi_operand(binary, usize::from(!left))?;
                    ((self.native?.compared_choices.is_some()
                        && self.facts.compared_literal_choice(producer).is_some()
                        || self.has_value_expression(producer))
                        && self.facts.trusted_temp_home_slot(producer)
                            == Some(HomeSlotKey::new(operand_slot, 0)))
                    .then_some((left, Some(producer)))
                }
                HirExpr::Binary(arithmetic) => {
                    // 这里只选择原算术结果；输入准备、写域和消费事件由随后的 expr 验证，
                    // 不能要求它预先属于“低槽与常量”的更窄协议。
                    (numeric_rk_arithmetic(arithmetic)
                        && self.facts.operation_result_home(arithmetic.source_site?)
                            == Some(HomeSlotKey::new(operand_slot, 0)))
                    .then_some((left, None))
                }
                HirExpr::UpvalueRef(_) | HirExpr::VarArg => {
                    // 有序比较在 HIR 中可反向表达，但 GETUPVAL 必须仍先于常量准备。
                    // 携带这次 use 的原 Def；VARARG 的固定单结果宽度由同一准备证书签发。
                    let (producer, home) =
                        self.facts
                            .binary_operand_preparation(binary, usize::from(!left), value)?;
                    (home == HomeSlotKey::new(operand_slot, 0)).then_some((left, Some(producer)))
                }
                _ => None,
            }
        })
    }

    /// 比较参数的物化位置来自当前 Boolean 值树或原单比较 phi，不从 operand 槽猜结果。
    fn jit_boolean_result_home(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> Option<HomeSlotKey> {
        (self.dialect == DecompileDialect::Luajit).then_some(())?;
        self.boolean_frame
            .filter(|home| home.slot() == slot)
            .or_else(|| {
                self.facts
                    .comparison_result_temp(binary)
                    .and_then(|result| self.facts.trusted_temp_home_slot(result))
                    .filter(|home| home.slot() == slot)
            })
    }

    /// JIT 有序关系的数字常量占寄存器，Eq 的常量则内嵌。已有 RI operand 先在结果槽
    /// 求值时，常量必须位于相邻后一槽；例如 `2 <= bits % 4` 保留 MOD 后的 LOADK。
    pub(super) fn jit_scalar_comparison(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        let Some(home) = self.jit_boolean_result_home(binary, slot) else {
            return false;
        };
        if !matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
            return false;
        }
        let Some(layout) = self.facts.native_binary_layout(binary) else {
            return false;
        };
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
                    constant_home
                        == Some(if scratch {
                            HomeSlotKey::new(slot + 1, 0)
                        } else {
                            home
                        })
                })
        })
    }

    /// KCDATA 不是 Eq 的内嵌常量：每个高槽输入仍须按原 use→Def 重发，
    /// Boolean 写回使用同一准备区的首槽。低槽现成输入不占准备槽。
    pub(super) fn jit_cdata_comparison_preparations(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<[Option<crate::hir::common::TempId>; 2]> {
        use crate::hir::common::HirBinaryOpKind::{Eq, Le, Lt};
        self.jit_boolean_result_home(binary, slot)?;
        if !matches!(binary.op, Eq | Lt | Le) {
            return None;
        }
        let layout = self.facts.native_binary_layout(binary)?;
        let mut preparations = [None; 2];
        let mut scratch = slot;
        for (index, (value, original)) in [&binary.lhs, &binary.rhs]
            .into_iter()
            .zip([layout.lhs, layout.rhs])
            .enumerate()
        {
            if self
                .facts
                .direct_binary_operand_home(binary, index)
                .is_some_and(|home| home.slot() < self.base && original == Some(home))
            {
                continue;
            }
            let prepared = match value {
                HirExpr::LocalRef(local) => {
                    scalar_local(self.run[self.definition(*local, before)?])?.1
                }
                value => value,
            };
            if !matches!(
                prepared,
                HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Complex { .. }
            ) {
                return None;
            }
            let (producer, home) = self
                .facts
                .binary_operand_preparation(binary, index, prepared)?;
            if original != Some(home) || home.slot() != scratch {
                return None;
            }
            preparations[index] = Some(producer);
            scratch += 1;
        }
        (scratch > slot).then_some(preparations)
    }

    /// JIT 比较参数复用首个 lookup 的槽；第二个 lookup 才占其相邻后一槽。
    /// `assert(t[1] == value and t[2] == nil)` 保留原 TGETB、低槽读取与 Boolean 写回；
    /// 不消费 run 中的新 producer；动态键须由原输入准备证明，不能借先前 COPY 的槽。
    pub(super) fn jit_lookup_comparison(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        let Some(home) = self.jit_boolean_result_home(binary, slot) else {
            return false;
        };
        if binary.op != crate::hir::common::HirBinaryOpKind::Eq {
            return false;
        }
        let Some(layout) = self.facts.native_binary_layout(binary) else {
            return false;
        };
        let lookup = |value: &HirExpr, home: HomeSlotKey| matches!(value, HirExpr::TableAccess(access) if self.jit_direct_lookup(access, home));
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

    /// Luau 的整数索引先保留结果，再由 compileExprAuto 在预留区之后调用 base；
    /// 外层具名字段在临时结果槽原位继续读取。只消费原嵌入键和完整单结果 CALL，
    /// 动态键也先保留结果：现成 base/key 直接读取，复合输入依次在高槽准备；
    /// 原 RK 算术须逐项核对输入和输出。
    pub(super) fn luau_lookup(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let result = HomeSlotKey::new(slot, 0);
        let scratch = self.declaration_reserved_top.unwrap_or(0).max(slot + 1);
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
            let direct_key = self
                .direct_home(&access.key)
                .is_some_and(|home| home == key_home && home.slot() < self.base);
            if !direct {
                // Luau 为动态索引保留结果槽，再依次准备 base 与 key；key 回调
                // 可以改写 base 的来源，不能在 key 之后重新读取它。
                if layout.base != HomeSlotKey::new(scratch, 0)
                    || !direct_key && key_home != HomeSlotKey::new(scratch + 1, 0)
                {
                    return None;
                }
                let base = self.register_table_base(access, before, scratch)?;
                // compileExprAuto 对既有 local/param 直接用原槽；它不因复合 base
                // 占用高槽就额外复制 key。仍在 base 求值后读取同一 binding。
                let key = if direct_key
                    || tables::literal_rk(&access.key)
                        && self.facts.table_key_preparation(access) == Some(key_home)
                {
                    // 非嵌入整数及 O0 字面键仍在 base 之后加载；原 key use→Def
                    // 证明此处重发同一常量，不能按字面值外形省略准备槽。
                    access.key.clone()
                } else {
                    self.luau_lookup_key(access, before, key_home)?
                };
                return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                    base,
                    key,
                    ..access.clone()
                })));
            }
            if !direct_key && key_home != HomeSlotKey::new(scratch, 0) {
                return None;
            }
            // 动态 key 的结果槽在 GETTABLE 结果上方；共享 operand builder
            // 继续核对算术、LEN 等原操作的输入，不能按表达式形状假定可移动。
            let key = if direct_key
                || tables::literal_rk(&access.key)
                    && self.facts.table_key_preparation(access) == Some(key_home)
            {
                access.key.clone()
            } else {
                self.luau_lookup_key(access, before, key_home)?
            };
            return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                key,
                ..access.clone()
            })));
        }
        let mut preserve_index_syntax = access.preserve_index_syntax;
        let base = match &access.key {
            HirExpr::String(_) if direct => access.base.clone(),
            HirExpr::String(_) if layout.base == HomeSlotKey::new(scratch, 0) => {
                // compileExprIndexExpr 保留结果槽，再在高槽准备 base；点语法的
                // compileExprIndexName 会复用结果槽，必须把已证明的方括号形式交给 AST。
                preserve_index_syntax = true;
                self.register_table_base(access, before, scratch)?
            }
            HirExpr::String(key)
                if layout.base == result
                    && key
                        .as_utf8()
                        .is_some_and(|name| self.dialect.is_identifier_name(name)) =>
            {
                let base = self.register_table_base(access, before, slot)?;
                // 显式全局快照并入点访问会启用 GETIMPORT；同槽不足以证明其原
                // 读取协议和声明写回。这里只扩展已有 CALL/字段链的 GETUPVAL 准备。
                if !matches!(
                    base,
                    HirExpr::Call(_) | HirExpr::TableAccess(_) | HirExpr::UpvalueRef(_)
                ) {
                    return None;
                }
                base
            }
            HirExpr::Integer(key) if (1..=256).contains(key) => {
                if direct {
                    access.base.clone()
                } else {
                    // 声明组或 CALL 已预留结果区；嵌套数字索引的 base 从当前
                    // freereg 准备，不能误用目标槽的紧邻位置覆盖其它结果。
                    if layout.base != HomeSlotKey::new(scratch, 0) {
                        return None;
                    }
                    self.register_table_base(access, before, scratch)?
                }
            }
            _ => return None,
        };
        Some(HirExpr::TableAccess(Box::new(HirTableAccess {
            base,
            preserve_index_syntax,
            ..access.clone()
        })))
    }

    /// 原 GETTABLE 的显式常量键也可尚未树化；保留其唯一 Def 和准备事件。
    fn luau_lookup_key(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        home: HomeSlotKey,
    ) -> Option<HirExpr> {
        let prepared = match &access.key {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .map(|(_, value)| value),
            value => Some(value),
        };
        if let Some(value) = prepared.filter(|value| tables::literal_rk(value)) {
            let (producer, original) = self.facts.table_key_value_preparation(access)?;
            // 候选拒绝[ProofIncomplete]：当前常量和别名必须共同指向本次 key use 的
            // 同一准备定义，不能因复用槽或同值常量就跨过另一次初始化。
            if original != home
                || self.facts.table_key_input_preparation(access, value) != Some((producer, home))
            {
                return None;
            }
            // 与已树化的字面键相同，原布局已证明它占寄存器。通用 register_operand
            // 禁止常量以避免擅自改成 RK；此处由查表自己的 use→Def 重发 LOADK/LOADN。
            self.expr(
                &access.key,
                before,
                home.slot(),
                None,
                false,
                true,
                Some(producer),
            )
        } else {
            self.register_operand(&access.key, before, home.slot())
        }
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
        let home = self.facts.operation_result_home(binary.source_site?)?;
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
                    .binary_operand_preparation(binary, 1, &binary.rhs)
                    .is_some_and(|(_, prepared)| {
                        Some(prepared) == layout.rhs
                            && prepared.slot() == slot + 1 + usize::from(!lhs_low)
                    }));
        if self.dialect != DecompileDialect::Luau
            || !self.native?.constants_fit_rk
            || (self.native?.barred.contains(&home)
                && !self
                    .facts
                    .operation_result_reference_unaliased(binary.source_site?))
            || self.native?.closed.contains(&home)
            || home.slot() != slot
            || (!lhs_low && layout.lhs.is_none_or(|home| home.slot() != slot + 1))
            || (!rhs_low
                && !rhs_constant
                && layout
                    .rhs
                    .is_none_or(|home| home.slot() != slot + 1 + usize::from(!lhs_low)))
        {
            return None;
        }
        // 低槽只借用同一绑定，不展开 producer。复合左侧仍逐层重发原 scratch，
        // 保持每次元方法的顺序与覆盖点，不能将它提前写进最终结果槽。
        let lhs = if lhs_low {
            binary.lhs.clone()
        } else {
            self.binary_register_operand(binary, 0, before, layout.lhs?)?
        };
        let rhs = if rhs_low || rhs_constant {
            binary.rhs.clone()
        } else {
            self.binary_register_operand(binary, 1, before, layout.rhs?)?
        };
        Some(HirExpr::Binary(Box::new(
            crate::hir::common::HirBinaryExpr {
                lhs,
                rhs,
                ..binary.clone()
            },
        )))
    }

    /// 原算术 use 读取的 phi 连同准备写交给完整操作数，保留尚未提升的 Temp 身份。
    fn binary_register_operand(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        operand: usize,
        before: usize,
        expected: HomeSlotKey,
    ) -> Option<HirExpr> {
        let slot = expected.slot();
        let value = [&binary.lhs, &binary.rhs][operand];
        let prepared = match value {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .map_or(value, |(_, value)| value),
            value => value,
        };
        if matches!(
            prepared,
            HirExpr::UpvalueRef(_) | HirExpr::Integer(_) | HirExpr::Number(_)
        ) {
            // GETUPVAL 和数字 LOAD 都由本次运算的对应 use→Def 取得准备身份；
            // 0/0 的两次相同常量写仍属于不同操作数，不能按值匹配成模糊输入。
            let (producer, home) = self
                .facts
                .binary_operand_preparation(binary, operand, prepared)?;
            if home != expected {
                return None;
            }
            let previous = std::mem::replace(&mut self.register_operand, false);
            let rebuilt = self.expr(value, before, slot, None, false, true, Some(producer));
            self.register_operand = previous;
            rebuilt
        } else if let Some(result) = self.facts.binary_phi_operand(binary, operand)
            && (self.facts.copy_value_prewrite(result).is_some()
                || matches!(value, HirExpr::TempRef(temp) if *temp == result)
                || matches!(value, HirExpr::LocalRef(local)
                    if self.facts.promoted_local_for_temp(result) == Some(*local)))
            && self.facts.trusted_temp_home_slot(result) == Some(expected)
        {
            // 当前绑定必须属于这次原 phi 读取；递归 builder 再核对完整写域和事件，
            // 不以相同槽号代替版本身份，也不要求合流值拥有单条 producer 指令。
            let previous = std::mem::replace(&mut self.register_operand, true);
            let rebuilt = self.expr(value, before, slot, None, false, true, Some(result));
            self.register_operand = previous;
            rebuilt
        } else {
            // 输入和结果可以各自属于 CLOSE 后的新 epoch；槽距只约束布局，
            // 算术 Def 的完整 home 仍须与这次 use 一致，不能从结果 epoch 推导输入。
            let home = if let HirExpr::Binary(input) = prepared {
                self.facts
                    .comparison_result_temp(input)
                    .and_then(|temp| self.facts.trusted_temp_home_slot(temp))
                    .or_else(|| {
                        input
                            .source_site
                            .and_then(|source| self.facts.operation_result_home(source))
                    })?
            } else {
                // 其它复合输入仍使用现有零 epoch 协议；不凭槽号扩展未证明的准备域。
                HomeSlotKey::new(slot, 0)
            };
            if home != expected {
                return None;
            }
            self.register_operand(value, before, slot)
        }
    }

    /// 已树化的全局字段不消费外部 producer；只在原同槽 GETGLOBAL/GETTABLE
    /// 布局可完整重发时供完整表达式帧的只读证明使用。
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
        if let Some((producer, home)) = self.facts.upvalue_table_read_key(access) {
            // GETTABUP 不占 base 寄存器，动态 key 在结果槽准备后由原操作覆盖；
            // 保留其精确 Def，不能把这个布局按普通 GETTABLE 的 base/key 双槽重放。
            let result = self.facts.table_read_result_home(access)?;
            if home != result
                || result.slot() != slot
                || self.native?.closed.contains(&result)
                || !matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if self.facts.operation_result_reference_unaliased(source))
            {
                return None;
            }
            let previous = std::mem::replace(&mut self.register_operand, false);
            let key = self.expr(&access.key, before, slot, None, false, true, Some(producer));
            self.register_operand = previous;
            return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                key: key?,
                ..access.clone()
            })));
        }
        let layout = self.facts.native_table_read_layout(access)?;
        if self.dialect == DecompileDialect::Luau
            && (layout.base == HomeSlotKey::new(slot + 1, 0)
                || layout.base.slot() > slot
                    && self.declaration_reserved_top == Some(layout.base.slot()))
        {
            // Luau 在结果上方准备 base；generic-for 预留的控制帧会把 freereg
            // 推得更高。两者都由 luau_lookup 核对，不能递归时退回同槽 base 规则。
            return self.luau_lookup(access, before, slot);
        }
        if matches!(
            self.dialect,
            DecompileDialect::Lua54 | DecompileDialect::Lua55
        ) && let Some((producer, home)) = self.facts.table_read_late_upvalue_base(access)
        {
            let result = self.facts.table_read_result_home(access)?;
            if result.slot() != slot
                || self.native?.closed.contains(&home)
                || self.native?.closed.contains(&result)
            {
                return None;
            }
            // 原动态 key 先完成，再读取上值 base；高槽 key 的一元操作可借用
            // 尚未读取 base 的结果槽。许可只覆盖本次原布局，不提前合并两次 cell 读取。
            let previous = std::mem::replace(&mut self.register_operand, false);
            let previous_key_base = self.indexed_key_base;
            self.indexed_key_base = Some(slot);
            let key = self.expr(
                &access.key,
                before,
                home.slot(),
                None,
                false,
                true,
                Some(producer),
            );
            self.indexed_key_base = previous_key_base;
            self.register_operand = previous;
            return Some(HirExpr::TableAccess(Box::new(HirTableAccess {
                key: key?,
                ..access.clone()
            })));
        }
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
        } else if matches!(access.base, HirExpr::UpvalueRef(_))
            && let Some(home) = self.prepared_upvalue_lookup_base(access, before)
        {
            if home != layout.base {
                return None;
            }
            // GETUPVAL 的单次 Def 仍在原 base 槽准备；不能将同名上值当成既有低槽。
            access.base.clone()
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
            self.register_table_base(
                access,
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
            } else if let HirExpr::LocalRef(local) = access.key
                && !matches!(
                    self.dialect,
                    DecompileDialect::Luau | DecompileDialect::Luajit
                )
                && self
                    .definition(local, before)
                    .and_then(|index| scalar_local(self.run[index]))
                    .is_some_and(|(_, value)| matches!(value, HirExpr::UpvalueRef(_)))
                && let Some((producer, preparation)) =
                    self.facts.table_key_value_preparation(access)
                && preparation == home
            {
                // 与 base 一样，尚未树化的 GETUPVAL 必须匹配这次 key use 的原 Def；
                // 完整准备区仍检查事件顺序，不把任意上值读取当作可移动的寄存器值。
                let previous = std::mem::replace(&mut self.register_operand, false);
                let key = self.expr(
                    &access.key,
                    before,
                    key_slot,
                    None,
                    false,
                    true,
                    Some(producer),
                );
                self.register_operand = previous;
                key?
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
                            && self.table_key_uses_rk(access, value) == Some(false)
                    })
                }
            {
                // 池满或命名变参的 key 仍在原高槽 LOADK/LOADBOOL；沿唯一 use→Def
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
            if self.table_key_uses_rk(access, &access.key) != Some(true)
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
            preserve_index_syntax: access.preserve_index_syntax,
        })))
    }

    /// 尚未提升的 base 仍绑定原 GETTABLE use→Def；递归消费时保留其 producer。
    fn register_table_base(
        &mut self,
        access: &HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let prepared = match &access.base {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .map_or(&access.base, |(_, value)| value),
            value => value,
        };
        if matches!(prepared, HirExpr::UpvalueRef(_)) {
            let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
                return None;
            };
            let (producer, home) = self.facts.operation_input_preparation(source, prepared)?;
            if home != HomeSlotKey::new(slot, 0) {
                return None;
            }
            // 同名上值可被 key/元方法改写；只消费原 GETTABLE 使用的这次 GETUPVAL。
            let previous = std::mem::replace(&mut self.register_operand, false);
            let base = self.expr(
                &access.base,
                before,
                slot,
                None,
                false,
                true,
                Some(producer),
            );
            self.register_operand = previous;
            return base;
        }
        let HirExpr::TempRef(temp) = access.base else {
            return self.register_operand(&access.base, before, slot);
        };
        if self.facts.table_read_base_value(access) != Some(temp) {
            return None;
        }
        let previous = std::mem::replace(&mut self.register_operand, true);
        let base = self.expr(&access.base, before, slot, None, false, true, Some(temp));
        self.register_operand = previous;
        base
    }

    /// 原 GETUPVAL→GETTABLE 的 base 准备；Local 按当前定义时点查询，GETTABUP 没有此寄存器输入。
    pub(super) fn prepared_upvalue_lookup_base(
        &self,
        access: &HirTableAccess,
        before: usize,
    ) -> Option<HomeSlotKey> {
        let value = match &access.base {
            HirExpr::LocalRef(local) => {
                let index = self.definition(*local, before)?;
                scalar_local(self.run[index])?.1
            }
            value => value,
        };
        if !matches!(value, HirExpr::UpvalueRef(_)) {
            return None;
        }
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return None;
        };
        self.facts
            .operation_input_preparation(source, value)
            .map(|(_, home)| home)
    }

    /// 新增帧内操作逐层核对原输入；旧的简单字段入口不承担嵌套准备证明。
    /// 原同槽 NOT 链只在最内层准备输入；逐边核对原 Def，再从叶到根重建。
    /// 不让长链逐层进入大型 expr 分派栈，也不复制每一层尚未处理的子树。
    pub(super) fn inplace_not_chain(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let mut chain = Vec::new();
        let mut current = expr;
        let (leaf, producer) = loop {
            let HirExpr::Unary(unary) = current else {
                unreachable!("native NOT chain retains its current operation");
            };
            let home = self.facts.unary_result_home(unary)?;
            if home.slot() != slot || self.facts.unary_operand_home(unary) != Some(home) {
                return None;
            }
            let input = match &unary.expr {
                HirExpr::LocalRef(local) => {
                    scalar_local(self.run[self.definition(*local, before)?])?.1
                }
                value => value,
            };
            let (producer, input_home) = self
                .facts
                .operation_input_preparation(unary.source_site?, input)?;
            if input_home != home {
                return None;
            }
            chain.push(unary);
            if matches!(&unary.expr, HirExpr::Unary(inner)
                if inner.op == crate::hir::common::HirUnaryOpKind::Not
                    && self.facts.unary_result_home(inner) == Some(home)
                    && self.facts.unary_operand_home(inner) == Some(home))
            {
                current = &unary.expr;
            } else {
                // 链的首运算可以从既有低槽读取，或使用不同输入布局；只迭代同槽段，
                // 首叶继续交给原表达式 owner 核对，不把其合法读取强改为同槽准备。
                break (&unary.expr, producer);
            }
        };
        let mut value = self.expr(leaf, before, slot, None, false, true, Some(producer))?;
        for unary in chain.into_iter().rev() {
            value = HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                source_site: unary.source_site,
                op: unary.op,
                expr: value,
            }));
        }
        // ResourceLimit：不能在完整帧内撤销临时值阶段为目标解析器保留的长链分段。
        crate::hir::simplify::syntax_budget::unary_frame_fits(&value).then_some(value)
    }

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
        if result.slot() != slot {
            return None;
        }
        self.register_arithmetic_inputs(binary, before, result, result)
    }

    /// 输入在高槽依次准备，最终运算写回已有低槽；调用方保持目标声明及整帧提交。
    pub(super) fn register_arithmetic_writeback(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        input: HomeSlotKey,
    ) -> Option<HirExpr> {
        let (_, result) = self.facts.operation_writeback(binary.source_site?)?;
        if self.dialect == DecompileDialect::Luau || result.slot() >= input.slot() {
            return None;
        }
        self.register_arithmetic_inputs(binary, before, input, result)
    }

    /// 调用方提供原布局确认的输入与结果 home；分槽运算不得以结果 epoch 替代输入 epoch。
    pub(super) fn register_arithmetic_inputs(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        input: HomeSlotKey,
        result: HomeSlotKey,
    ) -> Option<HirExpr> {
        let slot = input.slot();
        let constant = |value: &HirExpr| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_));
        if (self.native?.barred.contains(&result)
            // 封闭数值运算不读取捕获 cell，也不调用元方法；运算及原低槽写回
            // 仍由当前事务重发，不能据此删除计算或放宽其它输入的捕获边界。
            && !(constant(&binary.lhs) && constant(&binary.rhs))
            && !self
                .facts
                .operation_result_reference_unaliased(binary.source_site?))
            // 同槽未来的资源激活不保护当前普通算术定义；输入与结果的完整
            // home 仍由本帧核对，活动资源槽及真实 TBC 注册值不能取得该证明。
            || (self.native?.closed.contains(&result)
                && !self.facts.operation_result_temp(binary.source_site?)
                    .is_some_and(|temp| self.facts.temp_definition_tbc_unprotected(temp)))
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
        if matches!(
            self.dialect,
            DecompileDialect::Lua54 | DecompileDialect::Lua55 | DecompileDialect::Luajit
        ) && result == input
            && constant(&binary.lhs)
            && layout.rhs == Some(input)
            && layout.lhs.is_some_and(|home| home.slot() == slot + 1)
        {
            // 非 RK 左常量在右值完成后才载入相邻槽，例如 PUC 5.4+ 的 1/f()
            // 或 LuaJIT 的 2^f()。常量没有自身事件，但其准备槽不能提前覆盖。
            // 原两个输入的 use→Def 与准备次序共同签证，保留运算方向和回调看到的覆盖时点。
            let right_value = match &binary.rhs {
                HirExpr::LocalRef(local) => self
                    .definition(*local, before)
                    .and_then(|index| scalar_local(self.run[index]))
                    .map_or(&binary.rhs, |(_, value)| value),
                value => value,
            };
            let (right, right_home) =
                self.facts
                    .binary_operand_preparation(binary, 1, right_value)?;
            let (left, left_home) =
                self.facts
                    .binary_operand_preparation(binary, 0, &binary.lhs)?;
            if right_home != input
                || Some(left_home) != layout.lhs
                || self
                    .facts
                    .binary_preparation_instruction(binary, 0, &binary.lhs)?
                    <= self
                        .facts
                        .binary_preparation_instruction(binary, 1, right_value)?
            {
                // 候选拒绝[ProofIncomplete]：早已准备的左快照不能改成右值调用后的新常量写。
                return None;
            }
            let previous = std::mem::replace(&mut self.register_operand, false);
            let values = (|| {
                let rhs = self.expr(&binary.rhs, before, slot, None, false, true, Some(right))?;
                let lhs = self.expr(
                    &binary.lhs,
                    before,
                    left_home.slot(),
                    None,
                    false,
                    true,
                    Some(left),
                )?;
                Some((lhs, rhs))
            })();
            self.register_operand = previous;
            let (lhs, rhs) = values?;
            return Some(HirExpr::Binary(Box::new(
                crate::hir::common::HirBinaryExpr {
                    lhs,
                    rhs,
                    source_site: binary.source_site,
                    op: binary.op,
                },
            )));
        }
        let lhs = if layout.lhs.is_none() && constant(&binary.lhs) {
            if self.literal_uses_rk(&binary.lhs, Some((&sources, false))) != Some(true) {
                return None;
            }
            binary.lhs.clone()
        } else {
            if !lhs_low && layout.lhs != Some(input) {
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
                HirExpr::UpvalueRef(_)
                    | HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::Int64(_)
                    | HirExpr::UInt64(_)
            ) && !lhs_low
            {
                // 上值和字面量没有独立的表达式来源；用原 use→Def 证明输入在
                // 输入槽准备。尤其 0 / 0 不可折叠，左侧仍须重发原 LOADI。
                let (producer, home) =
                    self.facts.binary_operand_preparation(binary, 0, prepared)?;
                if home != input {
                    return None;
                }
                // 准备写可能已提升成匿名 Local；消费同一个原输入 Def 的声明，
                // 不能让通用寄存器操作数入口把这份已证明的读取重新拒绝。
                let previous = std::mem::replace(&mut self.register_operand, false);
                let rebuilt =
                    self.expr(&binary.lhs, before, slot, None, false, true, Some(producer));
                self.register_operand = previous;
                rebuilt?
            } else if !lhs_low && self.facts.binary_phi_operand(binary, 0).is_some() {
                // 只把需重建的 phi 准备交给该证书；既有低槽读取与普通 Def
                // 继续由 register_operand 消费其已有布局，不重新套用 phi 的 epoch 约束。
                self.binary_register_operand(binary, 0, before, layout.lhs?)?
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
            let cdata = self.dialect == DecompileDialect::Luajit
                && matches!(prepared, HirExpr::Int64(_) | HirExpr::UInt64(_));
            let upvalue = matches!(prepared, HirExpr::UpvalueRef(_));
            if !rhs_low
                && (upvalue
                    || cdata
                    || (constant(prepared)
                        && matches!(
                            self.dialect,
                            DecompileDialect::Lua51
                                | DecompileDialect::Lua52
                                | DecompileDialect::Lua53
                        )))
            {
                if !upvalue
                    && !cdata
                    && self.literal_uses_rk(prepared, Some((&sources, true))) != Some(false)
                {
                    return None;
                }
                let (producer, home) =
                    self.facts.binary_operand_preparation(binary, 1, prepared)?;
                if Some(home) != layout.rhs {
                    return None;
                }
                let previous = std::mem::replace(&mut self.register_operand, false);
                // RHS 上值也由原 use→Def 授权；保持左侧 CALL/运算完成后的读取时点。
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
            } else if !rhs_low && self.facts.binary_phi_operand(binary, 1).is_some() {
                self.binary_register_operand(binary, 1, before, layout.rhs?)?
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
