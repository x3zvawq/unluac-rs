//! 完整调用帧内的原构造步骤与暂存槽。
//!
//! 字段/SETLIST 角色由构造器 owner 提供，原操作槽由 Promotion 提供。本模块只在
//! PUC 的同一构造/调用事务中重放分配、字段求值、批次和 dispatch，不能用字段持有关系
//! 替代原根。例如 `callee; t={}; v=f(); SETLIST t(v,g()...); callee(t)` 保持 table 后
//! 的固定缓冲槽与开放返回槽；字段写完不清空 scratch，也不意味着旧根已经退休。
//! LuaJIT 的纯静态 TDUP 前缀不分配字段暂存槽，尾 CALL 单独核对原相邻 home/gap；
//! 开放数组覆盖和初始化约束复用构造器 builder，不复制零返回后缀的字段重排逻辑。

use super::*;
use crate::hir::common::{HirBinding, HirRecordField};
use crate::hir::simplify::table_constructors::{ConstructorWrite, TableBinding, constructor_write};
use crate::hir::visit::{HirVisitor, visit_stmts};

/// 只界定嵌套 initializer 的候选边界，不签发删除许可。定义边均指向较早语句，
/// 反向一次传播所属 seed 下界，避免对每个父构造器重扫整个 producer 链。
pub(super) fn nested_producers<'a>(
    stmts: impl Iterator<Item = Option<&'a HirStmt>>,
) -> BTreeSet<usize> {
    use crate::hir::simplify::mention::BindingReadCollector;
    let mut definitions = BTreeMap::<LocalId, usize>::new();
    let mut constructor_seeds = BTreeSet::new();
    let mut dependencies = Vec::<BTreeSet<usize>>::new();
    let mut owners = Vec::<Option<usize>>::new();
    for stmt in stmts {
        let index = dependencies.len();
        let mut reads = BTreeSet::new();
        let mut owner = None;
        if let Some(stmt) = stmt {
            crate::hir::visit::visit_stmt_header(
                stmt,
                &mut BindingReadCollector(|binding| {
                    if let HirBinding::Local(local) = binding
                        && let Some(&definition) = definitions.get(&local)
                    {
                        reads.insert(definition);
                    }
                }),
            );
            if let Some(write) = constructor_write(stmt)
                && let TableBinding::Local(local) = write.binding()
            {
                // 普通 table 写（如 weak[key]=result）不是构造器字段，不能把此前
                // 返回 weak 的 CALL 当成 seed，反向吞掉不相关的调用初始化边界。
                owner = definitions
                    .get(&local)
                    .copied()
                    .filter(|seed| constructor_seeds.contains(seed));
            }
            if let Some((local, value)) = scalar_local(stmt) {
                definitions.insert(local, index);
                if matches!(value, HirExpr::TableConstructor(_)) {
                    constructor_seeds.insert(index);
                }
            }
        } else {
            definitions.clear();
        }
        dependencies.push(reads);
        owners.push(owner);
    }
    let mut nested = BTreeSet::new();
    for index in (0..owners.len()).rev() {
        let Some(seed) = owners[index] else { continue };
        for &dependency in &dependencies[index] {
            if dependency >= seed {
                nested.insert(dependency);
                owners[dependency] = Some(owners[dependency].map_or(seed, |old| old.min(seed)));
            }
        }
    }
    nested
}

/// 当前 proto 字面量出现数给出生成常量池的保守上界；不以原常量池编号猜重编译 RK。
/// nil/两个 Boolean 可由后续语法化引入，预留这三个值；不进入子 proto 的常量域。
pub(in crate::hir::simplify) fn constants_fit_rk(proto: &HirProto) -> bool {
    struct Count(usize);
    impl HirVisitor<'_> for Count {
        fn is_complete(&self) -> bool {
            self.0 > 255
        }
        fn visit_expr(&mut self, expr: &HirExpr) {
            self.0 += usize::from(matches!(
                expr,
                HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::String(_)
                    | HirExpr::GlobalRef(_)
            ));
        }
        fn visit_lvalue(&mut self, value: &HirLValue) {
            self.0 += usize::from(matches!(value, HirLValue::Global(_)));
        }
    }
    let mut count = Count(3);
    visit_stmts(&proto.body.stmts, &mut count);
    count.0 <= 255
}

/// 只索引真实构造 seed 的字段；run 前缀可含普通表写。若它处于待吸收区间内部，
/// builder 的逐事件游标仍会拒绝跨越，不能让候选索引代替删除证明。
pub(super) fn index<'a>(
    run: &[&'a HirStmt],
    definitions: &BTreeMap<LocalId, Vec<usize>>,
) -> BTreeMap<usize, Vec<(usize, ConstructorWrite<'a>)>> {
    let mut frames = BTreeMap::<usize, Vec<_>>::new();
    for (index, stmt) in run.iter().enumerate() {
        let Some(write) = constructor_write(stmt) else {
            continue;
        };
        let TableBinding::Local(local) = write.binding() else {
            continue;
        };
        let Some(versions) = definitions.get(&local) else {
            continue;
        };
        let Some(seed_index) = versions
            .partition_point(|version| *version < index)
            .checked_sub(1)
        else {
            continue;
        };
        let seed = versions[seed_index];
        if !matches!(
            scalar_local(run[seed]),
            Some((_, HirExpr::TableConstructor(_)))
        ) {
            continue;
        }
        frames.entry(seed).or_default().push((index, write));
    }
    frames
}

fn literal_rk(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

/// 已完成的一元素原数组接低槽读取：复现保留目标后分配 table/buffer 的 Luau 槽序。
/// allocation、唯一批次和 GETTABLE 分别供证；当前字段是字面量不代表原批次可省略。
pub(super) fn scalar_array_lookup(
    facts: &ProtoPromotionFacts,
    table: &crate::hir::common::HirTableConstructor,
    access: &crate::hir::common::HirTableAccess,
    target: HomeSlotKey,
) -> Option<HirExpr> {
    let [crate::hir::common::HirTableField::Array(value)] = table.fields.as_slice() else {
        return None;
    };
    let allocation = facts.allocation_result_home(table)?;
    let batch = facts.native_allocation_batch_layout(table)?;
    let read = facts.native_table_read_layout(access)?;
    if !matches!(table.allocation, HirTableAllocation::Luau(_))
        || !table.matches_allocation_capacity(1)
        || table.trailing_multivalue.is_some()
        || !literal_rk(value)
        || allocation != HomeSlotKey::new(target.slot() + 1, 0)
        || batch.base != allocation
        || batch.buffer != HomeSlotKey::new(allocation.slot() + 1, 0)
        || batch.fixed_width != Some(1)
        || batch.start_index != 1
        || read.base != allocation
        || read.key.is_some()
        || !matches!(access.key, HirExpr::Integer(1))
        || facts.table_read_result_home(access) != Some(target)
    {
        return None;
    }
    let mut rebuilt = access.clone();
    rebuilt.base = HirExpr::TableConstructor(Box::new(table.clone()));
    Some(HirExpr::TableAccess(Box::new(rebuilt)))
}

impl FrameBuilder<'_> {
    /// 内层数组已由 constructor owner 合并，但其分配/Batch 来源仍在。
    /// 外层数组值语境必须重发同一 allocation 与连续缓冲；低槽值只在原位读取。
    /// 数字 Neg 的输入仍写到整批缓冲末端，不能只按结果为常量省掉原 scratch。
    pub(super) fn completed_luau_array(
        &self,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        let batch = self.facts.native_allocation_batch_layout(table)?;
        if !matches!(table.allocation, HirTableAllocation::Luau(_))
            || table.trailing_multivalue.is_some()
            || !table.matches_allocation_capacity(table.fields.len())
            || self.facts.allocation_result_home(table) != Some(HomeSlotKey::new(slot, 0))
            || batch.base != HomeSlotKey::new(slot, 0)
            || batch.buffer != HomeSlotKey::new(slot + 1, 0)
            || batch.start_index != 1
            || batch.fixed_width != Some(table.fields.len())
            || !table.fields.iter().enumerate().all(|(offset, field)| {
                let HirTableField::Array(value) = field else {
                    return false;
                };
                literal_rk(value)
                    || self
                        .direct_home(value)
                        .is_some_and(|home| home.slot() < self.base)
                    || matches!(value, HirExpr::Unary(unary)
                        if offset + 1 == table.fields.len()
                            && unary.op == crate::hir::common::HirUnaryOpKind::Neg
                            && match unary.expr {
                                HirExpr::Integer(value) => value >= 0,
                                HirExpr::Number(value) => value.is_finite() && !value.is_sign_negative(),
                                _ => false,
                            }
                            && self.facts.unary_result_home(unary)
                                == Some(HomeSlotKey::new(slot + 1 + offset, 0))
                            && self.facts.unary_operand_home(unary)
                                == Some(HomeSlotKey::new(slot + 1 + table.fields.len(), 0)))
            })
        {
            return None;
        }
        Some(HirExpr::TableConstructor(Box::new(table.clone())))
    }

    /// 构造器 owner 已合并的完整值仍携带各内部操作的 source site；调用帧只核对
    /// 这些表达式在原数组缓冲中的结果槽，不重新拆解字段或推测隐藏 SETTABLE 操作。
    pub(super) fn complete_constructor(
        &mut self,
        table: &crate::hir::common::HirTableConstructor,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        if !self.native?.constants_fit_rk {
            return None;
        }
        let mut rebuilt = table.clone();
        let mut arrays = 0;
        self.constructor_depth += 1;
        for field in &mut rebuilt.fields {
            match field {
                HirTableField::Array(value) => {
                    *value =
                        self.expr(value, before, slot + arrays + 1, None, false, false, None)?;
                    arrays += 1;
                }
                HirTableField::Record(record)
                    if literal_rk(&record.key) && literal_rk(&record.value) => {}
                _ => return None,
            }
        }
        if let Some(tail) = &table.trailing_multivalue {
            if tail.exact_width().is_some() {
                return None;
            }
            let HirExpr::Call(call) = tail.as_expr() else {
                return None;
            };
            rebuilt.trailing_multivalue = Some(HirPackTail::open(HirExpr::Call(Box::new(
                self.call(call, before, slot + arrays + 1, false, CallWidth::Open)?,
            ))));
        }
        self.constructor_depth -= 1;
        (rebuilt
            .allocation
            .batched_capacity_matches(arrays, rebuilt.fields.len() - arrays)
            == Some(true))
        .then(|| HirExpr::TableConstructor(Box::new(rebuilt)))
    }

    pub(super) fn constructor(
        &mut self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        if self.dialect == DecompileDialect::Luajit {
            return self.template_constructor(seed, table, slot);
        }
        if self.dialect == DecompileDialect::Luau {
            if matches!(table.allocation, HirTableAllocation::LuauTemplate { .. }) {
                return self.luau_record_constructor(seed, table, slot);
            }
            return self.luau_constructor(seed, table, slot);
        }
        if matches!(
            self.dialect,
            DecompileDialect::Luajit | DecompileDialect::Luau
        ) || !context.constants_fit_rk
            || table.trailing_multivalue.is_some()
            || table.fields.iter().any(|field| {
                !matches!(field, HirTableField::Record(record)
                if literal_rk(&record.key) && literal_rk(&record.value))
            })
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        let mut rebuilt = table.clone();
        let mut arrays = 0;
        let mut records = table.fields.len();
        self.finish_event(seed)?;
        self.constructor_depth += 1;
        for (position, (index, write)) in writes.iter().enumerate() {
            match write {
                ConstructorWrite::Record { access, value, .. } => {
                    let layout = self.facts.native_table_write_layout(access)?;
                    if layout.base != HomeSlotKey::new(slot, 0) {
                        return None;
                    }
                    let (key, key_scratch) =
                        self.record_operand(&access.key, layout.key, *index, slot + 1)?;
                    let (value, _) = self.record_operand(
                        value,
                        layout.value,
                        *index,
                        slot + 1 + usize::from(key_scratch),
                    )?;
                    rebuilt
                        .fields
                        .push(HirTableField::Record(HirRecordField { key, value }));
                    records += 1;
                }
                ConstructorWrite::Batch { batch, .. } => {
                    if position + 1 != writes.len()
                        || batch.start_index != 1
                        || batch.initializer_debug_scope.is_some()
                    {
                        return None;
                    }
                    for (offset, value) in batch.values.fixed.iter().enumerate() {
                        rebuilt.fields.push(HirTableField::Array(self.expr(
                            value,
                            *index,
                            slot + offset + 1,
                            None,
                            false,
                            false,
                            None,
                        )?));
                    }
                    arrays = batch.values.fixed.len();
                    if let Some(tail) = &batch.values.tail {
                        if tail.exact_width().is_some() {
                            return None;
                        }
                        let HirExpr::Call(call) = tail.as_expr() else {
                            return None;
                        };
                        rebuilt.trailing_multivalue =
                            Some(HirPackTail::open(HirExpr::Call(Box::new(self.call(
                                call,
                                *index,
                                slot + arrays + 1,
                                false,
                                CallWidth::Open,
                            )?))));
                    }
                }
            }
            self.finish_event(*index)?;
        }
        self.constructor_depth -= 1;
        if rebuilt.allocation.batched_capacity_matches(arrays, records) != Some(true) {
            return None;
        }
        Some(HirExpr::TableConstructor(Box::new(rebuilt)))
    }

    fn template_constructor(
        &mut self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        if !matches!(table.allocation, HirTableAllocation::Template { .. })
            || table.trailing_multivalue.is_some()
            || !table.fields.iter().all(|field| match field {
                HirTableField::Array(value) => literal_rk(value),
                HirTableField::Record(record) => {
                    literal_rk(&record.key) && literal_rk(&record.value)
                }
            })
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        let [(index, ConstructorWrite::Batch { batch, .. })] = writes.as_slice() else {
            return None;
        };
        if !batch.values.fixed.is_empty() || batch.initializer_debug_scope.is_some() {
            return None;
        }
        let tail = batch.values.tail.as_ref()?;
        if tail.exact_width().is_some() {
            return None;
        }
        let HirExpr::Call(call) = tail.as_expr() else {
            return None;
        };
        self.finish_event(seed)?;
        // TDUP 的静态字段不占运行时数组缓冲槽；原 TSETM 的开放 CALL 紧邻 table。
        // CALL owner 核对原 home 与 frame gap，字段覆盖语义仍交还构造器 owner。
        let call = self.call(call, *index, slot + 1, false, CallWidth::Open)?;
        let mut batch = (*batch).clone();
        batch.values.tail = Some(HirPackTail::open(HirExpr::Call(Box::new(call))));
        self.finish_event(*index)?;
        super::super::table_constructors::constructor_with_native_batch(table, &batch)
            .map(|table| HirExpr::TableConstructor(Box::new(table)))
    }

    /// DUPTABLE 的未显式初始化 record 仍在原 table 上按序写入。键/value 的原
    /// scratch 逐项核对；如 `{a=f(), b=g(), a=h()}` 保留三个调用和重复字段覆盖。
    fn luau_record_constructor(
        &mut self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let home = HomeSlotKey::new(slot, 0);
        let (owner, _) = scalar_local(self.run[seed])?;
        if table.trailing_multivalue.is_some()
            || table.fields.len() != table.implicit_template_fields.len()
            || table.fields.is_empty()
            || self.facts.allocation_result_home(table) != Some(home)
            || context.barred.contains(&home)
            || context.closed.contains(&home)
            || context
                .proto
                .local_debug_scopes
                .get(owner.index())
                .is_some_and(Option::is_some)
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        // 超过源码 DUPTABLE 的 32 字段上界时，必然改变分配协议，无需重建各个 RHS。
        if writes.len() > 32 {
            return None;
        }
        self.finish_event(seed)?;
        let mut records = Vec::with_capacity(writes.len());
        for (index, write) in writes {
            let ConstructorWrite::Record { access, value, .. } = write else {
                return None;
            };
            let layout = self.facts.native_table_write_layout(access)?;
            if layout.base != home
                || layout
                    .key
                    .is_some_and(|key| key != HomeSlotKey::new(slot + 1, 0))
                || layout.value
                    != Some(HomeSlotKey::new(
                        slot + 1 + usize::from(layout.key.is_some()),
                        0,
                    ))
            {
                return None;
            }
            let key = match layout.key {
                Some(key) => self.expr(&access.key, index, key.slot(), None, false, true, None)?,
                None => access.key.clone(),
            };
            if !matches!(&key, HirExpr::String(key)
                if key.as_utf8().is_some_and(|key| self.dialect.is_identifier_name(key)))
            {
                return None;
            }
            let value = self.expr(value, index, layout.value?.slot(), None, false, true, None)?;
            // compileExprAuto 对 CALL 分配独立结果槽；字面量/低槽 local 可能被模板
            // 常量化或直接读取，不能按当前结果值纯度省掉原字段 scratch 的写入。
            if !matches!(value, HirExpr::Call(_)) {
                return None;
            }
            records.push(HirRecordField { key, value });
            self.finish_event(index)?;
        }
        super::super::table_constructors::constructor_with_native_records(table, records)
            .map(|table| HirExpr::TableConstructor(Box::new(table)))
    }

    fn luau_constructor(
        &mut self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        if !matches!(table.allocation, HirTableAllocation::Luau(_))
            || !table.fields.is_empty()
            || table.trailing_multivalue.is_some()
            || self.facts.allocation_result_home(table) != Some(HomeSlotKey::new(slot, 0))
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        let (last, records) = writes.split_last()?;
        let (batch_index, ConstructorWrite::Batch { batch, .. }) = last else {
            return None;
        };
        let layout = self.facts.native_table_batch_layout(batch)?;
        let arrays = batch.values.fixed.len() + usize::from(batch.values.tail.is_some());
        if batch.initializer_debug_scope.is_some() {
            let context = self.native?;
            let scope = match batch.base {
                HirExpr::LocalRef(local) => context.proto.local_debug_scopes.get(local.index()),
                HirExpr::TempRef(temp) => context.proto.temp_debug_scopes.get(temp.index()),
                _ => None,
            }
            .copied()
            .flatten();
            let home = crate::hir::simplify::table_constructors::debug_initializer_home(
                self.run[seed],
                batch,
                scope,
                self.facts,
            )?;
            if home != HomeSlotKey::new(slot, 0)
                || context.barred.contains(&home)
                || context.closed.contains(&home)
            {
                return None;
            }
        }
        if !(1..=16).contains(&arrays)
            || batch.start_index != 1
            || layout.base != HomeSlotKey::new(slot, 0)
            || layout.buffer != HomeSlotKey::new(slot + 1, 0)
            || match layout.fixed_width {
                Some(width) => batch.values.tail.is_some() || width != batch.values.fixed.len(),
                None => batch
                    .values
                    .tail
                    .as_ref()
                    .is_none_or(|tail| tail.exact_width().is_some()),
            }
        {
            return None;
        }
        self.finish_event(seed)?;
        let mut rebuilt = table.clone();
        // Luau 先预留整批数组缓冲，再在它上方计算 record 的值；record 不采用 RK value。
        let record_home = HomeSlotKey::new(slot + 1 + arrays, 0);
        for (index, write) in records {
            let ConstructorWrite::Record { access, value, .. } = write else {
                return None;
            };
            let layout = self.facts.native_table_write_layout(access)?;
            if layout.base != HomeSlotKey::new(slot, 0)
                || layout.key.is_some()
                || layout.value != Some(record_home)
                || !literal_rk(value)
                || !matches!(access.key, HirExpr::String(_) | HirExpr::Integer(1..=256))
            {
                return None;
            }
            rebuilt.fields.push(HirTableField::Record(HirRecordField {
                key: access.key.clone(),
                value: (*value).clone(),
            }));
            self.finish_event(*index)?;
        }
        self.constructor_depth += 1;
        let fixed = batch
            .values
            .fixed
            .iter()
            .enumerate()
            .map(|(offset, value)| {
                self.expr(
                    value,
                    *batch_index,
                    slot + 1 + offset,
                    None,
                    false,
                    false,
                    None,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        let tail = match &batch.values.tail {
            Some(tail) => {
                let HirExpr::Call(call) = tail.as_expr() else {
                    return None;
                };
                Some(HirPackTail::open(HirExpr::Call(Box::new(self.call(
                    call,
                    *batch_index,
                    slot + 1 + fixed.len(),
                    false,
                    CallWidth::Open,
                )?))))
            }
            None => None,
        };
        self.constructor_depth -= 1;
        self.finish_event(*batch_index)?;
        let mut batch = (*batch).clone();
        batch.values = HirValuePack { fixed, tail };
        super::super::table_constructors::constructor_with_native_batch(&rebuilt, &batch)
            .map(|table| HirExpr::TableConstructor(Box::new(table)))
    }

    pub(super) fn direct_home(&self, expr: &HirExpr) -> Option<HomeSlotKey> {
        match HirBinding::from_expr(expr)? {
            HirBinding::Local(local) => self.facts.trusted_local_home_slot(local),
            HirBinding::Param(param) => self.facts.trusted_param_home_slot(param),
            _ => None,
        }
    }

    fn record_operand(
        &mut self,
        expr: &HirExpr,
        original: Option<HomeSlotKey>,
        before: usize,
        scratch: usize,
    ) -> Option<(HirExpr, bool)> {
        let Some(home) = original else {
            return literal_rk(expr).then(|| (expr.clone(), false));
        };
        if home.slot() < self.base && self.direct_home(expr) == Some(home) {
            return Some((expr.clone(), false));
        }
        if home != HomeSlotKey::new(scratch, 0) {
            return None;
        }
        let value = self.expr(expr, before, scratch, None, false, false, None)?;
        // RK 常量及现成 local/param 都不写 scratch；不能用它们替代原 LOADK/COPY，
        // 否则后续 lookup 的 GC 可能看到原本已覆盖的 activation 残值（regress_579）。
        if matches!(value, HirExpr::LocalRef(_) | HirExpr::ParamRef(_))
            || crate::value_semantics::table::table_constant_kind(&value).is_some()
        {
            return None;
        }
        Some((value, true))
    }

    pub(super) fn finish_dispatch(&mut self, call: &HirCallExpr, before: usize) -> Option<()> {
        if self.native.is_none() {
            return Some(());
        }
        let source = call.source_site?;
        let endings = self.facts.call_frame_root_ends(source.instr);
        let locals = endings
            .into_iter()
            .filter_map(|temp| self.facts.promoted_local_for_temp(temp))
            .collect::<BTreeSet<_>>();
        while self.next_event < before {
            let HirStmt::LocalRootRelease(local) = self.run[self.next_event] else {
                break;
            };
            if !locals.contains(local)
                || self
                    .definition(*local, self.next_event)
                    .is_none_or(|index| Some(index) < self.first_event)
            {
                return None;
            }
            self.next_event += 1;
        }
        Some(())
    }
}
