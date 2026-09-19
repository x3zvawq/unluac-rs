//! 在完整源码帧中重放表分配、字段求值及 SETLIST 暂存区。
//!
//! 构造器 owner 提供字段/批次角色，Promotion 提供原操作槽，FrameBuilder 统一
//! 核对 Def 版本与事件顺序；字段持有值不代表原 scratch 根可以提前退休。
//! 例如 t={}; v=f(); SETLIST t(v,g()...) 必须保留原固定缓冲与开放尾，
//! 各 VM 的分配方式和槽布局在对应构造路径中验证。

use super::*;
use crate::hir::common::{HirBinding, HirRecordField};
use crate::hir::simplify::table_constructors::{ConstructorWrite, TableBinding, constructor_write};
use crate::hir::visit::{HirVisitor, visit_stmts};

/// 嵌套初始化的准备语句与字段写边界；二者都应留给完整构造事务。
pub(super) struct NestedInitializers {
    pub producers: BTreeSet<usize>,
    pub writes: BTreeSet<usize>,
}

/// 只界定嵌套 initializer 的候选边界，不签发删除许可。定义边均指向较早语句，
/// 反向一次传播所属 seed 下界，避免对每个父构造器重扫整个 producer 链。
pub(super) fn nested_initializers<'a>(
    stmts: impl Iterator<Item = Option<&'a HirStmt>>,
) -> NestedInitializers {
    use crate::hir::simplify::mention::BindingReadCollector;
    let mut definitions = BTreeMap::<LocalId, usize>::new();
    let mut constructor_seeds = BTreeSet::new();
    let mut dependencies = Vec::<BTreeSet<usize>>::new();
    let mut owners = Vec::<Option<usize>>::new();
    let mut writes = BTreeSet::new();
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
        if owner.is_some() {
            // RK 常量字段没有单独 producer；仅查看前一条语句会把该写误当成
            // 独立赋值终点，在候选拒绝时截断仍未完成的构造器准备区。
            writes.insert(index);
        }
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
    NestedInitializers {
        producers: nested,
        writes,
    }
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

pub(super) fn literal_rk(expr: &HirExpr) -> bool {
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
        self.luau_array_frame_matches(table, slot)
            .then(|| HirExpr::TableConstructor(Box::new(table.clone())))
    }

    /// 数组元素与模板字段共享已完成数组的布局证明；查询不复制待保留的表达式树。
    fn luau_array_frame_matches(
        &self,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> bool {
        let Some(batch) = self.facts.native_allocation_batch_layout(table) else {
            return false;
        };
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
            return false;
        }
        true
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
        // 逐层重建字段，不能先 clone 整棵表树再递归替换子树，避免深嵌套重复复制。
        let mut rebuilt = crate::hir::common::HirTableConstructor {
            sources: table.sources.clone(),
            allocation: table.allocation.clone(),
            implicit_template_fields: table.implicit_template_fields.clone(),
            fields: Vec::with_capacity(table.fields.len()),
            trailing_multivalue: None,
        };
        let mut arrays = 0;
        self.constructor_depth += 1;
        for field in &table.fields {
            match field {
                HirTableField::Array(value) => {
                    let scratch = slot + arrays + 1;
                    let value = if matches!(value, HirExpr::TableConstructor(_)) {
                        // 已完成内层表仍在这个原 Batch 元素槽分配；递归使用同一字段帧，
                        // 不把嵌套 constructor 当作无暂存区的常量。
                        self.record_operand(
                            value,
                            Some(HomeSlotKey::new(scratch, 0)),
                            before,
                            scratch,
                        )?
                        .0
                    } else {
                        self.expr(value, before, scratch, None, false, false, None)?
                    };
                    rebuilt.fields.push(HirTableField::Array(value));
                    arrays += 1;
                }
                HirTableField::Record(record)
                    if literal_rk(&record.key) && literal_rk(&record.value) =>
                {
                    rebuilt.fields.push(field.clone());
                }
                HirTableField::Record(record)
                    if self.completed_puc_record_field(record, HomeSlotKey::new(slot, 0)) =>
                {
                    let layout = self
                        .facts
                        .native_record_write_layout(&record.write_sources)?;
                    let (key, key_scratch) =
                        self.record_operand(&record.key, layout.key, before, slot + arrays + 1)?;
                    let (value, _) = self.record_operand(
                        &record.value,
                        layout.value,
                        before,
                        slot + arrays + 1 + usize::from(key_scratch),
                    )?;
                    rebuilt.fields.push(HirTableField::Record(HirRecordField {
                        write_sources: record.write_sources.clone(),
                        key,
                        value,
                    }));
                }
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
            if matches!(table.allocation, HirTableAllocation::Indexed { .. }) {
                return self.indexed_constructor(seed, table, slot);
            }
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
        let pending_batch = writes.last().and_then(|(index, write)| match write {
            ConstructorWrite::Batch { batch, .. } => Some((*index, *batch)),
            ConstructorWrite::Record { .. } => None,
        });
        let mut rebuilt = table.clone();
        let mut arrays = 0;
        let mut records = table.fields.len();
        self.finish_event(seed)?;
        self.constructor_depth += 1;
        for (position, (index, write)) in writes.iter().enumerate() {
            match write {
                ConstructorWrite::Record { access, value, .. } => {
                    // SETLIST 延后提交数组，但数组 producer 可以先于 record 求值。
                    // 按最终 batch 读取的值版本推进一次游标；不从复用后的 local 名字猜顺序。
                    // 每个值仍由 expr 核对原缓冲槽，finish_event 核对期间没有遗漏事件。
                    if let Some((batch_index, batch)) = pending_batch {
                        while let Some(HirExpr::LocalRef(local)) = batch.values.fixed.get(arrays) {
                            // 低槽现成 binding 的定义不是本次数组 MOVE 的读取时点。
                            if self
                                .direct_home(&HirExpr::LocalRef(*local))
                                .is_none_or(|home| home.slot() < self.base)
                                || self
                                    .definition(*local, batch_index)
                                    .is_none_or(|def| def <= seed || def >= *index)
                            {
                                break;
                            }
                            rebuilt
                                .fields
                                .push(HirTableField::Array(self.puc_array_element(
                                    &batch.values.fixed[arrays],
                                    *index,
                                    slot + arrays + 1,
                                )?));
                            arrays += 1;
                        }
                    }
                    let layout = self.facts.native_table_write_layout(access)?;
                    if layout.base != HomeSlotKey::new(slot, 0) {
                        return None;
                    }
                    let (key, key_scratch) =
                        self.record_operand(&access.key, layout.key, *index, slot + arrays + 1)?;
                    let (value, _) = self.record_operand(
                        value,
                        layout.value,
                        *index,
                        slot + arrays + 1 + usize::from(key_scratch),
                    )?;
                    rebuilt.fields.push(HirTableField::Record(HirRecordField {
                        write_sources: access.sources.clone(),
                        key,
                        value,
                    }));
                    records += 1;
                }
                ConstructorWrite::Batch { batch, .. } => {
                    if position + 1 != writes.len() || batch.start_index != 1 {
                        return None;
                    }
                    self.batch_initializer_matches(seed, table, batch, slot)?;
                    for (offset, value) in batch.values.fixed.iter().enumerate().skip(arrays) {
                        rebuilt
                            .fields
                            .push(HirTableField::Array(self.puc_array_element(
                                value,
                                *index,
                                slot + offset + 1,
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

    /// 数组元素也会在原缓冲槽重新分配已合并的嵌套表；复用 record operand 的
    /// allocation/SETLIST 证明，普通标量仍使用数组值语境，不套用 RK 的省槽规则。
    fn puc_array_element(
        &mut self,
        value: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let prepared = match value {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value))
                .unwrap_or(value),
            _ => value,
        };
        if matches!(prepared, HirExpr::TableConstructor(_)) {
            self.record_operand(value, Some(HomeSlotKey::new(slot, 0)), before, slot)
                .map(|(value, _)| value)
        } else {
            self.expr(value, before, slot, None, false, false, None)
        }
    }

    /// debug binding 在末批次之后才激活；未来 capture 不妨碍重放其原始初始化。
    /// 已经打开的引用及资源边界仍需拒绝，后续 binding 身份由整帧 preview 验证。
    fn batch_initializer_matches(
        &self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        batch: &crate::hir::common::HirTableSetList,
        slot: usize,
    ) -> Option<()> {
        if batch.initializer_debug_scope.is_none() {
            return Some(());
        }
        let context = self.native?;
        let (owner, _) = scalar_local(self.run[seed])?;
        let scope = context
            .proto
            .local_debug_scopes
            .get(owner.index())
            .copied()
            .flatten();
        let home = super::super::table_constructors::debug_initializer_home(
            self.run[seed],
            batch,
            scope,
            self.facts,
        )?;
        (home == HomeSlotKey::new(slot, 0)
            && (!context.barred.contains(&home)
                || self.facts.allocation_result_reference_unaliased(table))
            && !context.closed.contains(&home))
        .then_some(())
    }

    fn indexed_constructor(
        &mut self,
        seed: usize,
        table: &crate::hir::common::HirTableConstructor,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let home = HomeSlotKey::new(slot, 0);
        let HirTableAllocation::Indexed { array_capacity, .. } = table.allocation else {
            return None;
        };
        let array_fields = array_capacity != 0;
        if !table.fields.is_empty()
            || table.trailing_multivalue.is_some()
            || self.facts.allocation_result_home(table) != Some(home)
            || (context.barred.contains(&home)
                && !self.facts.allocation_result_reference_unaliased(table))
            || context.closed.contains(&home)
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        if array_fields && !table.matches_indexed_array_capacity(writes.len()) {
            return None;
        }
        self.finish_event(seed)?;
        self.constructor_depth += 1;
        let mut rebuilt = table.clone();
        let write_count = writes.len();
        for (offset, (index, write)) in writes.into_iter().enumerate() {
            if let ConstructorWrite::Batch { batch, .. } = write {
                // TSETM 的尾 CALL 复用 table+1，而非 PUC 的固定数组缓冲末端。
                // 先前逐字段写已提交到表中；开放结果只能接在完整数组前缀之后。
                let layout = self.facts.native_table_batch_layout(batch)?;
                let tail = batch.values.tail.as_ref()?;
                if !array_fields
                    || offset + 1 != write_count
                    || !batch.values.fixed.is_empty()
                    || batch.start_index as usize != offset + 1
                    || layout.base != home
                    || layout.buffer != HomeSlotKey::new(slot + 1, 0)
                    || layout.fixed_width.is_some()
                    || tail.exact_width().is_some()
                {
                    return None;
                }
                self.batch_initializer_matches(seed, table, batch, slot)?;
                let HirExpr::Call(call) = tail.as_expr() else {
                    return None;
                };
                let call = self.call(call, index, slot + 1, false, CallWidth::Open)?;
                let mut batch = batch.clone();
                batch.values.tail = Some(HirPackTail::open(HirExpr::Call(Box::new(call))));
                self.finish_event(index)?;
                self.constructor_depth -= 1;
                return super::super::table_constructors::constructor_with_native_batch(
                    &rebuilt, &batch,
                )
                .map(|table| HirExpr::TableConstructor(Box::new(table)));
            }
            let ConstructorWrite::Record { access, value, .. } = write else {
                return None;
            };
            let layout = self.facts.native_table_write_layout(access)?;
            if layout.base != home
                || layout.key.is_some()
                || access.key != HirExpr::Integer(i64::try_from(offset + 1).ok()?)
            {
                return None;
            }
            let (value, _) = self.record_operand(value, layout.value, index, slot + 1)?;
            // 字面量数组会被 JIT 编译为模板；动态字段必须保留原 TNEW/TSETB 分配方式。
            if crate::value_semantics::table::table_constant_kind(&value).is_some() {
                return None;
            }
            if array_fields {
                rebuilt.fields.push(HirTableField::Array(value));
            } else {
                // 原数字 record 使用 hash 预分配，不能改成数组或从空表开始逐项扩容。
                rebuilt.fields.push(HirTableField::Record(HirRecordField {
                    write_sources: access.sources.clone(),
                    key: access.key.clone(),
                    value,
                }));
            }
            self.finish_event(index)?;
        }
        self.constructor_depth -= 1;
        rebuilt
            .matches_allocation_capacity(if array_fields { write_count } else { 0 })
            .then(|| HirExpr::TableConstructor(Box::new(rebuilt)))
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
        let (batch, records) = match writes.split_last()? {
            ((index, ConstructorWrite::Batch { batch, .. }), records) => {
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
                (Some((*index, *batch, call)), records)
            }
            _ => (None, writes.as_slice()),
        };
        let home = HomeSlotKey::new(slot, 0);
        if !records.is_empty() && self.facts.allocation_result_home(table) != Some(home) {
            return None;
        }
        self.finish_event(seed)?;
        let mut rebuilt = table.clone();
        let mut added = Vec::new();
        self.constructor_depth += 1;
        for (index, write) in records {
            let ConstructorWrite::Record { access, value, .. } = write else {
                return None;
            };
            let layout = self.facts.native_table_write_layout(access)?;
            if layout.base != home
                || layout.key.is_some()
                || layout.value != Some(HomeSlotKey::new(slot + 1, 0))
                || !literal_rk(&access.key)
            {
                return None;
            }
            let value = self.expr(value, *index, slot + 1, None, false, true, None)?;
            // 保持 TDUP 之后的动态写；常量不能借此提前移入模板初值。
            if crate::value_semantics::table::table_constant_kind(&value).is_some() {
                return None;
            }
            added.push(HirRecordField {
                write_sources: access.sources.clone(),
                key: access.key.clone(),
                value,
            });
            self.finish_event(*index)?;
        }
        let Some((index, batch, call)) = batch else {
            self.constructor_depth -= 1;
            return super::super::table_constructors::constructor_with_native_records(table, added)
                .map(|table| HirExpr::TableConstructor(Box::new(table)));
        };
        rebuilt
            .fields
            .extend(added.into_iter().map(HirTableField::Record));
        // TDUP 的静态字段不占运行时数组缓冲槽；原 TSETM 的开放 CALL 紧邻 table。
        // CALL owner 核对原 home 与 frame gap，字段覆盖语义仍交还构造器 owner。
        let call = self.call(call, index, slot + 1, false, CallWidth::Open)?;
        let mut batch = (*batch).clone();
        batch.values.tail = Some(HirPackTail::open(HirExpr::Call(Box::new(call))));
        self.finish_event(index)?;
        self.constructor_depth -= 1;
        super::super::table_constructors::constructor_with_native_batch(&rebuilt, &batch)
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
            // seed 已有的常量（包括混合模板的 Some 项）仍在分配时建立；这里只
            // 吸收后继动态写，不重放或删除构造器 owner 已完成的字段事务。
            || !table.fields.iter().all(|field| matches!(field,
                HirTableField::Record(record)
                    if literal_rk(&record.key) && literal_rk(&record.value)))
            || table.fields.is_empty()
            || self.facts.allocation_result_home(table) != Some(home)
            || context.barred.contains(&home)
            || context.closed.contains(&home)
        {
            return None;
        }
        let writes = self.constructors.remove(&seed)?;
        if let Some(scope) = context.proto.local_debug_scopes[owner.index()] {
            if !matches!(self.run[seed], HirStmt::LocalDecl(decl)
                if decl.bindings.as_slice() == [owner])
            {
                return None;
            }
            let (_, ConstructorWrite::Record { access, .. }) = writes.last()? else {
                return None;
            };
            let (producer, initializer_scope) =
                self.facts.native_table_write_layout(access)?.initializer?;
            let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
                return None;
            };
            // 名字在最后一次字段写之后才进入生命周期；原表 Def、当前声明及 scope
            // 必须仍是同一身份。coalesce 后失去 producer 映射时不能借同槽继续消费。
            if initializer_scope != scope
                || self.facts.operation_result_temp(source) != Some(producer)
                || self.facts.promoted_local_for_temp(producer) != Some(owner)
            {
                return None;
            }
        }
        // 超过源码 DUPTABLE 的 32 字段上界时，必然改变分配协议，无需重建各个 RHS。
        if writes.len() > 32 {
            return None;
        }
        self.finish_event(seed)?;
        let scratch = self.constructor_reserved_top.unwrap_or(0).max(slot + 1);
        let mut records = Vec::with_capacity(writes.len());
        for (index, write) in writes {
            let ConstructorWrite::Record { access, value, .. } = write else {
                return None;
            };
            let layout = self.facts.native_table_write_layout(access)?;
            if layout.base != home
                || layout
                    .key
                    .is_some_and(|key| key != HomeSlotKey::new(scratch, 0))
                || layout.value
                    != Some(HomeSlotKey::new(
                        scratch + usize::from(layout.key.is_some()),
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
            // compileExprAuto 对 CALL 和表分配独立结果槽；非空数组还须复用原 allocation/
            // Batch/连续缓冲证明。字面量和低槽 local 可能直接读取，不能省掉原 scratch 写。
            if !matches!(value, HirExpr::Call(_))
                && !matches!(&value, HirExpr::TableConstructor(table)
                    if (table.fields.is_empty() && table.trailing_multivalue.is_none()
                        && self.facts.allocation_result_home(table) == layout.value)
                        || self.luau_array_frame_matches(table, scratch))
            {
                return None;
            }
            records.push(HirRecordField {
                write_sources: access.sources.clone(),
                key,
                value,
            });
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
        self.batch_initializer_matches(seed, table, batch, slot)?;
        let buffer = self.constructor_reserved_top.unwrap_or(0).max(slot + 1);
        if !(1..=16).contains(&arrays)
            || batch.start_index != 1
            || layout.base != HomeSlotKey::new(slot, 0)
            || layout.buffer != HomeSlotKey::new(buffer, 0)
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
        let record_home = HomeSlotKey::new(buffer + arrays, 0);
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
                write_sources: access.sources.clone(),
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
                    buffer + offset,
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
                    buffer + fixed.len(),
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

    /// 完成字段不能再次吸收 producer：当前低槽引用须与原 SETTABLE 直接输入相同，
    /// 字面量须原本内嵌。嵌套表只获得递归入口，其 allocation/字段/Batch 的全部
    /// 证明随后仍由 record_operand 消费，不能把这里的当前层检查当作完整表证明。
    fn completed_puc_record_field(&self, record: &HirRecordField, home: HomeSlotKey) -> bool {
        let Some(layout) = self.facts.native_record_write_layout(&record.write_sources) else {
            return false;
        };
        let matches_operand = |expr: &HirExpr, original: Option<HomeSlotKey>| match original {
            Some(original) => {
                original.slot() < self.base && self.direct_home(expr) == Some(original)
            }
            None => literal_rk(expr),
        };
        layout.base == home
            && matches_operand(&record.key, layout.key)
            && (matches_operand(&record.value, layout.value)
                || (matches!(record.value, HirExpr::TableConstructor(_))
                    && layout.value == Some(HomeSlotKey::new(home.slot() + 1, 0))))
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
        let definition = if let HirExpr::LocalRef(local) = expr {
            self.definition(*local, before)
        } else {
            None
        };
        let prepared = definition
            .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value))
            .unwrap_or(expr);
        let producer = if let HirExpr::Closure(closure) = prepared {
            Some(self.constructor_closure_producer(closure, home)?)
        } else {
            None
        };
        let completed_table = if let HirExpr::TableConstructor(table) = prepared
            && !definition.is_some_and(|index| self.constructors.contains_key(&index))
        {
            if !matches!(table.allocation, HirTableAllocation::PucBatched(_))
                || self.facts.allocation_result_home(table) != Some(home)
            {
                return None;
            }
            if table.trailing_multivalue.is_none()
                && table
                    .fields
                    .iter()
                    .all(|field| matches!(field, HirTableField::Record(_)))
            {
                if table
                    .allocation
                    .batched_capacity_matches(0, table.fields.len())
                    != Some(true)
                    || !table.fields.iter().all(|field| {
                        matches!(field, HirTableField::Record(record)
                            if self.completed_puc_record_field(record, home))
                    })
                {
                    return None;
                }
            } else {
                // 原 SETLIST 已由字段 owner 合并；仍核对完整数组来源和连续缓冲。
                let batch = self.facts.native_allocation_batch_layout(table)?;
                if batch.base != home
                    || batch.buffer != HomeSlotKey::new(home.slot() + 1, 0)
                    || batch.start_index != 1
                    || batch.fixed_width
                        != table
                            .trailing_multivalue
                            .is_none()
                            .then_some(table.fields.len())
                    || !table
                        .fields
                        .iter()
                        .all(|field| matches!(field, HirTableField::Array(_)))
                {
                    return None;
                }
                for (offset, field) in table.fields.iter().enumerate() {
                    if let HirTableField::Array(HirExpr::Closure(closure)) = field {
                        self.constructor_closure_producer(
                            closure,
                            HomeSlotKey::new(home.slot() + offset + 1, 0),
                        )?;
                    }
                }
            }
            true
        } else {
            false
        };
        let value = self.expr(
            expr,
            before,
            scratch,
            None,
            false,
            completed_table,
            producer,
        )?;
        // RK 常量及现成 local/param 都不写 scratch；不能用它们替代原 LOADK/COPY，
        // 否则后续 lookup 的 GC 可能看到原本已覆盖的 activation 残值（regress_579）。
        if matches!(value, HirExpr::LocalRef(_) | HirExpr::ParamRef(_))
            || crate::value_semantics::table::table_constant_kind(&value).is_some()
        {
            return None;
        }
        Some((value, true))
    }

    /// 闭包字段仍在原 CLOSURE 的目标槽创建，捕获可见性再由共享 expr 分支核对。
    /// 不用合并 Local 的其它值版本代替这次分配，隐藏 MOVE 也不能被 record 消费。
    fn constructor_closure_producer(
        &self,
        closure: &crate::hir::common::HirClosureExpr,
        home: HomeSlotKey,
    ) -> Option<crate::hir::common::TempId> {
        closure.creation.as_ref()?;
        let producer = self.facts.operation_result_temp(closure.source_site?)?;
        (self.facts.trusted_temp_home_slot(producer) == Some(home)
            && self
                .facts
                .complete_temp_definition_write_homes(producer)
                .iter()
                .copied()
                .eq([home]))
        .then_some(producer)
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
