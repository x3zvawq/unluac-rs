//! 维护 HIR 表构造器重建时的字段布局状态。
//!
//! 消费已有字段及已获准的后续写入，输出保留写入语义和原初始化事实的构造器；
//! 区域选择与语句扫描由调用方负责。

use std::collections::BTreeMap;

use crate::hir::common::{
    HirExpr, HirPackTail, HirTableAllocation, HirTableConstructor, HirTableField,
};

use super::{RebuildScratch, RestoredArrayField, RestoredPendingIntegerField};
use crate::hir::value_facts::value_facts;
use crate::value_semantics::table::{TableExpression, initializes_template};

#[derive(Debug, Clone)]
enum BuilderField {
    Final(HirTableField),
    PendingInt {
        write_sources: crate::hir::common::HirOperationSources,
        key: i64,
        value: HirExpr,
    },
    MovedPendingInt,
}

#[derive(Debug, Clone, Copy)]
struct PendingIntegerField {
    field_index: usize,
    shadowed_at: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum RecordPromotionPolicy {
    Normal,
    PreserveSetListPrefix { start_index: u32 },
}

#[derive(Debug, Clone)]
pub(super) struct ConstructorBuilder {
    sources: crate::hir::common::HirOperationSources,
    allocation: HirTableAllocation,
    implicit_template_fields: std::collections::BTreeSet<usize>,
    fields: Vec<BuilderField>,
    pub(super) trailing_multivalue: Option<HirPackTail>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, PendingIntegerField>,
    // 未知键一次遮蔽所有更早的 pending；位置随事务回滚，避免逐键重复标记。
    last_unknown_key_field: Option<usize>,
    // 首次字段位置使搬移/降级不改变键身份，回滚只需移除检查点之后首次出现的键。
    numeric_key_first_fields: BTreeMap<i64, usize>,
    moved_fields: usize,
}

#[derive(Debug, Clone)]
pub(super) struct BuilderCheckpoint {
    fields_len: usize,
    last_unknown_key_field: Option<usize>,
    trailing_multivalue: Option<HirPackTail>,
    next_array_index: u32,
    restored_pending_integer_fields_len: usize,
    restored_array_fields_len: usize,
    moved_fields: usize,
}

impl ConstructorBuilder {
    /// 无 producer 的批次追加共用相同整数键/开放覆盖规则；时序与槽证明由调用方负责。
    pub(super) fn append_batch(
        &mut self,
        batch: &crate::hir::common::HirTableSetList,
        scratch: &mut RebuildScratch,
    ) -> Option<()> {
        if self.trailing_multivalue.is_some()
            || (batch.start_index < self.next_array_index()
                && !self.demote_array_suffix(batch.start_index, &mut scratch.restored_array_fields))
        {
            return None;
        }
        self.drain_pending_integer_fields(&mut scratch.restored_pending_integer_fields);
        if batch.start_index != self.next_array_index() {
            return None;
        }
        for value in &batch.values.fixed {
            self.push_array_value(value.clone());
        }
        self.trailing_multivalue = batch.values.tail.clone();
        Some(())
    }

    pub(super) fn from_constructor(constructor: HirTableConstructor) -> Self {
        let implicit_template_fields = constructor.implicit_template_fields;
        let mut builder = Self {
            sources: constructor.sources,
            allocation: constructor.allocation,
            implicit_template_fields: std::collections::BTreeSet::new(),
            fields: Vec::with_capacity(constructor.fields.len()),
            trailing_multivalue: constructor.trailing_multivalue,
            next_array_index: 1,
            pending_integer_fields: BTreeMap::new(),
            last_unknown_key_field: None,
            numeric_key_first_fields: BTreeMap::new(),
            moved_fields: 0,
        };
        for (index, field) in constructor.fields.into_iter().enumerate() {
            if implicit_template_fields.contains(&index) {
                builder.push_implicit_template_field(field);
                continue;
            }
            match field {
                HirTableField::Array(value) => {
                    builder.push_array_value(value);
                }
                HirTableField::Record(field) => {
                    if builder.trailing_multivalue.is_some() {
                        // 已完成构造器的 array 数量决定 open tail 起点，不能重新晋升 record。
                        if let Some(key) = field.key.table_integer_key() {
                            builder
                                .numeric_key_first_fields
                                .entry(key)
                                .or_insert(builder.fields.len());
                        }
                        builder
                            .fields
                            .push(BuilderField::Final(HirTableField::Record(field)));
                    } else {
                        builder.push_record_field(field);
                    }
                }
            }
        }
        builder
    }

    pub(super) fn into_constructor(self) -> HirTableConstructor {
        let mut fields = Vec::with_capacity(self.fields.len());
        let mut implicit_template_fields = std::collections::BTreeSet::new();
        for (index, field) in self.fields.into_iter().enumerate() {
            let output_index = fields.len();
            match field {
                BuilderField::Final(field) => fields.push(field),
                BuilderField::PendingInt {
                    write_sources,
                    key,
                    value,
                } => {
                    fields.push(HirTableField::Record(crate::hir::common::HirRecordField {
                        write_sources,
                        key: HirExpr::Integer(key),
                        value,
                    }));
                }
                BuilderField::MovedPendingInt => {
                    debug_assert!(!self.implicit_template_fields.contains(&index));
                }
            }
            if fields.len() != output_index && self.implicit_template_fields.contains(&index) {
                implicit_template_fields.insert(output_index);
            }
        }
        let mut constructor = HirTableConstructor {
            sources: self.sources,
            fields,
            trailing_multivalue: self.trailing_multivalue,
            allocation: self.allocation,
            implicit_template_fields,
        };
        restore_luau_template_initialization(&mut constructor);
        restore_template_nil_hash_fields(&mut constructor);
        restore_template_nil_slots(&mut constructor);
        restore_indexed_array_fields(&mut constructor);
        constructor
    }

    pub(super) fn checkpoint(&self, scratch: &RebuildScratch) -> BuilderCheckpoint {
        BuilderCheckpoint {
            fields_len: self.fields.len(),
            last_unknown_key_field: self.last_unknown_key_field,
            trailing_multivalue: self.trailing_multivalue.clone(),
            next_array_index: self.next_array_index,
            restored_pending_integer_fields_len: scratch.restored_pending_integer_fields.len(),
            restored_array_fields_len: scratch.restored_array_fields.len(),
            moved_fields: self.moved_fields,
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: BuilderCheckpoint, scratch: &mut RebuildScratch) {
        self.fields.truncate(checkpoint.fields_len);
        self.implicit_template_fields
            .retain(|index| *index < checkpoint.fields_len);
        self.last_unknown_key_field = checkpoint.last_unknown_key_field;
        self.numeric_key_first_fields
            .retain(|_, first_field| *first_field < checkpoint.fields_len);
        self.trailing_multivalue = checkpoint.trailing_multivalue;
        self.next_array_index = checkpoint.next_array_index;
        self.moved_fields = checkpoint.moved_fields;
        for restored in scratch.restored_array_fields[checkpoint.restored_array_fields_len..]
            .iter()
            .rev()
        {
            if restored.field_index < checkpoint.fields_len {
                self.fields[restored.field_index] =
                    BuilderField::Final(HirTableField::Array(restored.value.clone()));
            }
        }
        self.pending_integer_fields
            .retain(|_, pending| pending.field_index < checkpoint.fields_len);
        for pending in self.pending_integer_fields.values_mut() {
            if pending
                .shadowed_at
                .is_some_and(|field_index| field_index >= checkpoint.fields_len)
            {
                pending.shadowed_at = None;
            }
        }
        for restored in scratch.restored_pending_integer_fields
            [checkpoint.restored_pending_integer_fields_len..]
            .iter()
            .rev()
        {
            if restored.field_index < checkpoint.fields_len {
                self.fields[restored.field_index] = BuilderField::PendingInt {
                    write_sources: restored.write_sources.clone(),
                    key: restored.key,
                    value: restored.value.clone(),
                };
                self.pending_integer_fields.insert(
                    restored.key,
                    PendingIntegerField {
                        field_index: restored.field_index,
                        shadowed_at: None,
                    },
                );
            }
        }
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
        scratch
            .restored_array_fields
            .truncate(checkpoint.restored_array_fields_len);
    }

    pub(super) fn commit(&mut self, checkpoint: &BuilderCheckpoint, scratch: &mut RebuildScratch) {
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
        scratch
            .restored_array_fields
            .truncate(checkpoint.restored_array_fields_len);
    }

    pub(super) fn next_array_index(&self) -> u32 {
        self.next_array_index
    }

    /// 已完成的字段段超过原分配上界时，保留 scanner 的上一个完整事务。
    /// 重复字段也计入这个保守预算；精确语法布局仍在完整构造器提交处统一核对。
    pub(super) fn fits_preallocated_field_count(&self) -> bool {
        let HirTableAllocation::Luau(allocation) = self.allocation else {
            return true;
        };
        let fields = self.fields.len() - self.moved_fields;
        let tail_slot = self
            .trailing_multivalue
            .as_ref()
            .is_some_and(|tail| !matches!(tail.as_expr(), HirExpr::VarArg));
        fields as u64 + u64::from(tail_slot)
            <= u64::from(allocation.array_capacity) + u64::from(allocation.hash_capacity)
    }

    pub(super) fn has_indexed_array_layout(&self) -> bool {
        self.allocation.indexed_array_capacity().is_some()
    }

    pub(super) fn push_array_value(&mut self, value: HirExpr) {
        self.numeric_key_first_fields
            .entry(i64::from(self.next_array_index))
            .or_insert(self.fields.len());
        self.fields
            .push(BuilderField::Final(HirTableField::Array(value)));
        self.next_array_index += 1;
    }

    /// Lowering 发布的模板占位保持原字段角色；不能让通用整数 record 晋升或暂存后再从
    /// nil 外形反猜其来源。当前两个生产者都发布 record，数组分支只保持索引完备性。
    fn push_implicit_template_field(&mut self, field: HirTableField) {
        let field_index = self.fields.len();
        match field {
            HirTableField::Array(value) => self.push_array_value(value),
            HirTableField::Record(record) => {
                self.shadow_aliased_pending_integer_fields(&record.key);
                let numeric_key = record.key.table_integer_key();
                self.fields
                    .push(BuilderField::Final(HirTableField::Record(record)));
                if let Some(key) = numeric_key {
                    self.numeric_key_first_fields
                        .entry(key)
                        .or_insert(field_index);
                }
            }
        }
        self.implicit_template_fields.insert(field_index);
    }

    pub(super) fn push_record_field(&mut self, field: crate::hir::common::HirRecordField) {
        self.push_record_field_with_policy(field, RecordPromotionPolicy::Normal);
    }

    pub(super) fn push_record_field_with_policy(
        &mut self,
        field: crate::hir::common::HirRecordField,
        policy: RecordPromotionPolicy,
    ) {
        self.shadow_aliased_pending_integer_fields(&field.key);
        let current_next_index = i64::from(self.next_array_index);
        let numeric_key = field.key.table_integer_key();
        let field_index = self.fields.len();
        match numeric_key {
            Some(value)
                if (matches!(policy, RecordPromotionPolicy::Normal)
                    || matches!(policy, RecordPromotionPolicy::PreserveSetListPrefix { start_index } if value < i64::from(start_index)))
                    && value == current_next_index
                    && !self.numeric_key_first_fields.contains_key(&value)
                    && match self.allocation {
                        HirTableAllocation::Synthetic | HirTableAllocation::LuauTemplate { .. } => {
                            value_facts(&field.value).is_non_nil()
                        }
                        HirTableAllocation::Luau(allocation) => {
                            value <= i64::from(allocation.array_capacity)
                                && value_facts(&field.value).is_non_nil()
                        }
                        // PUC 的数组字段由原 SETLIST 发布；数字 record 仍计入 hash 预分配。
                        HirTableAllocation::PucBatched(_) => false,
                        HirTableAllocation::Template { .. } => true,
                        HirTableAllocation::Indexed { array_capacity, .. } => {
                            value <= i64::from(array_capacity)
                        }
                    } =>
            {
                self.push_array_value(field.value);
            }
            Some(value)
                if !matches!(self.allocation, HirTableAllocation::PucBatched(_))
                    && can_stage_pending_integer_record(
                        value,
                        current_next_index,
                        &field.value,
                        policy,
                    ) =>
            {
                if let std::collections::btree_map::Entry::Vacant(entry) =
                    self.pending_integer_fields.entry(value)
                {
                    let field_index = self.fields.len();
                    self.fields.push(BuilderField::PendingInt {
                        write_sources: field.write_sources,
                        key: value,
                        value: field.value,
                    });
                    entry.insert(PendingIntegerField {
                        field_index,
                        shadowed_at: None,
                    });
                } else {
                    self.fields.push(BuilderField::Final(HirTableField::Record(
                        crate::hir::common::HirRecordField {
                            write_sources: field.write_sources,
                            key: HirExpr::Integer(value),
                            value: field.value,
                        },
                    )));
                }
            }
            _ => self.fields.push(BuilderField::Final(HirTableField::Record(
                crate::hir::common::HirRecordField {
                    write_sources: field.write_sources,
                    key: field.key,
                    value: field.value,
                },
            ))),
        }
        if let Some(key) = numeric_key {
            self.numeric_key_first_fields
                .entry(key)
                .or_insert(field_index);
        }
    }

    pub(super) fn drain_pending_integer_fields(
        &mut self,
        restored_pending_integer_fields: &mut Vec<RestoredPendingIntegerField>,
    ) {
        while let Some(pending) = self
            .pending_integer_fields
            .remove(&i64::from(self.next_array_index))
        {
            if pending.shadowed_at.is_some()
                || self
                    .last_unknown_key_field
                    .is_some_and(|field_index| field_index > pending.field_index)
            {
                continue;
            }
            let field_index = pending.field_index;
            let old_field =
                std::mem::replace(&mut self.fields[field_index], BuilderField::MovedPendingInt);
            self.moved_fields += 1;
            let BuilderField::PendingInt {
                write_sources,
                key,
                value,
            } = old_field
            else {
                unreachable!("pending integer field index should always point at a pending field");
            };
            restored_pending_integer_fields.push(RestoredPendingIntegerField {
                field_index,
                write_sources,
                key,
                value: value.clone(),
            });
            self.fields
                .push(BuilderField::Final(HirTableField::Array(value)));
            self.next_array_index += 1;
        }
    }

    pub(super) fn demote_array_suffix(
        &mut self,
        start_index: u32,
        restored_array_fields: &mut Vec<RestoredArrayField>,
    ) -> bool {
        if start_index == self.next_array_index {
            return true;
        }
        if start_index == 0 {
            // 候选拒绝[SemanticBarrier:TableShape]：raw SETLIST 起点 0 写键 0；把它
            // 吸收到 constructor array 会改写成从键 1 开始。
            return false;
        }
        if start_index > self.next_array_index {
            // 当前调用方只在 overlap（start < next）时请求降级；保留这个边界检查，
            // 但它不是一个可执行的 constructor rewrite 候选。
            return false;
        }

        let mut array_index = 1_u32;
        for (field_index, field) in self.fields.iter_mut().enumerate() {
            let BuilderField::Final(HirTableField::Array(value)) = field else {
                continue;
            };
            if array_index >= start_index {
                restored_array_fields.push(RestoredArrayField {
                    field_index,
                    value: value.clone(),
                });
                *field = BuilderField::Final(HirTableField::Record(
                    crate::hir::common::HirRecordField {
                        write_sources: crate::hir::common::HirOperationSources::Unknown,
                        key: HirExpr::Integer(i64::from(array_index)),
                        value: value.clone(),
                    },
                ));
            }
            array_index += 1;
        }
        self.next_array_index = start_index;
        true
    }

    fn shadow_aliased_pending_integer_fields(&mut self, key: &HirExpr) {
        let shadowed_at = self.fields.len();
        match statically_known_numeric_key(key) {
            Some(Some(value)) => {
                if let Some(pending) = self.pending_integer_fields.get_mut(&value) {
                    pending.shadowed_at.get_or_insert(shadowed_at);
                }
            }
            Some(None) => {}
            None => {
                self.last_unknown_key_field = Some(shadowed_at);
            }
        }
    }
}

/// Luau 模板把 None 项预置为零，Some 项则在分配时已有真正的常量值。
/// 原运行写填回同键的隐式位置时，仍在源码字段中求值一次；不能删掉 Some 常量，
/// 也不能重新识别已经消费的零值。只跨初始常量和无事件的字面量写，运行字段保持
/// 单调顺序；原前缀位置不删除，所以未消费角色的索引在后缀压缩后仍然有效。
fn restore_luau_template_initialization(constructor: &mut HirTableConstructor) {
    if constructor.implicit_template_fields.is_empty() || constructor.trailing_multivalue.is_some()
    {
        return;
    }
    let HirTableAllocation::LuauTemplate { hash_keys } = &constructor.allocation else {
        return;
    };
    let prefix = hash_keys.len();
    // compileExprTable 只对至多 32 个裸名 record 选择 DUPTABLE。最多消费每个隐式
    // 位置一次；即使全消费仍超过上界的候选无需扫描，也不能改变为 NEWTABLE。
    if prefix >= constructor.fields.len()
        || constructor
            .implicit_template_fields
            .iter()
            .any(|index| *index >= prefix)
        || constructor.fields.len() - constructor.implicit_template_fields.len() > 32
    {
        return;
    }
    let mut initial = BTreeMap::new();
    let mut last_runtime_field = None;
    for (index, field) in constructor.fields[..prefix].iter().enumerate() {
        let HirTableField::Record(record) = field else {
            return;
        };
        let Some(key) = record.key.table_key() else {
            return;
        };
        if !hash_keys.contains(&key) || initial.insert(key, index).is_some() {
            return;
        }
        if constructor.implicit_template_fields.contains(&index)
            && record.value != HirExpr::Integer(0)
        {
            return;
        }
        if !is_template_literal(&record.value) {
            last_runtime_field = Some(index);
        }
    }
    let mut pending = constructor.implicit_template_fields.clone();
    let mut fills = Vec::new();
    for (index, field) in constructor.fields.iter().enumerate() {
        let HirTableField::Record(record) = field else {
            return;
        };
        let HirExpr::String(name) = &record.key else {
            return;
        };
        if !name
            .as_utf8()
            .is_some_and(|name| crate::decompile::DecompileDialect::Luau.is_identifier_name(name))
        {
            return;
        }
        let Some(destination) = record
            .key
            .table_key()
            .and_then(|key| initial.get(&key).copied())
        else {
            return;
        };
        if index < prefix {
            continue;
        }
        if pending.contains(&destination)
            && last_runtime_field.is_none_or(|last| last <= destination)
        {
            pending.remove(&destination);
            fills.push((index, destination));
            if !is_template_literal(&record.value) {
                last_runtime_field = Some(destination);
            }
        } else {
            // 未收回的真实字段写仍在这里，不能把后面的求值移到它前面。
            last_runtime_field = Some(index);
        }
    }
    if fills.is_empty() || constructor.fields.len() - fills.len() > 32 {
        return;
    }
    let mut removed = vec![false; constructor.fields.len()];
    for (source, destination) in fills {
        constructor.fields[destination] = std::mem::replace(
            &mut constructor.fields[source],
            HirTableField::Array(HirExpr::Nil),
        );
        removed[source] = true;
    }
    let mut removed = removed.into_iter();
    constructor
        .fields
        .retain(|_| !removed.next().expect("one decision per field"));
    constructor.implicit_template_fields = pending;
}

/// TDUP 的 nil 数组槽不是必须输出的源码字段：`{nil,"tail"}; t[1]=f()` 可以复原
/// `{f(),"tail"}`。只跨过字面量，运行时字段的目的位置必须保持单调，不能把倒序
/// `t[2]=a(); t[1]=b()` 变成先 b 后 a。这里仅归约完整候选，原 builder 不变，失败仍
/// 由外层整区间事务丢弃；容量、owner 独立性及 producer 根另由原有提交证明核对。
fn restore_template_nil_slots(constructor: &mut HirTableConstructor) {
    if !matches!(constructor.allocation, HirTableAllocation::Template { .. }) {
        return;
    }
    let mut nil_slots = Vec::new();
    let mut last_runtime_field = None;
    let mut removed = vec![false; constructor.fields.len()];
    for (index, removed) in removed.iter_mut().enumerate() {
        if constructor.implicit_template_fields.contains(&index) {
            // 未消费的 TDUP hash marker 仍描述原 hash key，不能借相同数字外形把它
            // 改成数组槽；该位置也隔开其前后的运行时字段移动。
            last_runtime_field = Some(index);
            continue;
        }
        let slot = match &constructor.fields[index] {
            HirTableField::Array(value) => {
                nil_slots.push(matches!(value, HirExpr::Nil).then_some(index));
                if !is_template_literal(value) {
                    last_runtime_field = Some(index);
                }
                continue;
            }
            HirTableField::Record(record) => match record.key {
                HirExpr::Integer(key) => {
                    usize::try_from(key).ok().and_then(|key| key.checked_sub(1))
                }
                _ => None,
            },
        };
        let destination = slot.and_then(|slot| nil_slots.get_mut(slot)?.take());
        let Some(destination) = destination
            .filter(|destination| last_runtime_field.is_none_or(|last| last <= *destination))
        else {
            // record 写入可能改变表布局；即使 key/value 是常量也不能跨它搬动调用。
            last_runtime_field = Some(index);
            continue;
        };
        let HirTableField::Record(record) = std::mem::replace(
            &mut constructor.fields[index],
            HirTableField::Array(HirExpr::Nil),
        ) else {
            unreachable!()
        };
        if !is_template_literal(&record.value) {
            last_runtime_field = Some(destination);
        }
        constructor.fields[destination] = HirTableField::Array(record.value);
        *removed = true;
    }
    retain_fields_and_template_roles(constructor, &removed);
}

/// LuaJIT TDUP 的 nil hash marker 只描述原模板 key，不是独立源码求值。完整 region 已按
/// 原事件顺序追加同键运行字段后，可删除 marker 而保留后继字段位置；后继字段仍须满足
/// LuaJIT 模板初始化规则，保证重新编译时原 key 集合不缩小。未匹配 marker 继续显式输出。
fn restore_template_nil_hash_fields(constructor: &mut HirTableConstructor) {
    let HirTableAllocation::Template { hash_keys, .. } = &constructor.allocation else {
        return;
    };
    if constructor.implicit_template_fields.is_empty() {
        return;
    }

    let mut markers = BTreeMap::new();
    for &index in &constructor.implicit_template_fields {
        let Some(HirTableField::Record(record)) = constructor.fields.get(index) else {
            continue;
        };
        let Some(key) = record.key.table_key() else {
            continue;
        };
        if matches!(&record.value, HirExpr::Nil) && hash_keys.contains(&key) {
            markers.insert(key, index);
        }
    }
    if markers.is_empty() {
        return;
    }

    let mut removed = vec![false; constructor.fields.len()];
    for (index, field) in constructor.fields.iter().enumerate() {
        let HirTableField::Record(record) = field else {
            continue;
        };
        let Some(marker) = record
            .key
            .table_key()
            .and_then(|key| markers.get(&key).copied())
        else {
            continue;
        };
        if index > marker && initializes_template(&record.key, &record.value) {
            removed[marker] = true;
        }
    }
    if !removed.iter().any(|removed| *removed) {
        return;
    }

    retain_fields_and_template_roles(constructor, &removed);
}

/// 字段压缩和 lowering role 使用同一旧坐标；任何 owner 删除字段时都必须在同一遍扫描中
/// 重映射角色，不能让后续模板恢复把已移动的索引解释成另一个字段。
fn retain_fields_and_template_roles(constructor: &mut HirTableConstructor, removed: &[bool]) {
    debug_assert_eq!(constructor.fields.len(), removed.len());
    let old_implicit = std::mem::take(&mut constructor.implicit_template_fields);
    let mut new_implicit = std::collections::BTreeSet::new();
    let mut old_index = 0;
    let mut new_index = 0;
    constructor.fields.retain(|_| {
        let retain = !removed[old_index];
        if retain {
            if old_implicit.contains(&old_index) {
                new_implicit.insert(new_index);
            }
            new_index += 1;
        }
        old_index += 1;
        retain
    });
    constructor.implicit_template_fields = new_implicit;
}

fn is_template_literal(value: &HirExpr) -> bool {
    matches!(
        value,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

/// 索引式构造器的预分配是前层事实；只有完整有序前缀能复现该容量时才恢复数组字段。
/// 字段没有换序，故 indexed VM 的写入事件也不变；不把零散整数键猜成数组初始化。
fn restore_indexed_array_fields(constructor: &mut HirTableConstructor) {
    if constructor.trailing_multivalue.is_some() || !constructor.implicit_template_fields.is_empty()
    {
        // open tail 的起点已由 rebuild 核对；容量相同不能证明扩大固定前缀合法。
        // {"head", [2] = "old", many()} 中的 record 必须保留覆盖后的空返回路径。
        // 未消费的 TDUP marker 还必须保持 hash key 角色，不能改写成连续 array 字段。
        return;
    }
    let mut array_fields = 0;
    for field in &constructor.fields {
        match field {
            HirTableField::Array(_) => array_fields += 1,
            HirTableField::Record(record)
                if record.key == HirExpr::Integer((array_fields + 1) as i64) =>
            {
                array_fields += 1
            }
            _ => {}
        }
    }
    if !constructor.matches_indexed_array_capacity(array_fields) {
        return;
    }
    let mut array_index = 1;
    for field in &mut constructor.fields {
        match field {
            HirTableField::Array(_) => array_index += 1,
            HirTableField::Record(record) if record.key == HirExpr::Integer(array_index) => {
                *field = HirTableField::Array(std::mem::replace(&mut record.value, HirExpr::Nil));
                array_index += 1;
            }
            _ => {}
        }
    }
}

fn statically_known_numeric_key(key: &HirExpr) -> Option<Option<i64>> {
    match key {
        HirExpr::Integer(_) | HirExpr::Number(_) => key.table_integer_key().map(Some),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::String(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::Closure(_)
        | HirExpr::TableConstructor(_) => Some(None),
        HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::TableAccess(_)
        | HirExpr::Unary(_)
        | HirExpr::Binary(_)
        | HirExpr::LogicalAnd(_)
        | HirExpr::LogicalOr(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::CaptureInitializer(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => None,
    }
}

fn can_reorder_integer_record_value(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
    )
}

fn can_stage_pending_integer_record(
    value: i64,
    current_next_index: i64,
    record_value: &HirExpr,
    policy: RecordPromotionPolicy,
) -> bool {
    let is_future_array_slot = match policy {
        RecordPromotionPolicy::Normal => value > current_next_index,
        RecordPromotionPolicy::PreserveSetListPrefix { start_index } => {
            value >= i64::from(start_index)
        }
    };
    if !is_future_array_slot {
        return false;
    }

    if !can_reorder_integer_record_value(record_value) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：暂存 future integer record 会把 value 求值
        // 延后到较小整数键之后；反例见 regress_212_table_constructor_field_order 与
        // lua54_01_close#12。
        return false;
    }
    true
}
