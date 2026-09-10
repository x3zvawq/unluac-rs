//! 这个子模块承载 `HirTableConstructor` rebuild 时的 builder 状态机。
//!
//! rebuild 主流程只关心 region step 如何 flush；字段顺序、数组下标推进、整数 record
//! 是否可以暂存为未来 array slot，则属于构造器内部状态。本文件只维护这些 builder
//! 规则，不扫描语句，也不决定哪些语句可以进入构造器 region。
//!
//! 输入形状：已有构造器字段 + 后续 array / record / set-list 值。
//! 输出形状：按 Lua 构造器语义重新排序后的 `HirTableConstructor`。未来整数键只有在后续
//! 写入可证明不别名时才能晋升为 array；open list 覆盖已有后缀时先降回显式整数字段。

use std::collections::BTreeMap;

use crate::hir::common::{
    HirExpr, HirPackTail, HirTableAllocation, HirTableConstructor, HirTableField,
};

use super::{RebuildScratch, RestoredArrayField, RestoredPendingIntegerField};
use crate::hir::value_facts::value_facts;
use crate::value_semantics::table::TableExpression;

#[derive(Debug, Clone)]
enum BuilderField {
    Final(HirTableField),
    PendingInt { key: i64, value: HirExpr },
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
    allocation: HirTableAllocation,
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
    pub(super) fn from_constructor(constructor: HirTableConstructor) -> Self {
        let mut builder = Self {
            allocation: constructor.allocation,
            fields: Vec::with_capacity(constructor.fields.len()),
            trailing_multivalue: constructor.trailing_multivalue,
            next_array_index: 1,
            pending_integer_fields: BTreeMap::new(),
            last_unknown_key_field: None,
            numeric_key_first_fields: BTreeMap::new(),
            moved_fields: 0,
        };
        for field in constructor.fields {
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
        for field in self.fields {
            match field {
                BuilderField::Final(field) => fields.push(field),
                BuilderField::PendingInt { key, value } => {
                    fields.push(HirTableField::Record(crate::hir::common::HirRecordField {
                        key: HirExpr::Integer(key),
                        value,
                    }));
                }
                BuilderField::MovedPendingInt => {}
            }
        }
        let mut constructor = HirTableConstructor {
            fields,
            trailing_multivalue: self.trailing_multivalue,
            allocation: self.allocation,
        };
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
                            key: HirExpr::Integer(value),
                            value: field.value,
                        },
                    )));
                }
            }
            _ => self.fields.push(BuilderField::Final(HirTableField::Record(
                crate::hir::common::HirRecordField {
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
            let BuilderField::PendingInt { key, value } = old_field else {
                unreachable!("pending integer field index should always point at a pending field");
            };
            restored_pending_integer_fields.push(RestoredPendingIntegerField {
                field_index,
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

/// 索引式构造器的预分配是前层事实；只有完整有序前缀能复现该容量时才恢复数组字段。
/// 字段没有换序，故 indexed VM 的写入事件也不变；不把零散整数键猜成数组初始化。
fn restore_indexed_array_fields(constructor: &mut HirTableConstructor) {
    if constructor.trailing_multivalue.is_some() {
        // open tail 的起点已由 rebuild 核对；容量相同不能证明扩大固定前缀合法。
        // {"head", [2] = "old", many()} 中的 record 必须保留覆盖后的空返回路径。
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
