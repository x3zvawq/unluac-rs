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

use crate::hir::common::{HirExpr, HirPackTail, HirTableConstructor, HirTableField, HirTableKey};

use super::{RebuildScratch, RestoredArrayField, RestoredPendingIntegerField};

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
    fields: Vec<BuilderField>,
    pub(super) trailing_multivalue: Option<HirPackTail>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, PendingIntegerField>,
}

#[derive(Debug, Clone)]
pub(super) struct BuilderCheckpoint {
    fields_len: usize,
    trailing_multivalue: Option<HirPackTail>,
    next_array_index: u32,
    restored_pending_integer_fields_len: usize,
    restored_array_fields_len: usize,
}

impl ConstructorBuilder {
    pub(super) fn from_constructor(constructor: HirTableConstructor) -> Self {
        let mut builder = Self {
            fields: Vec::with_capacity(constructor.fields.len()),
            trailing_multivalue: constructor.trailing_multivalue,
            next_array_index: 1,
            pending_integer_fields: BTreeMap::new(),
        };
        for field in constructor.fields {
            match field {
                HirTableField::Array(value) => {
                    builder.push_array_value(value);
                }
                HirTableField::Record(field) => {
                    builder.push_record_field(field);
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
                        key: HirTableKey::Expr(HirExpr::Integer(key)),
                        value,
                    }));
                }
                BuilderField::MovedPendingInt => {}
            }
        }
        HirTableConstructor {
            fields,
            trailing_multivalue: self.trailing_multivalue,
        }
    }

    pub(super) fn checkpoint(&self, scratch: &RebuildScratch) -> BuilderCheckpoint {
        BuilderCheckpoint {
            fields_len: self.fields.len(),
            trailing_multivalue: self.trailing_multivalue.clone(),
            next_array_index: self.next_array_index,
            restored_pending_integer_fields_len: scratch.restored_pending_integer_fields.len(),
            restored_array_fields_len: scratch.restored_array_fields.len(),
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: BuilderCheckpoint, scratch: &mut RebuildScratch) {
        self.fields.truncate(checkpoint.fields_len);
        self.trailing_multivalue = checkpoint.trailing_multivalue;
        self.next_array_index = checkpoint.next_array_index;
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

    pub(super) fn push_array_value(&mut self, value: HirExpr) {
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
        match field.key {
            HirTableKey::Expr(HirExpr::Integer(value))
                if matches!(policy, RecordPromotionPolicy::Normal)
                    && value == current_next_index
                    && !self.has_numeric_key(value)
                    && expr_is_definitely_non_nil(&field.value) =>
            {
                self.push_array_value(field.value);
            }
            HirTableKey::Expr(HirExpr::Integer(value))
                if can_stage_pending_integer_record(
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
                            key: HirTableKey::Expr(HirExpr::Integer(value)),
                            value: field.value,
                        },
                    )));
                }
            }
            key => self.fields.push(BuilderField::Final(HirTableField::Record(
                crate::hir::common::HirRecordField {
                    key,
                    value: field.value,
                },
            ))),
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
            if pending.shadowed_at.is_some() {
                continue;
            }
            let field_index = pending.field_index;
            let old_field =
                std::mem::replace(&mut self.fields[field_index], BuilderField::MovedPendingInt);
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
        if start_index == 0 || start_index > self.next_array_index {
            // 候选拒绝[SemanticBarrier:TableShape]：SETLIST 起点跳过尚未生成的隐式数组槽，
            // 不能用 constructor array 语法表示而不改变后续隐式下标。
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
                        key: HirTableKey::Expr(HirExpr::Integer(i64::from(array_index))),
                        value: value.clone(),
                    },
                ));
            }
            array_index += 1;
        }
        self.next_array_index = start_index;
        true
    }

    fn shadow_aliased_pending_integer_fields(&mut self, key: &HirTableKey) {
        let shadowed_at = self.fields.len();
        match statically_known_numeric_key(key) {
            Some(Some(value)) => {
                if let Some(pending) = self.pending_integer_fields.get_mut(&value) {
                    pending.shadowed_at.get_or_insert(shadowed_at);
                }
            }
            Some(None) => {}
            None => {
                for pending in self.pending_integer_fields.values_mut() {
                    pending.shadowed_at.get_or_insert(shadowed_at);
                }
            }
        }
    }

    fn has_numeric_key(&self, key: i64) -> bool {
        let mut array_index = 1_i64;
        self.fields.iter().any(|field| match field {
            BuilderField::Final(HirTableField::Array(_)) => {
                let matches = array_index == key;
                array_index += 1;
                matches
            }
            BuilderField::Final(HirTableField::Record(record)) => {
                numeric_key_matches(&record.key, key)
            }
            BuilderField::PendingInt { key: existing, .. } => *existing == key,
            BuilderField::MovedPendingInt => false,
        })
    }
}

fn statically_known_numeric_key(key: &HirTableKey) -> Option<Option<i64>> {
    match key {
        HirTableKey::Name(_) => Some(None),
        HirTableKey::Expr(HirExpr::Integer(value)) => Some(Some(*value)),
        HirTableKey::Expr(HirExpr::Number(value)) => {
            if value.is_finite()
                && value.fract() == 0.0
                && value.abs() <= ((1_u64 << f64::MANTISSA_DIGITS) as f64)
            {
                Some(Some(*value as i64))
            } else {
                None
            }
        }
        HirTableKey::Expr(
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::String(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::Closure(_)
            | HirExpr::TableConstructor(_),
        ) => Some(None),
        HirTableKey::Expr(
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
            | HirExpr::Unresolved(_),
        ) => None,
    }
}

fn numeric_key_matches(key: &HirTableKey, expected: i64) -> bool {
    match key {
        HirTableKey::Expr(HirExpr::Integer(value)) => *value == expected,
        HirTableKey::Expr(HirExpr::Number(value)) => {
            value.is_finite() && value.fract() == 0.0 && *value == expected as f64
        }
        _ => false,
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

pub(super) fn expr_is_definitely_non_nil(expr: &HirExpr) -> bool {
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
            | HirExpr::Closure(_)
            | HirExpr::TableConstructor(_)
    )
}

fn can_stage_pending_integer_record(
    value: i64,
    current_next_index: i64,
    record_value: &HirExpr,
    policy: RecordPromotionPolicy,
) -> bool {
    if !can_reorder_integer_record_value(record_value) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：暂存 future integer record 会把 value 求值
        // 延后到较小整数键之后；反例见 regress_212_table_constructor_field_order 与
        // lua54_01_close#12。
        return false;
    }

    match policy {
        RecordPromotionPolicy::Normal => value > current_next_index,
        RecordPromotionPolicy::PreserveSetListPrefix { start_index } => {
            value >= i64::from(start_index)
        }
    }
}
