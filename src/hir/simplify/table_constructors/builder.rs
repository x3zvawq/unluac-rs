//! 这个子模块承载 `HirTableConstructor` rebuild 时的 builder 状态机。
//!
//! rebuild 主流程只关心 region step 如何 flush；字段顺序、数组下标推进、整数 record
//! 是否可以暂存为未来 array slot，则属于构造器内部状态。本文件只维护这些 builder
//! 规则，不扫描语句，也不决定哪些语句可以进入构造器 region。
//!
//! 输入形状：已有构造器字段 + 后续 array / record / set-list 值。
//! 输出形状：按 Lua 构造器语义重新排序后的 `HirTableConstructor`。

use std::collections::BTreeMap;

use crate::hir::common::{HirExpr, HirTableConstructor, HirTableField, HirTableKey};

use super::{RebuildScratch, RestoredPendingIntegerField};

#[derive(Debug, Clone)]
enum BuilderField {
    Final(HirTableField),
    PendingInt { key: i64, value: HirExpr },
    MovedPendingInt,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum RecordPromotionPolicy {
    Normal,
    PreserveSetListPrefix { start_index: u32 },
}

#[derive(Debug, Clone)]
pub(super) struct ConstructorBuilder {
    fields: Vec<BuilderField>,
    pub(super) trailing_multivalue: Option<HirExpr>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, usize>,
}

#[derive(Debug, Clone)]
pub(super) struct BuilderCheckpoint {
    fields_len: usize,
    trailing_multivalue: Option<HirExpr>,
    next_array_index: u32,
    pending_integer_fields: BTreeMap<i64, usize>,
    restored_pending_integer_fields_len: usize,
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
            pending_integer_fields: self.pending_integer_fields.clone(),
            restored_pending_integer_fields_len: scratch.restored_pending_integer_fields.len(),
        }
    }

    pub(super) fn rollback(&mut self, checkpoint: BuilderCheckpoint, scratch: &mut RebuildScratch) {
        self.fields.truncate(checkpoint.fields_len);
        self.trailing_multivalue = checkpoint.trailing_multivalue;
        self.next_array_index = checkpoint.next_array_index;
        self.pending_integer_fields = checkpoint.pending_integer_fields;
        for restored in scratch.restored_pending_integer_fields
            [checkpoint.restored_pending_integer_fields_len..]
            .iter()
            .rev()
        {
            self.fields[restored.field_index] = BuilderField::PendingInt {
                key: restored.key,
                value: restored.value.clone(),
            };
        }
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
    }

    pub(super) fn commit(&mut self, checkpoint: &BuilderCheckpoint, scratch: &mut RebuildScratch) {
        scratch
            .restored_pending_integer_fields
            .truncate(checkpoint.restored_pending_integer_fields_len);
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
        let current_next_index = i64::from(self.next_array_index);
        match field.key {
            HirTableKey::Expr(HirExpr::Integer(value))
                if matches!(policy, RecordPromotionPolicy::Normal)
                    && value == current_next_index =>
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
                    entry.insert(field_index);
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
        while let Some(field_index) = self
            .pending_integer_fields
            .remove(&i64::from(self.next_array_index))
        {
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
}

fn can_reorder_integer_record_value(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::Closure(_) => true,
        HirExpr::Unary(unary) => can_reorder_integer_record_value(&unary.expr),
        HirExpr::Binary(binary) => {
            can_reorder_integer_record_value(&binary.lhs)
                && can_reorder_integer_record_value(&binary.rhs)
        }
        _ => false,
    }
}

fn can_stage_pending_integer_record(
    value: i64,
    current_next_index: i64,
    record_value: &HirExpr,
    policy: RecordPromotionPolicy,
) -> bool {
    if !can_reorder_integer_record_value(record_value) {
        return false;
    }

    match policy {
        RecordPromotionPolicy::Normal => value > current_next_index,
        RecordPromotionPolicy::PreserveSetListPrefix { start_index } => {
            value >= i64::from(start_index)
        }
    }
}
