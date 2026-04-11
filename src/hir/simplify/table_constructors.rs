//! 这个文件负责把“稳定的建表片段”收回 `TableConstructor`。
//!
//! `NewTable + SetTable + SetList` 在 low-IR 里天然是分散的；如果 HIR 一直把它们保留成
//! 零散语句，后面 AST 虽然还能继续工作，但整层会长期带着明显的机械噪音。这里专门吃一类
//! 很稳的构造区域：
//! 1. 先出现一个空表构造器 seed；
//! 2. 后面紧跟一段 keyed write、简单值生产和 `table-set-list`；
//! 3. 这段时间里表值没有逃逸，也没有跨语句依赖还没落地的中间绑定。
//!
//! 这样做的目的不是“尽可能多地猜源码”，而是把已经能够证明安全的构造片段收回更自然的
//! HIR 形状，为后续 AST 降低继续减负。
//! 另外，如果构造器 seed 在 block 尾声只剩一次“把整张表 handoff 给最终目标”的写入，
//! 这里也会把 owner 直接认回最终目标，避免后层继续携带机械性的中转 local。

mod bindings;
mod inline_value;
mod rebuild;
mod scan;

use std::collections::BTreeMap;

use crate::hir::common::{HirAssign, HirExpr, HirLValue, HirProto, HirStmt, LocalId, TempId};

use self::bindings::collect_materialized_binding_counts;
use self::scan::{
    constructor_seed, install_constructor_seed, trailing_constructor_handoff,
    try_rebuild_constructor_region,
};
use super::walk::{HirRewritePass, rewrite_proto};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum TableBinding {
    Temp(TempId),
    Local(LocalId),
}

type BindingId = usize;

#[derive(Debug, Clone, Copy)]
enum RegionStep {
    Producer {
        stmt_index: usize,
        slot_index: usize,
    },
    ProducerGroup {
        stmt_index: usize,
    },
    Record {
        stmt_index: usize,
    },
    SetList {
        stmt_index: usize,
    },
}

#[derive(Debug, Clone)]
struct PendingProducer {
    binding: TableBinding,
    binding_id: BindingId,
    source: PendingProducerSource,
    group: Option<usize>,
}

#[derive(Debug, Clone)]
enum PendingProducerSource {
    Value {
        stmt_index: usize,
        value_index: usize,
    },
    Empty,
}

#[derive(Debug, Clone, Copy)]
struct ProducerGroupMeta {
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone, Copy)]
enum SegmentToken {
    Producer { producer_index: usize },
    Record { prepared_record_index: usize },
}

#[derive(Debug, Clone)]
struct RestoredPendingIntegerField {
    field_index: usize,
    key: i64,
    value: HirExpr,
}

#[derive(Debug, Clone, Default)]
struct RebuildScratch {
    pending_producers: Vec<PendingProducer>,
    producer_groups: Vec<ProducerGroupMeta>,
    tokens: Vec<SegmentToken>,
    prepared_records: Vec<crate::hir::common::HirRecordField>,
    producer_index_by_binding: Vec<Option<usize>>,
    consumed_bindings: Vec<bool>,
    consumed_groups: Vec<bool>,
    removed_materializations: Vec<u32>,
    touched_binding_ids: Vec<BindingId>,
    restored_pending_integer_fields: Vec<RestoredPendingIntegerField>,
}

pub(super) fn stabilize_table_constructors_in_proto(proto: &mut HirProto) -> bool {
    let materialized_bindings = collect_materialized_binding_counts(&proto.body);
    let mut pass = TableConstructorPass {
        materialized_bindings,
    };
    rewrite_proto(proto, &mut pass)
}

struct TableConstructorPass {
    materialized_bindings: BTreeMap<TableBinding, usize>,
}

impl HirRewritePass for TableConstructorPass {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        let mut changed = false;
        let mut scratch = RebuildScratch::default();
        let mut index = 0;
        while index < block.stmts.len() {
            let Some((binding, seed_ctor)) = constructor_seed(&block.stmts[index]) else {
                index += 1;
                continue;
            };

            let (constructor, end_index, rebuilt_region, retained_stmts) =
                match try_rebuild_constructor_region(
                    block,
                    index,
                    binding,
                    seed_ctor.clone(),
                    &self.materialized_bindings,
                    &mut scratch,
                ) {
                    Some((rebuilt_ctor, end_index, retained)) => {
                        (rebuilt_ctor, end_index, true, retained)
                    }
                    None => (seed_ctor, index, false, Vec::new()),
                };

            let handoff_target =
                trailing_constructor_handoff(&block.stmts[(end_index + 1)..], binding);
            if !rebuilt_region && handoff_target.is_none() {
                index += 1;
                continue;
            }

            let consumed_handoff = handoff_target.is_some();
            install_constructor_owner(&mut block.stmts[index], handoff_target, constructor);
            let drain_end = end_index + usize::from(consumed_handoff);
            if drain_end > index {
                if retained_stmts.is_empty() {
                    block.stmts.drain(index + 1..=drain_end);
                } else {
                    for i in (index + 1..=drain_end).rev() {
                        if !retained_stmts.contains(&i) {
                            block.stmts.remove(i);
                        }
                    }
                }
            }
            changed = true;
            index += 1;
        }

        changed
    }
}

fn install_constructor_owner(
    stmt: &mut HirStmt,
    target: Option<HirLValue>,
    constructor: crate::hir::common::HirTableConstructor,
) {
    if let Some(target) = target {
        *stmt = HirStmt::Assign(Box::new(HirAssign {
            targets: vec![target],
            values: vec![HirExpr::TableConstructor(Box::new(constructor))],
        }));
        return;
    }
    install_constructor_seed(stmt, constructor);
}

#[cfg(test)]
mod tests;
