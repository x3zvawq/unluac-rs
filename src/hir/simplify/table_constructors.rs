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

mod bindings;
mod inline_value;
mod rebuild;
mod scan;

use crate::hir::common::{HirBlock, HirExpr, HirProto, HirStmt, HirTableSetList, LocalId, TempId};

use self::bindings::collect_materialized_binding_counts;
use self::scan::{constructor_seed, install_constructor_seed, try_rebuild_constructor_region};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
enum TableBinding {
    Temp(TempId),
    Local(LocalId),
}

#[derive(Debug, Clone)]
enum RegionStep {
    Producer(TableBinding, HirExpr),
    ProducerGroup(ProducerGroup),
    Record(crate::hir::common::HirRecordField),
    SetList(HirTableSetList),
}

#[derive(Debug, Clone)]
struct ProducerGroup {
    slots: Vec<ProducerGroupSlot>,
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone)]
struct ProducerGroupSlot {
    binding: TableBinding,
    value: Option<HirExpr>,
}

#[derive(Debug, Clone)]
struct PendingProducer {
    binding: TableBinding,
    value: Option<HirExpr>,
    group: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
struct ProducerGroupMeta {
    drop_without_consumption_is_safe: bool,
}

#[derive(Debug, Clone)]
enum SegmentToken {
    Producer(TableBinding),
    Record(crate::hir::common::HirRecordField),
}

pub(super) fn stabilize_table_constructors_in_proto(proto: &mut HirProto) -> bool {
    let materialized_bindings = collect_materialized_binding_counts(&proto.body);
    stabilize_block(&mut proto.body, &materialized_bindings)
}

fn stabilize_block(
    block: &mut HirBlock,
    materialized_bindings: &std::collections::BTreeMap<TableBinding, usize>,
) -> bool {
    let mut changed = false;

    for stmt in &mut block.stmts {
        changed |= stabilize_nested(stmt, materialized_bindings);
    }

    let mut index = 0;
    while index < block.stmts.len() {
        let Some((binding, seed_ctor)) = constructor_seed(&block.stmts[index]) else {
            index += 1;
            continue;
        };

        let Some((rebuilt_ctor, end_index)) =
            try_rebuild_constructor_region(block, index, binding, seed_ctor, materialized_bindings)
        else {
            index += 1;
            continue;
        };

        install_constructor_seed(&mut block.stmts[index], rebuilt_ctor);
        debug_assert!(
            end_index > index,
            "constructor rewrite must consume at least one trailing stmt"
        );
        block.stmts.drain(index + 1..=end_index);
        changed = true;
        index += 1;
    }

    changed
}

fn stabilize_nested(
    stmt: &mut HirStmt,
    materialized_bindings: &std::collections::BTreeMap<TableBinding, usize>,
) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = stabilize_block(&mut if_stmt.then_block, materialized_bindings);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= stabilize_block(else_block, materialized_bindings);
            }
            changed
        }
        HirStmt::While(while_stmt) => stabilize_block(&mut while_stmt.body, materialized_bindings),
        HirStmt::Repeat(repeat_stmt) => {
            stabilize_block(&mut repeat_stmt.body, materialized_bindings)
        }
        HirStmt::NumericFor(numeric_for) => {
            stabilize_block(&mut numeric_for.body, materialized_bindings)
        }
        HirStmt::GenericFor(generic_for) => {
            stabilize_block(&mut generic_for.body, materialized_bindings)
        }
        HirStmt::Block(block) => stabilize_block(block, materialized_bindings),
        HirStmt::Unstructured(unstructured) => {
            stabilize_block(&mut unstructured.body, materialized_bindings)
        }
        HirStmt::LocalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_)
        | HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_) => false,
    }
}

#[cfg(test)]
mod tests;
