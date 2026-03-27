//! 这个文件负责清理 HIR 里已经没有入边的机械 label。
//!
//! fallback label/goto body 会先给每个可能成为跳转目标的 block 发一个稳定 label。
//! 但经过 close-scope 物化、branch/loop 恢复之后，入口块和大量中间 pad 的 label 往往
//! 已经不再被任何 `goto` 命中。它们继续留在 HIR 里不仅会让源码多出 `::L0::` 这类
//! 噪音，还会挡住后续 locals pass 对顶层 temp 的提升。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirLabelId, HirProto, HirStmt};

#[cfg(test)]
mod tests;

pub(super) fn remove_unused_labels_in_proto(proto: &mut HirProto) -> bool {
    let referenced = collect_referenced_labels(&proto.body);
    rewrite_block(&mut proto.body, &referenced)
}

fn collect_referenced_labels(block: &HirBlock) -> BTreeSet<HirLabelId> {
    let mut labels = BTreeSet::new();
    collect_block_labels(block, &mut labels);
    labels
}

fn collect_block_labels(block: &HirBlock, labels: &mut BTreeSet<HirLabelId>) {
    for stmt in &block.stmts {
        match stmt {
            HirStmt::Goto(goto_stmt) => {
                labels.insert(goto_stmt.target);
            }
            HirStmt::If(if_stmt) => {
                collect_block_labels(&if_stmt.then_block, labels);
                if let Some(else_block) = &if_stmt.else_block {
                    collect_block_labels(else_block, labels);
                }
            }
            HirStmt::While(while_stmt) => collect_block_labels(&while_stmt.body, labels),
            HirStmt::Repeat(repeat_stmt) => collect_block_labels(&repeat_stmt.body, labels),
            HirStmt::NumericFor(numeric_for) => collect_block_labels(&numeric_for.body, labels),
            HirStmt::GenericFor(generic_for) => collect_block_labels(&generic_for.body, labels),
            HirStmt::Block(block) => collect_block_labels(block, labels),
            HirStmt::Unstructured(unstructured) => collect_block_labels(&unstructured.body, labels),
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
            | HirStmt::Label(_) => {}
        }
    }
}

fn rewrite_block(block: &mut HirBlock, referenced: &BTreeSet<HirLabelId>) -> bool {
    let mut changed = false;
    for stmt in &mut block.stmts {
        changed |= rewrite_stmt(stmt, referenced);
    }

    let original_len = block.stmts.len();
    block
        .stmts
        .retain(|stmt| !matches!(stmt, HirStmt::Label(label) if !referenced.contains(&label.id)));
    changed |= block.stmts.len() != original_len;

    changed
}

fn rewrite_stmt(stmt: &mut HirStmt, referenced: &BTreeSet<HirLabelId>) -> bool {
    match stmt {
        HirStmt::If(if_stmt) => {
            let mut changed = rewrite_block(&mut if_stmt.then_block, referenced);
            if let Some(else_block) = &mut if_stmt.else_block {
                changed |= rewrite_block(else_block, referenced);
            }
            changed
        }
        HirStmt::While(while_stmt) => rewrite_block(&mut while_stmt.body, referenced),
        HirStmt::Repeat(repeat_stmt) => rewrite_block(&mut repeat_stmt.body, referenced),
        HirStmt::NumericFor(numeric_for) => rewrite_block(&mut numeric_for.body, referenced),
        HirStmt::GenericFor(generic_for) => rewrite_block(&mut generic_for.body, referenced),
        HirStmt::Block(block) => rewrite_block(block, referenced),
        HirStmt::Unstructured(unstructured) => rewrite_block(&mut unstructured.body, referenced),
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
