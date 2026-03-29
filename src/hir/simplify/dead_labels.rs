//! 这个文件负责清理 HIR 里已经没有入边的机械 label。
//!
//! fallback label/goto body 会先给每个可能成为跳转目标的 block 发一个稳定 label。
//! 但经过 close-scope 物化、branch/loop 恢复之后，入口块和大量中间 pad 的 label 往往
//! 已经不再被任何 `goto` 命中。它们继续留在 HIR 里不仅会让源码多出 `::L0::` 这类
//! 噪音，还会挡住后续 locals pass 对顶层 temp 的提升。
//!
//! 它依赖更前面的 HIR 结构恢复和 scope/loop pass 已经稳定了真正需要保留的 goto，
//! 这里只做“没有任何引用”的 label 清扫，不重新判断控制流是否可结构化，也不会替
//! 前层兜底重写 jump 目标。
//!
//! 例子：
//! - `::L1::` 如果已经没有任何 `goto L1`，这里会把它删掉
//! - fallback body 里为了每个 block 都预发的 label，经过 branch/loop 吸收后只要
//!   失去引用，就会在这里统一清理
//! - 它不会删除仍被 `goto` 命中的 label，也不会主动合并 block 或改写 goto 结构

use std::collections::BTreeSet;

use crate::hir::common::{HirLabelId, HirProto, HirStmt};

use super::visit::{HirVisitor, visit_proto};
use super::walk::{HirRewritePass, rewrite_proto};

#[cfg(test)]
mod tests;

pub(super) fn remove_unused_labels_in_proto(proto: &mut HirProto) -> bool {
    let referenced = collect_referenced_labels(proto);
    let mut pass = DeadLabelPass {
        referenced: &referenced,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadLabelPass<'a> {
    referenced: &'a BTreeSet<HirLabelId>,
}

impl HirRewritePass for DeadLabelPass<'_> {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(
            |stmt| !matches!(stmt, HirStmt::Label(label) if !self.referenced.contains(&label.id)),
        );
        block.stmts.len() != original_len
    }
}

fn collect_referenced_labels(proto: &HirProto) -> BTreeSet<HirLabelId> {
    let mut collector = ReferencedLabelCollector::default();
    visit_proto(proto, &mut collector);
    collector.labels
}

#[derive(Default)]
struct ReferencedLabelCollector {
    labels: BTreeSet<HirLabelId>,
}

impl HirVisitor for ReferencedLabelCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Goto(goto_stmt) = stmt else {
            return;
        };
        self.labels.insert(goto_stmt.target);
    }
}
