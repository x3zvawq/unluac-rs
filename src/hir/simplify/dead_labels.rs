//! 删除 HIR 中没有 goto 引用且不再承担 cleanup 边界的机械标签。
//!
//! 消费当前 label 引用与 pending TBC/Close 事实，不合并 block 或改写跳转目标。
//! 例如无人引用的 ::L1:: 可删除；仍是 close-scopes active-set 边界的标签，
//! 须等对应资源协议消费后再清理。

use std::collections::BTreeSet;

use crate::hir::common::{HirLabel, HirLabelId, HirProto, HirStmt};

use super::close_scopes::pending_tbc_boundary_labels_in_proto;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::visit::{HirVisitor, visit_proto};

pub(super) fn remove_unused_labels_in_proto(proto: &mut HirProto) -> bool {
    let facts = collect_label_facts(proto);
    let pending_tbc_boundaries = pending_tbc_boundary_labels_in_proto(proto);
    let mut pass = DeadLabelPass {
        referenced: &facts.referenced,
        pending_tbc_boundaries: &pending_tbc_boundaries,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadLabelPass<'a> {
    referenced: &'a BTreeSet<HirLabelId>,
    pending_tbc_boundaries: &'a BTreeSet<HirLabelId>,
}

impl HirRewritePass for DeadLabelPass<'_> {
    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| {
            !matches!(stmt, HirStmt::Label(label) if label_is_removable(
                label,
                self.referenced,
                self.pending_tbc_boundaries,
            ))
        });
        block.stmts.len() != original_len
    }
}

fn label_is_removable(
    label: &HirLabel,
    referenced: &BTreeSet<HirLabelId>,
    pending_tbc_boundaries: &BTreeSet<HirLabelId>,
) -> bool {
    // 仍被 `goto` 命中的 label 不是 dead-label 候选；候选从“全 proto 无引用”形成。
    if referenced.contains(&label.id) {
        return false;
    }
    // 候选拒绝[LayerBoundary]：raw TBC/Close 尚未收敛时，这些 label 是 close-scopes
    // owner 的 active-set/epoch 输入；该 owner 消费 cleanup 后会触发下一轮 Deferred
    // dead-labels 再审计（regress_328_dead_label_tbc_barrier）。
    !pending_tbc_boundaries.contains(&label.id)
}

fn collect_label_facts(proto: &HirProto) -> LabelFacts {
    let mut collector = LabelFacts::default();
    visit_proto(proto, &mut collector);
    collector
}

#[derive(Default)]
struct LabelFacts {
    referenced: BTreeSet<HirLabelId>,
}

impl HirVisitor<'_> for LabelFacts {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::Goto(goto_stmt) = stmt {
            self.referenced.insert(goto_stmt.target);
        }
    }
}
