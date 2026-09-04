//! carried-local handoff 的 label/goto 边界索引。
//!
//! 这个模块只把当前 block 内的跳转目标和最近 label 投影成位置索引，供
//! `handoffs.rs` 判断 seed 是否可能被外部路径绕过、回边是否确实返回 handoff label。
//! 它不从边界复制语句推断 binding 等价类；值相等的快照不等于跨时点的状态身份。

use super::super::label_refs::label_references_by_stmt;
use crate::graph::LabelReferenceIndex;

use crate::hir::common::{HirLabelId, HirStmt};

pub(super) struct LabelJumpIndex {
    references: LabelReferenceIndex<HirLabelId>,
    nearest_prior_labels: Vec<Option<HirLabelId>>,
}

impl LabelJumpIndex {
    pub(super) fn new(stmts: &[HirStmt]) -> Self {
        let references = LabelReferenceIndex::new(&label_references_by_stmt(stmts));
        let mut nearest_prior_labels = Vec::with_capacity(stmts.len());
        let mut nearest_prior_label = None;

        for stmt in stmts {
            nearest_prior_labels.push(nearest_prior_label);
            if let HirStmt::Label(label) = stmt {
                nearest_prior_label = Some(label.id);
            }
        }

        Self {
            references,
            nearest_prior_labels,
        }
    }

    pub(super) fn next_label_has_prior_goto(&self, stmts: &[HirStmt], index: usize) -> bool {
        let Some(HirStmt::Label(label)) = stmts.get(index + 1) else {
            return false;
        };
        self.references.has_goto_before(index, label.id)
    }

    pub(super) fn suffix_has_prior_goto(&self, index: usize) -> bool {
        let end = self.nearest_prior_labels.len();
        self.references
            .has_incoming_outside(index + 1..end, index..end)
    }

    pub(super) fn nearest_prior_label(&self, index: usize) -> Option<HirLabelId> {
        self.nearest_prior_labels.get(index).copied().flatten()
    }

    pub(super) fn has_goto_at_or_after(&self, start: usize, target: HirLabelId) -> bool {
        self.references.has_goto_at_or_after(start, target)
    }
}
