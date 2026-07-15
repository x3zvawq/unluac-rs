//! HIR simplify pass 共享的 label 引用计数。

use std::collections::BTreeMap;

use crate::hir::common::{HirLabelId, HirStmt};

use super::visit::HirVisitor;

pub(super) fn count_label_references(stmts: &[HirStmt]) -> BTreeMap<HirLabelId, usize> {
    let mut collector = LabelReferenceCount::default();
    super::visit::visit_stmts(stmts, &mut collector);
    collector.counts
}

#[derive(Default)]
struct LabelReferenceCount {
    counts: BTreeMap<HirLabelId, usize>,
}

impl HirVisitor for LabelReferenceCount {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        let HirStmt::Goto(goto) = stmt else {
            return;
        };
        *self.counts.entry(goto.target).or_default() += 1;
    }
}
