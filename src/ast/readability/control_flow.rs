use std::collections::BTreeSet;

use super::super::common::{AstBlock, AstFunctionExpr, AstLabelId, AstStmt};
use super::visit::{self, AstVisitor};

struct LabelOrGotoVisitor(bool);

impl AstVisitor for LabelOrGotoVisitor {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        self.0 |= matches!(stmt, AstStmt::Label(_) | AstStmt::Goto(_));
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

pub(super) fn block_contains_label_or_goto(block: &AstBlock) -> bool {
    let mut visitor = LabelOrGotoVisitor(false);
    visit::visit_block(block, &mut visitor);
    visitor.0
}

pub(super) fn stmt_contains_label_or_goto(stmt: &AstStmt) -> bool {
    let mut visitor = LabelOrGotoVisitor(false);
    visit::visit_stmt(stmt, &mut visitor);
    visitor.0
}

pub(super) struct BlockGotoIndex {
    goto_targets_by_stmt: Vec<BTreeSet<AstLabelId>>,
    labels_by_stmt: Vec<BTreeSet<AstLabelId>>,
}

impl BlockGotoIndex {
    pub(super) fn new(stmts: &[AstStmt]) -> Self {
        Self {
            goto_targets_by_stmt: stmts.iter().map(collect_goto_targets).collect(),
            labels_by_stmt: stmts.iter().map(collect_labels).collect(),
        }
    }

    pub(super) fn has_external_entry(&self, start: usize, end: usize) -> bool {
        let nested_labels = self.labels_by_stmt[start..end]
            .iter()
            .flatten()
            .copied()
            .collect::<BTreeSet<_>>();
        if nested_labels.is_empty() {
            return false;
        }
        self.goto_targets_by_stmt[..start]
            .iter()
            .chain(&self.goto_targets_by_stmt[end..])
            .flatten()
            .any(|target| nested_labels.contains(target))
    }
}

#[derive(Default)]
struct GotoLabelCollector {
    goto_targets: BTreeSet<AstLabelId>,
    labels: BTreeSet<AstLabelId>,
}

impl AstVisitor for GotoLabelCollector {
    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::Goto(goto_stmt) => {
                self.goto_targets.insert(goto_stmt.target);
            }
            AstStmt::Label(label) => {
                self.labels.insert(label.id);
            }
            _ => {}
        }
    }

    fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
        false
    }
}

fn collect_goto_targets(stmt: &AstStmt) -> BTreeSet<AstLabelId> {
    let mut collector = GotoLabelCollector::default();
    visit::visit_stmt(stmt, &mut collector);
    collector.goto_targets
}

fn collect_labels(stmt: &AstStmt) -> BTreeSet<AstLabelId> {
    let mut collector = GotoLabelCollector::default();
    visit::visit_stmt(stmt, &mut collector);
    collector.labels
}
