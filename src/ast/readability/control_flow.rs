use std::collections::{BTreeMap, BTreeSet, VecDeque};

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

/// Repeat body 顶层语句 CFG；nested goto/continue 映射到所属顶层 statement。
///
/// 这份图只回答 dominance/must-execute，不尝试恢复 structured statement 内部的逐节点
/// 路径。调用方若把一个 structured statement 当作 handoff owner，仍需单独证明它的每条
/// fallthrough/continue 路径已经完成 handoff。
pub(super) struct RepeatBodyControlFlow {
    successors: Vec<Vec<usize>>,
    exit: usize,
}

impl RepeatBodyControlFlow {
    pub(super) fn new(stmts: &[AstStmt]) -> Option<Self> {
        let exit = stmts.len();
        let mut label_owners = BTreeMap::new();
        for (stmt_index, labels) in stmts.iter().map(collect_labels).enumerate() {
            for label in labels {
                if label_owners.insert(label, stmt_index).is_some() {
                    return None;
                }
            }
        }

        let mut successors = vec![Vec::new(); stmts.len() + 1];
        for (stmt_index, stmt) in stmts.iter().enumerate() {
            for target in collect_goto_targets(stmt) {
                successors[stmt_index].push(*label_owners.get(&target)?);
            }
            if stmt_contains_continue(stmt) {
                successors[stmt_index].push(exit);
            }
            if stmt_may_fall_through(stmt) {
                successors[stmt_index].push(stmt_index + 1);
            }
            successors[stmt_index].sort_unstable();
            successors[stmt_index].dedup();
        }
        Some(Self { successors, exit })
    }

    pub(super) const fn exit(&self) -> usize {
        self.exit
    }

    pub(super) fn dominates(&self, dominator: usize, node: usize) -> bool {
        dominator < self.exit
            && node <= self.exit
            && self.reachable(node, None)
            && !self.reachable(node, Some(dominator))
    }

    fn reachable(&self, target: usize, removed: Option<usize>) -> bool {
        if self.exit == 0 || removed == Some(0) {
            return false;
        }
        let mut seen = vec![false; self.successors.len()];
        let mut pending = VecDeque::from([0]);
        while let Some(node) = pending.pop_front() {
            if Some(node) == removed || seen[node] {
                continue;
            }
            if node == target {
                return true;
            }
            seen[node] = true;
            pending.extend(self.successors[node].iter().copied());
        }
        false
    }
}

fn stmt_contains_continue(stmt: &AstStmt) -> bool {
    struct ContinueVisitor(bool);

    impl AstVisitor for ContinueVisitor {
        fn visit_stmt(&mut self, stmt: &AstStmt) {
            self.0 |= matches!(stmt, AstStmt::Continue);
        }

        fn visit_function_expr(&mut self, _function: &AstFunctionExpr) -> bool {
            false
        }
    }

    let mut visitor = ContinueVisitor(false);
    visit::visit_stmt(stmt, &mut visitor);
    visitor.0
}

fn block_may_fall_through(block: &AstBlock) -> bool {
    if block_contains_label_or_goto(block) {
        // Without an owner-internal CFG, a goto may jump past an apparent terminator and
        // resume at a later label. Keeping the enclosing statement's fallthrough edge is
        // conservative for the top-level dominance proof.
        return true;
    }
    block
        .stmts
        .iter()
        .find(|stmt| !stmt_may_fall_through(stmt))
        .is_none()
}

fn stmt_may_fall_through(stmt: &AstStmt) -> bool {
    match stmt {
        AstStmt::Return(_) | AstStmt::Break | AstStmt::Continue | AstStmt::Goto(_) => false,
        AstStmt::If(if_stmt) => if_stmt.else_block.as_ref().is_none_or(|else_block| {
            block_may_fall_through(&if_stmt.then_block) || block_may_fall_through(else_block)
        }),
        AstStmt::DoBlock(block) => block_may_fall_through(block),
        AstStmt::LocalDecl(_)
        | AstStmt::GlobalDecl(_)
        | AstStmt::Assign(_)
        | AstStmt::CallStmt(_)
        | AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::NumericFor(_)
        | AstStmt::GenericFor(_)
        | AstStmt::Label(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Error(_) => true,
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
