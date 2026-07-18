//! carried-local handoff 的 label/goto 边界索引。
//!
//! 这个模块只把当前 block 内的跳转目标和最近 label 投影成位置索引，供
//! `handoffs.rs` 判断 seed 是否可能被外部路径绕过、回边是否确实返回 handoff label。
//! 它不从边界复制语句推断 binding 等价类；值相等的快照不等于跨时点的状态身份。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirLabelId, HirStmt};

pub(super) struct LabelJumpIndex {
    gotos_by_label: BTreeMap<HirLabelId, Vec<usize>>,
    nearest_prior_labels: Vec<Option<HirLabelId>>,
}

impl LabelJumpIndex {
    pub(super) fn new(stmts: &[HirStmt]) -> Self {
        let mut gotos_by_label = BTreeMap::<HirLabelId, Vec<usize>>::new();
        let mut nearest_prior_labels = Vec::with_capacity(stmts.len());
        let mut nearest_prior_label = None;

        for (index, stmt) in stmts.iter().enumerate() {
            nearest_prior_labels.push(nearest_prior_label);
            for target in goto_targets(stmt) {
                gotos_by_label.entry(target).or_default().push(index);
            }
            if let HirStmt::Label(label) = stmt {
                nearest_prior_label = Some(label.id);
            }
        }

        Self {
            gotos_by_label,
            nearest_prior_labels,
        }
    }

    pub(super) fn next_label_has_prior_goto(&self, stmts: &[HirStmt], index: usize) -> bool {
        let Some(HirStmt::Label(label)) = stmts.get(index + 1) else {
            return false;
        };
        self.has_goto_before(index, label.id)
    }

    pub(super) fn nearest_prior_label(&self, index: usize) -> Option<HirLabelId> {
        self.nearest_prior_labels.get(index).copied().flatten()
    }

    pub(super) fn has_goto_at_or_after(&self, start: usize, target: HirLabelId) -> bool {
        let Some(indices) = self.gotos_by_label.get(&target) else {
            return false;
        };
        let offset = indices.partition_point(|index| *index < start);
        indices.get(offset).is_some()
    }

    fn has_goto_before(&self, end: usize, target: HirLabelId) -> bool {
        self.gotos_by_label
            .get(&target)
            .is_some_and(|indices| indices.first().is_some_and(|index| *index < end))
    }
}

fn goto_targets(stmt: &HirStmt) -> BTreeSet<HirLabelId> {
    let mut targets = BTreeSet::new();
    collect_goto_targets(stmt, &mut targets);
    targets
}

fn collect_goto_targets(stmt: &HirStmt, targets: &mut BTreeSet<HirLabelId>) {
    match stmt {
        HirStmt::Goto(goto) => {
            targets.insert(goto.target);
        }
        HirStmt::If(if_stmt) => {
            collect_block_goto_targets(&if_stmt.then_block, targets);
            if let Some(else_block) = &if_stmt.else_block {
                collect_block_goto_targets(else_block, targets);
            }
        }
        HirStmt::While(while_stmt) => collect_block_goto_targets(&while_stmt.body, targets),
        HirStmt::Repeat(repeat_stmt) => collect_block_goto_targets(&repeat_stmt.body, targets),
        HirStmt::Block(block) => collect_block_goto_targets(block, targets),
        HirStmt::NumericFor(numeric_for) => collect_block_goto_targets(&numeric_for.body, targets),
        HirStmt::GenericFor(generic_for) => collect_block_goto_targets(&generic_for.body, targets),
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

fn collect_block_goto_targets(block: &HirBlock, targets: &mut BTreeSet<HirLabelId>) {
    for stmt in &block.stmts {
        collect_goto_targets(stmt, targets);
    }
}
