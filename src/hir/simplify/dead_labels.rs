//! 清理无 goto 引用或处于同一词法位置的机械标签。
//!
//! 消费当前跳转引用与资源事实，保持控制和作用域结构。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirLabel, HirLabelId, HirProto, HirStmt};

use super::close_scopes::pending_tbc_boundary_labels_in_proto;
use super::walk::{HirRewritePass, rewrite_proto};
use crate::hir::visit::{HirVisitor, visit_proto};

pub(super) fn remove_unused_labels_in_proto(proto: &mut HirProto) -> bool {
    let pending_tbc_boundaries = pending_tbc_boundary_labels_in_proto(proto);
    let facts = collect_label_facts(proto, &pending_tbc_boundaries);
    let mut pass = DeadLabelPass {
        referenced: &facts.referenced,
        aliases: &facts.aliases,
        pending_tbc_boundaries: &pending_tbc_boundaries,
    };
    rewrite_proto(proto, &mut pass)
}

struct DeadLabelPass<'a> {
    referenced: &'a BTreeSet<HirLabelId>,
    aliases: &'a BTreeMap<HirLabelId, HirLabelId>,
    pending_tbc_boundaries: &'a BTreeSet<HirLabelId>,
}

impl HirRewritePass for DeadLabelPass<'_> {
    fn rewrite_stmt(&mut self, stmt: &mut HirStmt) -> bool {
        if let HirStmt::Goto(goto) = stmt
            && let Some(&target) = self.aliases.get(&goto.target)
        {
            goto.target = target;
            return true;
        }
        false
    }

    fn rewrite_block(&mut self, block: &mut crate::hir::common::HirBlock) -> bool {
        let original_len = block.stmts.len();
        block.stmts.retain(|stmt| {
            !matches!(stmt, HirStmt::Label(label) if self.aliases.contains_key(&label.id) || label_is_removable(
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

fn collect_label_facts<'a>(
    proto: &HirProto,
    pending_tbc_boundaries: &'a BTreeSet<HirLabelId>,
) -> LabelFacts<'a> {
    let mut collector = LabelFacts {
        referenced: BTreeSet::new(),
        aliases: BTreeMap::new(),
        pending_tbc_boundaries,
    };
    visit_proto(proto, &mut collector);
    collector.referenced = collector
        .referenced
        .into_iter()
        .map(|label| collector.aliases.get(&label).copied().unwrap_or(label))
        .collect();
    collector
}

struct LabelFacts<'a> {
    referenced: BTreeSet<HirLabelId>,
    aliases: BTreeMap<HirLabelId, HirLabelId>,
    pending_tbc_boundaries: &'a BTreeSet<HirLabelId>,
}

impl HirVisitor<'_> for LabelFacts<'_> {
    fn visit_block(&mut self, block: &crate::hir::common::HirBlock) {
        let mut anchor = None;
        for stmt in &block.stmts {
            let HirStmt::Label(label) = stmt else {
                anchor = None;
                continue;
            };
            if self.pending_tbc_boundaries.contains(&label.id) {
                // 候选拒绝[LayerBoundary]：未消费的 TBC epoch 仍靠 label 区分活跃域
                // 和 cleanup 入口，不能以文本相邻替代 close-scopes 的边界证明。
                anchor = None;
            } else if let Some(target) = anchor {
                // 候选接受：同一 block 内没有跨越声明、操作或 scope 边界，且两端
                // 已不承担 raw cleanup；所有 goto 原子改指同一入口，词法退出路径不变。
                self.aliases.insert(label.id, target);
            } else {
                anchor = Some(label.id);
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::Goto(goto_stmt) = stmt {
            self.referenced.insert(goto_stmt.target);
        }
    }
}
