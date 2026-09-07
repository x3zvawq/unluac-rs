//! HIR simplify pass 共享的 label/goto 存在性查询、引用计数与顶层 owner 投影。
//!
//! 嵌套控制块的 label/goto 保留其顶层语句位置，跨语句查询消费共享词法引用索引；
//! 例如 if 内的 goto 属于整个 if 的 owner，不按运行可达性裁剪源码作用域入边。

use std::collections::BTreeMap;

use crate::hir::common::{HirLabelId, HirStmt};

use crate::hir::visit::{any_stmt_structure, visit_stmt_structure};

pub(super) fn stmt_has_label_or_goto(stmt: &HirStmt) -> bool {
    any_stmt_structure(stmt, &mut |stmt| {
        matches!(stmt, HirStmt::Goto(_) | HirStmt::Label(_))
    })
}

pub(super) fn label_references_by_stmt(
    stmts: &[HirStmt],
) -> Vec<crate::graph::LabelReferences<HirLabelId>> {
    stmts
        .iter()
        .map(|stmt| {
            let mut refs = crate::graph::LabelReferences::default();
            visit_stmt_structure(stmt, &mut |stmt| match stmt {
                HirStmt::Label(label) => {
                    refs.labels.insert(label.id);
                }
                HirStmt::Goto(goto) => {
                    refs.goto_targets.insert(goto.target);
                }
                _ => {}
            });
            refs
        })
        .collect()
}

pub(super) fn count_label_references(stmts: &[HirStmt]) -> BTreeMap<HirLabelId, usize> {
    let mut counts = BTreeMap::new();
    for stmt in stmts {
        visit_stmt_structure(stmt, &mut |stmt| {
            if let HirStmt::Goto(goto) = stmt {
                *counts.entry(goto.target).or_default() += 1;
            }
        });
    }
    counts
}
