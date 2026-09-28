//! Readability block 重建的所有权转移计划。
//!
//! 记录已确定的原语句保留与局部改写，统一移交输出；语义证明由 pass 持有。

use super::super::common::AstStmt;

pub(super) enum PlannedStmt {
    Original(usize),
    Rewritten(AstStmt),
}

pub(super) fn materialize_stmt_plan(
    old_stmts: Vec<AstStmt>,
    stmt_plan: Vec<PlannedStmt>,
) -> Vec<AstStmt> {
    let mut originals = old_stmts.into_iter().enumerate();
    let mut new_stmts = Vec::with_capacity(stmt_plan.len());

    for planned in stmt_plan {
        match planned {
            PlannedStmt::Original(target) => loop {
                let (index, stmt) = originals
                    .next()
                    .expect("statement plan must reference an existing statement");
                assert!(index <= target, "statement plan must preserve source order");
                if index == target {
                    new_stmts.push(stmt);
                    break;
                }
            },
            PlannedStmt::Rewritten(stmt) => new_stmts.push(stmt),
        }
    }

    new_stmts
}
