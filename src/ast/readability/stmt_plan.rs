//! 这个文件提供 Readability block 重建时的所有权转移计划。
//!
//! pass 可以先借用完整旧 block 做 lookahead 与 use 分析，只记录需要保留的原语句索引
//! 和已经提交的局部改写；分析结束后再一次性 move 原语句，避免 clone 深层 closure 子树。
//! 这里不判断任何 pass 语义，也不参与 trial/rollback。
//!
//! 例子：`[Original(0), Rewritten(stmt), Original(3)]` 会保留旧语句 0、跳过被改写
//! 覆盖的中间语句，再接上旧语句 3。

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
