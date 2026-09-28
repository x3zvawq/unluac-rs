//! 当前 HIR 快照的语句路径与改写计划提交器。
//!
//! 消费已证明的删除或端点计划，保持原坐标身份；不重建控制流或生命周期证明。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirStmt};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum PathComponent {
    Stmt(usize),
    Then,
    Else,
    Body,
}

pub(super) type StmtPath = Vec<PathComponent>;

pub(super) fn remove_planned_stmts(
    block: &mut HirBlock,
    path: &mut StmtPath,
    plan: &BTreeSet<StmtPath>,
) {
    retain_stmts_with_paths(block, path, &mut |_, path| !plan.contains(path));
}

/// 后序提交同一快照的语句改写；回调返回 false 才删除当前语句。
/// 回调不能移动、插入或删除其它待提交语句，否则它们的原始坐标将失效。
pub(super) fn retain_stmts_with_paths(
    block: &mut HirBlock,
    path: &mut StmtPath,
    retain: &mut impl FnMut(&mut HirStmt, &StmtPath) -> bool,
) {
    let mut index = 0;
    block.stmts.retain_mut(|stmt| {
        path.push(PathComponent::Stmt(index));
        index += 1;
        let body = match stmt {
            HirStmt::LocalRootRelease(_) => None,
            HirStmt::If(if_stmt) => {
                path.push(PathComponent::Then);
                retain_stmts_with_paths(&mut if_stmt.then_block, path, retain);
                path.pop();
                if let Some(else_block) = &mut if_stmt.else_block {
                    path.push(PathComponent::Else);
                    retain_stmts_with_paths(else_block, path, retain);
                    path.pop();
                }
                None
            }
            HirStmt::While(while_stmt) => Some(&mut while_stmt.body),
            HirStmt::Repeat(repeat_stmt) => Some(&mut repeat_stmt.body),
            HirStmt::NumericFor(for_stmt) => Some(&mut for_stmt.body),
            HirStmt::GenericFor(for_stmt) => Some(&mut for_stmt.body),
            HirStmt::Block(nested) => Some(nested.as_mut()),
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_)
            | HirStmt::Return(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_) => None,
        };
        if let Some(body) = body {
            path.push(PathComponent::Body);
            retain_stmts_with_paths(body, path, retain);
            path.pop();
        }
        let keep = retain(stmt, path);
        path.pop();
        keep
    });
}
