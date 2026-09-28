//! 源码帧事务共用的快照坐标与词法遍历。
//!
//! 统一语句及 repeat 条件位置，供读取、预览和提交消费同一坐标；不证明槽位或生命周期。

use crate::hir::common::{HirBlock, HirStmt};
use crate::hir::simplify::walk::for_each_nested_block_mut;
use crate::hir::visit::for_each_nested_block;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::hir::simplify) enum PointKind {
    Statement,
    RepeatCondition,
    /// 只读扁平视图的路径分隔，不占坐标。
    Boundary,
}

pub(in crate::hir::simplify) fn visit<'a>(
    block: &'a HirBlock,
    cursor: &mut usize,
    action: &mut impl FnMut(usize, PointKind, &'a HirStmt),
) {
    for stmt in &block.stmts {
        let index = *cursor;
        *cursor += 1;
        action(index, PointKind::Statement, stmt);
        if let HirStmt::Repeat(repeat) = stmt {
            visit(&repeat.body, cursor, action);
            let index = *cursor;
            *cursor += 1;
            action(index, PointKind::RepeatCondition, stmt);
            action(*cursor, PointKind::Boundary, stmt);
        } else {
            for_each_nested_block(stmt, &mut |child| {
                visit(child, cursor, action);
                action(*cursor, PointKind::Boundary, stmt);
            });
        }
    }
}

pub(in crate::hir::simplify) fn visit_mut(
    block: &mut HirBlock,
    cursor: &mut usize,
    action: &mut impl FnMut(usize, usize, &mut HirStmt) -> Option<()>,
) -> Option<()> {
    let owner = *cursor;
    for stmt in &mut block.stmts {
        let index = *cursor;
        *cursor += 1;
        if let HirStmt::Repeat(repeat) = stmt {
            // repeat 入口是路径边界，没有可树化的条件；真实条件在 body 末端处理。
            let body_owner = *cursor;
            visit_mut(&mut repeat.body, cursor, action)?;
            let condition = *cursor;
            *cursor += 1;
            action(condition, body_owner, stmt)?;
        } else {
            action(index, owner, stmt)?;
            let mut complete = Some(());
            for_each_nested_block_mut(stmt, &mut |child| {
                if complete.is_some() {
                    complete = visit_mut(child, cursor, action);
                }
            });
            complete?;
        }
    }
    Some(())
}

pub(in crate::hir::simplify) fn compact(
    block: &mut HirBlock,
    removed: &[bool],
    cursor: &mut usize,
) {
    block.stmts.retain_mut(|stmt| {
        let index = *cursor;
        *cursor += 1;
        for_each_nested_block_mut(stmt, &mut |child| compact(child, removed, cursor));
        if matches!(stmt, HirStmt::Repeat(_)) {
            // condition 点只能替换表达式；不能用删除位删除 loop 或跳过末端条件。
            assert!(!removed[index] && !removed[*cursor]);
            *cursor += 1;
        }
        !removed[index]
    });
}

/// 各词法 owner 的排他末端；repeat 条件仍属于 body，须包含其额外坐标。
pub(in crate::hir::simplify) fn owner_ends(block: &HirBlock, count: usize) -> Vec<usize> {
    fn scan(block: &HirBlock, cursor: &mut usize, ends: &mut [usize]) {
        let owner = *cursor;
        for stmt in &block.stmts {
            *cursor += 1;
            if let HirStmt::Repeat(repeat) = stmt {
                let body_owner = *cursor;
                scan(&repeat.body, cursor, ends);
                *cursor += 1;
                ends[body_owner] = *cursor;
            } else {
                for_each_nested_block(stmt, &mut |child| scan(child, cursor, ends));
            }
        }
        if owner < ends.len() {
            ends[owner] = *cursor;
        }
    }
    let mut ends = vec![0; count];
    scan(block, &mut 0, &mut ends);
    ends
}
