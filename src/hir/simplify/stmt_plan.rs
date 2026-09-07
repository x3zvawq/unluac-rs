//! HIR 快照内的语句路径与已证明删除计划共用的提交器。
//!
//! entry-nil 与死布尔壳各自证明哪些写入可删；这里统一解释 `Stmt/Then/Else/Body`
//! 坐标，只执行已经完成的计划，不重新分析控制流、binding 或生命周期。路径必须来自
//! 同一根节点的改写前快照，不能跨 rewrite 当作持久身份；删除计数始终包含原来的槽位。
//! 例如 `[Stmt(2), Then, Stmt(1)]` 删除原第 3 条 if 的 then 第 2 条语句，前面的
//! 同级删除不会改变这个坐标。遍历复用一条路径栈，并在每个 block 内原地压缩一次。

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

/// 临时导航复用同一条路径；先恢复父路径，再交还包括 `Err` 在内的分析结果。
pub(super) fn with_path_component<R>(
    path: &mut StmtPath,
    component: PathComponent,
    visit: impl FnOnce(&mut StmtPath) -> R,
) -> R {
    path.push(component);
    let result = visit(path);
    path.pop();
    result
}

pub(super) fn remove_planned_stmts(
    block: &mut HirBlock,
    path: &mut StmtPath,
    plan: &BTreeSet<StmtPath>,
) {
    let mut index = 0;
    block.stmts.retain_mut(|stmt| {
        path.push(PathComponent::Stmt(index));
        index += 1;
        let body = match stmt {
            HirStmt::LocalRootRelease(_) => None,
            HirStmt::If(if_stmt) => {
                path.push(PathComponent::Then);
                remove_planned_stmts(&mut if_stmt.then_block, path, plan);
                path.pop();
                if let Some(else_block) = &mut if_stmt.else_block {
                    path.push(PathComponent::Else);
                    remove_planned_stmts(else_block, path, plan);
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
            remove_planned_stmts(body, path, plan);
            path.pop();
        }
        let retain = !plan.contains(path);
        path.pop();
        retain
    });
}
