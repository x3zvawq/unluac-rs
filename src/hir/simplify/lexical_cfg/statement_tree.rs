//! 当前 HIR 快照的独占词法语句树，用于递归改写前一次投影并传递原始子域。
//!
//! 子块顺序复用 HIR 的 `for_each_nested_block`，不进入表达式或 child proto。
//! 每条语句只保存连续先序区间和直属子块 ID，每个 block 只保存直属语句 ID；
//! 回调在语句入口借用原 HIR 收集事件，发布的树不保留 HIR 引用、路径副本或后代集合。
//! ID 只标识这次快照；改写方通过原语句位置和子块位置传递未改写子域，不能拿它查询新树。
//!
//! break/continue 的归属是最近的词法 loop owner，不是 VM 边或运行可达性证明。
//! 例如 `while flag do if stop then break end end` 的完整 while 子树包含该转移的 owner，
//! 而其中 if 子树不包含。break 的实际 successor 在 while 外，不能据此把完整循环
//! 误判为外跳。构建时向上传递最小 owner 排名，并保存各语句的外跳结论和每个 block 的
//! 直属外跳前缀计数；任意连续语句区间直接查询其 owner，不重建循环嵌套关系。
//! label/goto 及其它边界仍由各消费者判定，不把整图的 label 校验错误域带入这里。

use std::ops::Range;

use crate::hir::common::HirStmt;
use crate::hir::visit::for_each_nested_block;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::hir::simplify) struct HirStmtId(usize);

impl HirStmtId {
    pub(in crate::hir::simplify) const fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::hir::simplify) struct HirBlockId(usize);

pub(in crate::hir::simplify) struct HirStmtScope {
    pub(in crate::hir::simplify) range: Range<usize>,
    pub(in crate::hir::simplify) children: Box<[HirBlockId]>,
    pub(in crate::hir::simplify) has_external_loop_transfer: bool,
}

pub(in crate::hir::simplify) struct HirStmtTree {
    stmts: Vec<HirStmtScope>,
    blocks: Vec<HirBlockScope>,
}

#[derive(Default)]
struct HirBlockScope {
    stmts: Box<[HirStmtId]>,
    external_loop_transfer_prefix: Box<[usize]>,
}

impl HirStmtTree {
    pub(in crate::hir::simplify) fn build(
        stmts: &[HirStmt],
        visit: &mut impl FnMut(HirStmtId, &HirStmt),
    ) -> Self {
        let mut tree = Self {
            stmts: Vec::new(),
            blocks: Vec::new(),
        };
        tree.build_block(stmts, None, visit);
        tree
    }

    pub(in crate::hir::simplify) const fn root_block(&self) -> HirBlockId {
        HirBlockId(0)
    }

    pub(in crate::hir::simplify) fn block(&self, id: HirBlockId) -> &[HirStmtId] {
        &self.blocks[id.0].stmts
    }

    pub(in crate::hir::simplify) fn block_loop_transfer_prefix(&self, id: HirBlockId) -> &[usize] {
        &self.blocks[id.0].external_loop_transfer_prefix
    }

    pub(in crate::hir::simplify) fn stmt(&self, id: HirStmtId) -> &HirStmtScope {
        &self.stmts[id.index()]
    }

    fn build_block(
        &mut self,
        stmts: &[HirStmt],
        loop_owner: Option<HirStmtId>,
        visit: &mut impl FnMut(HirStmtId, &HirStmt),
    ) -> (HirBlockId, usize) {
        let id = HirBlockId(self.blocks.len());
        self.blocks.push(HirBlockScope::default());
        let mut direct = Vec::with_capacity(stmts.len());
        let mut external_loop_transfer_prefix = Vec::with_capacity(stmts.len() + 1);
        external_loop_transfer_prefix.push(0);
        let mut minimum_owner = usize::MAX;
        for stmt in stmts {
            let (stmt_id, owner) = self.build_stmt(stmt, loop_owner, visit);
            direct.push(stmt_id);
            external_loop_transfer_prefix.push(
                external_loop_transfer_prefix.last().unwrap()
                    + usize::from(self.stmt(stmt_id).has_external_loop_transfer),
            );
            minimum_owner = minimum_owner.min(owner);
        }
        self.blocks[id.0] = HirBlockScope {
            stmts: direct.into_boxed_slice(),
            external_loop_transfer_prefix: external_loop_transfer_prefix.into_boxed_slice(),
        };
        (id, minimum_owner)
    }

    fn build_stmt(
        &mut self,
        stmt: &HirStmt,
        loop_owner: Option<HirStmtId>,
        visit: &mut impl FnMut(HirStmtId, &HirStmt),
    ) -> (HirStmtId, usize) {
        let id = HirStmtId(self.stmts.len());
        let rank = id.index() + 1;
        self.stmts.push(HirStmtScope {
            range: id.index()..rank,
            children: Box::default(),
            has_external_loop_transfer: false,
        });
        visit(id, stmt);

        // 0 表示没有词法 loop owner，MAX 表示子树没有 break/continue。
        let mut minimum_owner = if matches!(stmt, HirStmt::Break | HirStmt::Continue) {
            loop_owner.map_or(0, |owner| owner.index() + 1)
        } else {
            usize::MAX
        };
        let child_loop_owner = if is_loop(stmt) { Some(id) } else { loop_owner };
        let mut children = Vec::new();
        for_each_nested_block(stmt, &mut |block| {
            let (child, owner) = self.build_block(&block.stmts, child_loop_owner, visit);
            children.push(child);
            minimum_owner = minimum_owner.min(owner);
        });

        let end = self.stmts.len();
        self.stmts[id.index()] = HirStmtScope {
            range: id.index()..end,
            children: children.into_boxed_slice(),
            has_external_loop_transfer: minimum_owner < rank,
        };
        (id, minimum_owner)
    }
}

fn is_loop(stmt: &HirStmt) -> bool {
    matches!(
        stmt,
        HirStmt::While(_) | HirStmt::Repeat(_) | HirStmt::NumericFor(_) | HirStmt::GenericFor(_)
    )
}
