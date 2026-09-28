//! 为当前 HIR 快照发布共享词法语句树与控制 owner 查询。
//!
//! 消费语句子块结构，不进入表达式或 child proto；语句身份只对对应的未改写子域有效。

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
