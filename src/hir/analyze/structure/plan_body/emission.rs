//! 在私有 plan lowering 结果中传递已证明的词法边界，拼接完成后才物化 HIR block。
//!
//! scope 身份来自 bindings.lexical_scopes 的索引；位置由 low 指令实际发射点记录，
//! 不从 HIR 表达式、寄存器名称或节点地址重建。比如 `local t={}; if p then ... end;
//! use(t); scope-end` 的开始和结束可以由不同 region 发射，再由共同 Sequence 包成 do。
//! 这里只保持语句与边界顺序，不证明跨控制流窗口是否合法；嵌入分支、循环等独立
//! 语法块前，调用方必须完成相应拼接并通过 finish 检查所有边界已经闭合。

use std::collections::BTreeSet;

use crate::hir::common::{HirBlock, HirStmt};

#[derive(Default)]
pub(super) struct PlannedBlock {
    stmts: Vec<HirStmt>,
    boundaries: Vec<ScopeBoundary>,
}

struct ScopeBoundary {
    position: usize,
    scope: usize,
    kind: BoundaryKind,
}

enum BoundaryKind {
    Start,
    End,
}

impl PlannedBlock {
    pub(super) fn new() -> Self {
        Self::default()
    }

    pub(super) fn len(&self) -> usize {
        self.stmts.len()
    }

    pub(super) fn last(&self) -> Option<&HirStmt> {
        self.stmts.last()
    }

    /// 将末尾求值接到紧随其后的条件时，不能跨过词法边界；其余位置和事件保持原样。
    pub(super) fn pop_trailing_without_scope_boundary(&mut self) -> Option<HirStmt> {
        let position = self.stmts.len().checked_sub(1)?;
        if self
            .boundaries
            .last()
            .is_some_and(|event| event.position >= position)
        {
            return None;
        }
        self.stmts.pop()
    }

    /// 只允许原位标注语句，不暴露改变长度而使边界位置失效的 Vec。
    pub(super) fn stmts_mut(&mut self) -> &mut [HirStmt] {
        &mut self.stmts
    }

    pub(super) fn split_off(&mut self, at: usize) -> Self {
        let mut boundary = self.boundaries.partition_point(|event| event.position < at);
        // gap 前刚闭合的 scope 属于左侧；同 gap 新开始的（含空 scope）留给右侧。
        while self
            .boundaries
            .get(boundary)
            .is_some_and(|event| event.position == at && matches!(event.kind, BoundaryKind::End))
        {
            boundary += 1;
        }
        let mut boundaries = self.boundaries.split_off(boundary);
        for event in &mut boundaries {
            event.position -= at;
        }
        Self {
            stmts: self.stmts.split_off(at),
            boundaries,
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.stmts.is_empty() && self.boundaries.is_empty()
    }

    pub(super) fn push(&mut self, stmt: HirStmt) {
        self.stmts.push(stmt);
    }

    pub(super) fn extend_plain(&mut self, stmts: impl IntoIterator<Item = HirStmt>) {
        self.stmts.extend(stmts);
    }

    pub(super) fn append(&mut self, mut other: Self) {
        let offset = self.stmts.len();
        self.stmts.append(&mut other.stmts);
        self.boundaries
            .extend(other.boundaries.into_iter().map(|mut boundary| {
                boundary.position += offset;
                boundary
            }));
    }

    pub(super) fn start_scope(&mut self, scope: usize) {
        self.boundaries.push(ScopeBoundary {
            position: self.stmts.len(),
            scope,
            kind: BoundaryKind::Start,
        });
    }

    pub(super) fn end_scope(&mut self, scope: usize) {
        self.boundaries.push(ScopeBoundary {
            position: self.stmts.len(),
            scope,
            kind: BoundaryKind::End,
        });
    }

    pub(super) fn finish(self) -> Result<HirBlock, &'static str> {
        if self.boundaries.is_empty() {
            return Ok(HirBlock { stmts: self.stmts });
        }

        let mut input = self.stmts.into_iter();
        let mut position = 0;
        let mut stmts = Vec::new();
        let mut stack = Vec::new();
        let mut started = BTreeSet::new();
        // append 只偏移位置，保持同一语句间隙内的事件先后；不按 scope ID 重新排序。
        for boundary in self.boundaries {
            stmts.extend(input.by_ref().take(boundary.position - position));
            position = boundary.position;
            match boundary.kind {
                BoundaryKind::Start => {
                    if !started.insert(boundary.scope) {
                        return Err("lexical scope is started more than once");
                    }
                    stack.push((boundary.scope, std::mem::take(&mut stmts)));
                }
                BoundaryKind::End => {
                    let Some((scope, mut parent)) = stack.pop() else {
                        return Err("lexical scope end has no matching start");
                    };
                    if scope != boundary.scope {
                        return Err("lexical scope end crosses another scope");
                    }
                    parent.push(HirStmt::Block(Box::new(HirBlock { stmts })));
                    stmts = parent;
                }
            }
        }
        if !stack.is_empty() {
            return Err("lexical scope start has no matching end");
        }
        stmts.extend(input);
        Ok(HirBlock { stmts })
    }
}

impl From<HirBlock> for PlannedBlock {
    fn from(block: HirBlock) -> Self {
        block.stmts.into()
    }
}

impl From<Vec<HirStmt>> for PlannedBlock {
    fn from(stmts: Vec<HirStmt>) -> Self {
        Self {
            stmts,
            boundaries: Vec::new(),
        }
    }
}
