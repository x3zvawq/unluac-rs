//! eliminate-decisions pass 的物化状态。
//!
//! 这个模块只保存最终线性化 `Decision` 时需要追加到 proto 的 synthetic local 分配状态。
//! 它不决定哪些表达式需要物化，也不生成语句；这些由 `eliminate.rs` 的遍历入口和
//! `eliminate_materialize.rs` 的物化通道负责。
//!
//! 例子：
//! - 输入形状：`x = Decision(...)`
//! - 输出形状：分配一个新的 local 暂存短路值，并把该 local 追加到 proto locals。

use crate::hir::common::LocalId;

pub(super) struct EliminationState<'a> {
    pub(super) next_local_index: &'a mut usize,
    pub(super) new_locals: &'a mut Vec<LocalId>,
    pub(super) new_local_debug_hints: &'a mut Vec<Option<String>>,
}

impl EliminationState<'_> {
    pub(super) fn alloc_local(&mut self) -> LocalId {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        self.new_locals.push(local);
        self.new_local_debug_hints.push(None);
        local
    }
}
