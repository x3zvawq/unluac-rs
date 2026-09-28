//! 管理 Decision 线性化所需的 synthetic local 分配状态。
//!
//! 向物化通道提供新身份；候选选择和语句构造由调用方负责。

use crate::hir::common::LocalId;

pub(super) struct EliminationState<'a> {
    pub(super) next_local_index: &'a mut usize,
}

impl EliminationState<'_> {
    pub(super) fn alloc_local(&mut self) -> LocalId {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        local
    }
}
