//! 管理 Decision 线性化的新身份分配与当前 proto 的引用捕获快照。
//! 表达式抽取只引入新结果写入，不改写现存未捕获的 Local/Param。

use super::super::mention::ReferenceCapturedBindings;
use crate::hir::common::{HirExpr, LocalId};
use crate::hir::promotion::ProtoPromotionFacts;

pub(super) struct EliminationState<'a> {
    pub(super) next_local_index: &'a mut usize,
    pub(super) promotion_facts: &'a ProtoPromotionFacts,
    pub(super) reference_captures: &'a ReferenceCapturedBindings,
}

impl EliminationState<'_> {
    /// 表达式前缀只写新 Local 或独立且尚未提升的结果 Temp；原语句的目标另行提交。
    /// 不被引用捕获的可见 binding 也不能被前缀中的 CALL 改写，故无需合成快照。
    pub(super) fn binding_read_is_stable(&self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::LocalRef(local) => !self.reference_captures.locals.contains(local),
            HirExpr::ParamRef(param) => !self.reference_captures.params.contains(param),
            _ => false,
        }
    }

    pub(super) fn alloc_local(&mut self) -> LocalId {
        let local = LocalId(*self.next_local_index);
        *self.next_local_index += 1;
        local
    }
}
