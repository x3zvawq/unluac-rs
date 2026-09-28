//! HIR simplify 跨 pass 共用的 local 形状查询。
//!
//! 将当前声明、赋值和左值投影为绑定及固定单值信息；候选接受证明由消费者负责。

use crate::hir::common::{HirExpr, HirStmt, LocalId};

pub(super) fn empty_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

pub(super) fn initialized_single_local_decl(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    if local_decl.values.tail.is_some() {
        return None;
    }
    Some((*binding, value))
}
