//! 这个文件集中放置 HIR simplify 阶段跨 pass 复用的 local 形状判断。
//!
//! 它只描述局部绑定在 HIR 语句和左值里的机械形态，不负责做 branch-value、
//! temp 提升或布尔壳折叠决策。这样各 pass 可以共享同一套基础判断，同时保留各自的
//! 语义 owner。
//!
//! 例子：
//! - `local l0` → `Some(l0)`
//! - 左值 `l0` 与 binding `l0` → `true`

use crate::hir::common::{HirLValue, HirStmt, LocalId};

pub(super) fn empty_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    local_decl.values.is_empty().then_some(*binding)
}

pub(super) fn initialized_single_local_decl_binding(stmt: &HirStmt) -> Option<LocalId> {
    let HirStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    let [binding] = local_decl.bindings.as_slice() else {
        return None;
    };
    let [_value] = local_decl.values.as_slice() else {
        return None;
    };
    Some(*binding)
}

pub(super) fn matches_local_lvalue(target: &HirLValue, binding: LocalId) -> bool {
    matches!(target, HirLValue::Local(local) if *local == binding)
}
