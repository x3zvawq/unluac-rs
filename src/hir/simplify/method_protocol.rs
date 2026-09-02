//! 提供 HIR method-setup lookup/call occurrence 的共享协议匹配。
//!
//! 本模块只验证同一 low/SSA protocol 在最终 HIR 的双端形状仍完整，不判断 root 生命周期、
//! binding 删除、capture 或目标 Lua 语法；这些条件分别由各自 transaction owner 证明。

use crate::hir::common::{
    HirCallExpr, HirCallRootHandoff, HirExpr, HirMethodSetupProtocolId, HirTableAccess,
};

pub(super) fn match_method_setup_pair(
    access: &HirTableAccess,
    expected_callee: &HirExpr,
    call: &HirCallExpr,
) -> Option<HirMethodSetupProtocolId> {
    let HirExpr::String(method_key) = &access.key else {
        return None;
    };
    let protocol = access.method_setup_protocol?;
    let Some(HirCallRootHandoff::MethodCallee(call_protocol)) = call.callee_root_handoff else {
        return None;
    };
    (call_protocol == protocol
        && call.method
        && call.method_key.as_ref() == Some(method_key)
        && &call.callee == expected_callee
        && call.args.first() == Some(&access.base))
    .then_some(protocol)
}
