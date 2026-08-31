//! 回归 case 412；method chain 不得缩短 call result 跨 opaque callback 的 root 生命周期。

use super::*;

pub(super) const REGRESSION_CASES_412: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_412_method_chain_callback_root.lua",
    &[LuaCaseDialect::Lua54],
)];
