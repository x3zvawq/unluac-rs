//! 回归 case 348；覆盖 call-root 同槽二元覆盖的 direct-binding RHS。

use super::*;

pub(super) const REGRESSION_CASES_348: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_348_call_root_binary_binding_rhs.lua",
    PUC_LUA_54,
)];
