//! 回归 case 329；覆盖递归 closure 写回 loop binding 时的 self capture 身份。

use super::*;

pub(super) const REGRESSION_CASES_329: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_329_closure_self_capture.lua",
    PUC_LUA_51,
)];
