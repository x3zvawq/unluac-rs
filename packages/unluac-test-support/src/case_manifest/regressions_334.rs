//! 回归 case 334；覆盖 close-scope 的同槽位资源 epoch 与关闭求值顺序。

use super::*;

pub(super) const REGRESSION_CASES_334: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_334_close_scope_epochs.lua",
    PUC_LUA_54,
)];
