//! 回归 case 400；跨 home 的调用结果副本必须独立保留物理 root 生命周期。

use super::*;

pub(super) const REGRESSION_CASES_400: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_400_call_copy_only_root.lua",
    &[LuaCaseDialect::Lua54],
)];
