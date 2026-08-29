//! 回归 case 398；稳定参数复制仍须释放目标槽旧 root。

use super::*;

pub(super) const REGRESSION_CASES_398: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_398_dead_temp_stable_param_old_root.lua",
    &[LuaCaseDialect::Lua54],
)];
