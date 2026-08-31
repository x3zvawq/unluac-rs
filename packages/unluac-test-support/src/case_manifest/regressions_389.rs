//! 回归 case 389；删除未使用且无事件的 truthiness/vararg 初始化器。

use super::*;

pub(super) const REGRESSION_CASES_389: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_389_discard_safe_truthiness.lua",
    ALL_NON_LUAU_DIALECTS,
)];
