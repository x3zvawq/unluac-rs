//! 回归 case 367；覆盖 repeat 条件折叠对嵌套 loop 资源 owner 的区分。

use super::*;

pub(super) const REGRESSION_CASES_367: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_367_repeat_nested_close_owner.lua",
    PUC_LUA_GE_54,
)];
