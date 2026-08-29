//! 回归 case 404；稳定调用语句前缀可承接嵌套 method alias。

use super::*;

pub(super) const REGRESSION_CASES_404: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_404_method_alias_nested_call_stmt.lua",
    &[LuaCaseDialect::Lua54],
)];
