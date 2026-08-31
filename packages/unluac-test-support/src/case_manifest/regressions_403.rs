//! 回归 case 403；constructor-call 可跨无事件字面量折叠并保持参数位置。

use super::*;

pub(super) const REGRESSION_CASES_403: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_403_constructor_literal_args.lua",
    &[LuaCaseDialect::Lua54],
)];
