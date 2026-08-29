//! 回归 case 362；覆盖 constructor-call 折叠后仍被字段闭包捕获的参数 binding。

use super::*;

pub(super) const REGRESSION_CASES_362: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_362_constructor_call_capture.lua",
    ALL_NON_LUAU_DIALECTS,
)];
