//! 回归 case 365；覆盖字段构造器折叠与 terminal return binding 解耦。

use super::*;

pub(super) const REGRESSION_CASES_365: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_365_constructor_fields_other_return.lua",
    ALL_NON_LUAU_DIALECTS,
)];
