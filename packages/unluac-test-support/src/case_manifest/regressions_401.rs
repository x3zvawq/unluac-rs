//! 回归 case 401；function sugar 不得改变转发求值顺序或最终实参值宽度。

use super::*;

pub(super) const REGRESSION_CASES_401: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_401_forwarded_lvalue_eval_order.lua",
        &[LuaCaseDialect::Lua54],
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_401_constructor_value_arity.lua",
        &[LuaCaseDialect::Lua54],
    ),
];
