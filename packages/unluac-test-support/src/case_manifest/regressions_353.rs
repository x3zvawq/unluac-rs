//! 回归 case 353；覆盖 extended call run 的非尾返回值与 index 位置证明。

use super::*;

pub(super) const REGRESSION_CASES_353: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_return_call_run.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_return_call_run_order.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_return_method_run.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_return_field_run.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_return_field_order.lua",
        PUC_LUA_ALL,
    ),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_353_extended_index_key_lifetime.lua",
        PUC_LUA_ALL,
    ),
];
