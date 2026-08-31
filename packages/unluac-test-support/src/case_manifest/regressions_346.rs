//! 回归 case 346；覆盖 parameter alias 穿过 generic-for iterator callback 的路径证明。

use super::*;

pub(super) const REGRESSION_CASES_346: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_346_param_alias_generic_iterator_callback.lua",
    PUC_LUA_54,
)];
