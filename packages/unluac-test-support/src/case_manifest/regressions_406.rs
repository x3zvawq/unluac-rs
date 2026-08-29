//! 回归 case 406；GenericFor 首个 iterator 可原子收回 receiver alias。

use super::*;

pub(super) const REGRESSION_CASES_406: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_406_method_alias_generic_for.lua",
    &[LuaCaseDialect::Lua54],
)];
