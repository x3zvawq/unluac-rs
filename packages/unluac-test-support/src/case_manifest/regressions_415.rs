//! 回归 case 415；method-chain 中间 binding 作为实参再次使用时不能随 receiver 一起删除。

use super::*;

pub(super) const REGRESSION_CASES_415: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_415_method_chain_receiver_extra_use.lua",
    &[LuaCaseDialect::Lua54],
)];
