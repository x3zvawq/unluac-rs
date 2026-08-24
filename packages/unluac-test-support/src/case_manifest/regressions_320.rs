//! 回归 case 320；覆盖 Luau 迭代 proto pipeline 的深层词法链。

use super::*;

pub(super) const REGRESSION_CASES_320: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_320_luau_deep_proto_chain.lua",
    LUAU_ONLY,
)];
