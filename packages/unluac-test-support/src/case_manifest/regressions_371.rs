//! 回归 case 371；覆盖 repeat prefix 中已结束词法 block 的资源 owner。

use super::*;

pub(super) const REGRESSION_CASES_371: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_371_repeat_closed_block_resource.lua",
    PUC_LUA_GE_54,
)];
