//! 回归 case 378；保留 repeat 尾普通 closure 的可观察生命周期。

use super::*;

pub(super) const REGRESSION_CASES_378: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_378_repeat_tail_closure_lifetime.lua",
    PUC_LUA_GE_52,
)];
