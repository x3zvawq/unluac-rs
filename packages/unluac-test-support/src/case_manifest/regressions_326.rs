//! 回归 case 326；覆盖带 debug identity 的相邻 dynamic fixed SETLIST 构造器恢复。

use super::*;

pub(super) const REGRESSION_CASES_326: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_326_adjacent_uncertain_setlist.lua",
    ALL_DIALECTS,
)
.with_options(LuaCaseOptions {
    retain_debug: true,
    ..LuaCaseOptions::DEFAULT
})];
