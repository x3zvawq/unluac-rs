//! 回归 case 379；属性 local 合并保留目标语法与关闭注册边界。

use super::*;

pub(super) const REGRESSION_CASES_379: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_379_statement_merge_local_attrs.lua",
    PUC_LUA_GE_54,
)
.with_options(LuaCaseOptions {
    retain_debug: true,
    ..LuaCaseOptions::DEFAULT
})];
