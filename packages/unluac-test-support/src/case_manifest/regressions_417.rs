//! 回归 case 417；纯 copy root 必须保留到同槽显式覆盖，而不是提前删除或延长到 Return。

use super::*;

pub(super) const REGRESSION_CASES_417: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_417_copy_root_before_overwrite.lua",
    ALL_NON_LUAU_DIALECTS,
)];
