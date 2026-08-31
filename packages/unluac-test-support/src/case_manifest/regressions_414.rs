//! 回归 case 414；合法字符串 constructor key 应收成 record name，非法/关键字/原始字节保持索引。

use super::*;

pub(super) const REGRESSION_CASES_414: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_414_constructor_field_name_sugar.lua",
    &[LuaCaseDialect::Lua54],
)];
