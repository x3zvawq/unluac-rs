//! 回归 case 364；覆盖 terminal-else 折叠中的单 goto 备用分支。

use super::*;

const TERMINAL_ELSE_SINGLE_GOTO_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
];

pub(super) const REGRESSION_CASES_364: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_364_terminal_else_single_goto.lua",
    TERMINAL_ELSE_SINGLE_GOTO_DIALECTS,
)];
