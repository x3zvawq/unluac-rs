//! 回归 case 352；覆盖多值 return 尾调用 run 的稳定前缀与可观察顺序边界。

use super::*;

pub(super) const REGRESSION_CASES_352: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_352_multi_return_call_run_accept.lua",
        PUC_LUA_ALL,
    )
    .with_options(LuaCaseOptions {
        // 该 case 锁定首轮 run owner；重编译后的嵌套 callee 会重新展开为另一组 local。
        recompile_rounds: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_352_multi_return_call_run_order.lua",
        PUC_LUA_ALL,
    ),
];
