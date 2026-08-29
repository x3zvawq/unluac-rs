//! 回归 case 333；覆盖 function-sugar 的 scope/origin guard 与有序表达式放宽。

use super::*;

pub(super) const REGRESSION_CASES_333: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_333_function_sugar_guards.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        retain_debug: true,
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_333_function_sugar_relax.lua",
        PUC_LUA_54,
    ),
    // 该载体必须保留 open-tail SETLIST 才能进入 table-field walker；生成源码的二次编译
    // 会命中尚未支持的 residual SETLIST，因此这里只执行完整首轮语义与 shape 合同。
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_333_function_sugar_table.lua",
        PUC_LUA_54,
    )
    .with_options(NO_RECOMPILE_STRESS_OPTIONS),
];
