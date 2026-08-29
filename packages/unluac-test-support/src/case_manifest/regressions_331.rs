//! 回归 case 331；从 Luau 源码基线动态构造 self-by-value capture 后覆盖真实 target。

use super::*;

pub(super) const REGRESSION_CASES_331: &[LuaCaseMatrixEntry] = &[LuaCaseMatrixEntry::new(
    "tests/regress-case/regress_331_luau_self_value_capture.lua",
    LUAU_ONLY,
)
.with_expectation(LuaCaseExpectation::LuauSelfValueCaptureCarrier {
    closure_pc: 7,
    save_pc: 9,
    overwrite_pc: 10,
    target_reg: 3,
})];
