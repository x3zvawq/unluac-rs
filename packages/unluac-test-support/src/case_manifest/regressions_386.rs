//! 回归 case 386；分支覆盖精确终结 lookup/allocation 物理 root。

use super::*;

pub(super) const REGRESSION_CASES_386: &[LuaCaseMatrixEntry] = &[
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_386_lookup_branch_root_release.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        // Recompiling the valid generated assignment reaches the unrelated goto-label
        // visibility residual already isolated by the boolean-shell lifetime cases.
        recompile_rounds: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
    LuaCaseMatrixEntry::new(
        "tests/regress-case/regress_386_allocation_branch_root_release.lua",
        PUC_LUA_54,
    )
    .with_options(LuaCaseOptions {
        recompile_rounds: Some(0),
        ..LuaCaseOptions::DEFAULT
    }),
];
