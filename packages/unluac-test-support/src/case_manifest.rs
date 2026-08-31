//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 真正的事实源是“一个 case 属于哪类测试、支持哪些 dialect”。
//! 目录负责区分 `unit` / `regression`，矩阵只负责展开具体 `(case, dialect)` 测试单元，
//! 这样后续给 common case 显式挂多个 dialect 时，不需要回到“每行一个组合”的散乱写法。

use strum_macros::{Display, IntoStaticStr};
use unluac::ast::NamingMode;
use unluac::decompile::DecompileDialect;

mod regressions_001_100;
mod regressions_101_200;
mod regressions_201_318;
mod regressions_319;
mod regressions_320;
mod regressions_321;
mod regressions_322;
mod regressions_323;
mod regressions_324;
mod regressions_325;
mod regressions_326;
mod regressions_327;
mod regressions_328;
mod regressions_329;
mod regressions_330;
mod regressions_331;
mod regressions_332;
mod regressions_333;
mod regressions_334;
mod regressions_335;
mod regressions_336;
mod regressions_337;
mod regressions_338;
mod regressions_339;
mod regressions_340;
mod regressions_341;
mod unit_cases;

use regressions_001_100::REGRESSION_CASES_001_100;
use regressions_101_200::REGRESSION_CASES_101_200;
use regressions_201_318::REGRESSION_CASES_201_318;
use regressions_319::REGRESSION_CASES_319;
use regressions_320::REGRESSION_CASES_320;
use regressions_321::REGRESSION_CASES_321;
use regressions_322::REGRESSION_CASES_322;
use regressions_323::REGRESSION_CASES_323;
use regressions_324::REGRESSION_CASES_324;
use regressions_325::REGRESSION_CASES_325;
use regressions_326::REGRESSION_CASES_326;
use regressions_327::REGRESSION_CASES_327;
use regressions_328::REGRESSION_CASES_328;
use regressions_329::REGRESSION_CASES_329;
use regressions_330::REGRESSION_CASES_330;
use regressions_331::REGRESSION_CASES_331;
use regressions_332::REGRESSION_CASES_332;
use regressions_333::REGRESSION_CASES_333;
use regressions_334::REGRESSION_CASES_334;
use regressions_335::REGRESSION_CASES_335;
use regressions_336::REGRESSION_CASES_336;
use regressions_337::REGRESSION_CASES_337;
use regressions_338::REGRESSION_CASES_338;
use regressions_339::REGRESSION_CASES_339;
use regressions_340::REGRESSION_CASES_340;
use regressions_341::REGRESSION_CASES_341;
use unit_cases::UNIT_CASES;

#[derive(Debug, Clone, Copy, Eq, PartialEq, Display, IntoStaticStr)]
pub enum LuaCaseDialect {
    #[strum(serialize = "lua5.1")]
    Lua51,
    #[strum(serialize = "lua5.2")]
    Lua52,
    #[strum(serialize = "lua5.3")]
    Lua53,
    #[strum(serialize = "lua5.4")]
    Lua54,
    #[strum(serialize = "lua5.5")]
    Lua55,
    #[strum(serialize = "luajit")]
    Luajit,
    #[strum(serialize = "luau")]
    Luau,
}

impl LuaCaseDialect {
    pub(crate) const fn decompile_dialect(self) -> DecompileDialect {
        match self {
            Self::Lua51 => DecompileDialect::Lua51,
            Self::Lua52 => DecompileDialect::Lua52,
            Self::Lua53 => DecompileDialect::Lua53,
            Self::Lua54 => DecompileDialect::Lua54,
            Self::Lua55 => DecompileDialect::Lua55,
            Self::Luajit => DecompileDialect::Luajit,
            Self::Luau => DecompileDialect::Luau,
        }
    }
}

/// 矩阵里的单个 case 定义。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseMatrixEntry {
    pub(crate) path: &'static str,
    pub(crate) dialects: &'static [LuaCaseDialect],
    pub(crate) options: LuaCaseOptions,
    pub(crate) variants: &'static [LuaCaseVariant],
    pub(crate) expectation: LuaCaseExpectation,
    pub(crate) structure_contracts: &'static [LuaCaseStructureContract],
}

impl LuaCaseMatrixEntry {
    const fn new(path: &'static str, dialects: &'static [LuaCaseDialect]) -> Self {
        Self {
            path,
            dialects,
            options: LuaCaseOptions::DEFAULT,
            variants: &[],
            expectation: LuaCaseExpectation::Source,
            structure_contracts: &[],
        }
    }

    const fn with_options(mut self, options: LuaCaseOptions) -> Self {
        self.options = options;
        self
    }

    const fn with_variants(mut self, variants: &'static [LuaCaseVariant]) -> Self {
        self.variants = variants;
        self
    }

    const fn with_expectation(mut self, expectation: LuaCaseExpectation) -> Self {
        self.expectation = expectation;
        self
    }

    const fn with_structure_contracts(
        mut self,
        structure_contracts: &'static [LuaCaseStructureContract],
    ) -> Self {
        self.structure_contracts = structure_contracts;
        self
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum LuaCaseExpectation {
    Source,
    TableSetListResidual,
    InvalidDebugStillRejected,
    LuaJitBuiltinTableRemove,
    LuaJitMethodProtocol,
    ProtoFailureRecovery,
    UnsupportedIsland {
        jump_pc: usize,
        target_pc: usize,
    },
    LuauSelfValueCaptureCarrier {
        closure_pc: usize,
        save_pc: usize,
        overwrite_pc: usize,
        target_reg: u8,
    },
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum LuaCaseStructureContract {
    MixedUnstructuredChildLoop {
        dialect: LuaCaseDialect,
        protocol: LuaCaseLoopProtocol,
    },
}

impl LuaCaseStructureContract {
    pub(crate) const fn dialect(self) -> LuaCaseDialect {
        match self {
            Self::MixedUnstructuredChildLoop { dialect, .. } => dialect,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) enum LuaCaseLoopProtocol {
    NumericFor,
    GenericFor,
}

/// 单个源码 case 需要的宿主编译与反编译选项。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub(crate) struct LuaCaseOptions {
    pub(crate) retain_debug: bool,
    pub(crate) ignore_debug: bool,
    pub(crate) naming_mode: Option<NamingMode>,
    pub(crate) luau_optimization_level: Option<u8>,
    pub(crate) luau_vector: Option<LuauVectorCaseOptions>,
    pub(crate) recompile_rounds: Option<u32>,
}

impl LuaCaseOptions {
    const DEFAULT: Self = Self {
        retain_debug: false,
        ignore_debug: false,
        naming_mode: None,
        luau_optimization_level: None,
        luau_vector: None,
        recompile_rounds: None,
    };
}

/// Luau 编译器和反编译器共同使用的 vector 宿主身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuauVectorCaseOptions {
    pub(crate) library: Option<&'static str>,
    pub(crate) constructor: &'static str,
    pub(crate) components: u8,
}

/// 展开后的 `(case, dialect)` 测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub variant: Option<LuaCaseVariant>,
    pub(crate) options: LuaCaseOptions,
    pub(crate) expectation: LuaCaseExpectation,
    pub(crate) structure_contracts: &'static [LuaCaseStructureContract],
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuaCaseVariant {
    LuauO0,
    LuauO1,
    LuauO2,
    NamingDebugLike,
    NamingSimple,
    NamingHeuristic,
}

impl LuaCaseVariant {
    pub const fn label(self) -> &'static str {
        match self {
            Self::LuauO0 => "O0",
            Self::LuauO1 => "O1",
            Self::LuauO2 => "O2",
            Self::NamingDebugLike => "naming-debug-like",
            Self::NamingSimple => "naming-simple",
            Self::NamingHeuristic => "naming-heuristic",
        }
    }

    const fn apply(self, options: &mut LuaCaseOptions) {
        match self {
            Self::LuauO0 => options.luau_optimization_level = Some(0),
            Self::LuauO1 => options.luau_optimization_level = Some(1),
            Self::LuauO2 => options.luau_optimization_level = Some(2),
            Self::NamingDebugLike => options.naming_mode = Some(NamingMode::DebugLike),
            Self::NamingSimple => options.naming_mode = Some(NamingMode::Simple),
            Self::NamingHeuristic => options.naming_mode = Some(NamingMode::Heuristic),
        }
    }
}

const ALL_NAMING_VARIANTS: &[LuaCaseVariant] = &[
    LuaCaseVariant::NamingDebugLike,
    LuaCaseVariant::NamingSimple,
    LuaCaseVariant::NamingHeuristic,
];

const ALL_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
    LuaCaseDialect::Luau,
];
const ALL_NON_LUAU_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
];
const MUTABLE_NUMERIC_FOR_BINDING_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Luajit,
    LuaCaseDialect::Luau,
];
const PUC_LUA_ALL: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua51,
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const PUC_LUA_51: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51];
const LUA_51_AND_LUAU: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51, LuaCaseDialect::Luau];
const LUA_51_AND_LUAJIT: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51, LuaCaseDialect::Luajit];
const PUC_LUA_52: &[LuaCaseDialect] = &[LuaCaseDialect::Lua52];
const PUC_LUA_54: &[LuaCaseDialect] = &[LuaCaseDialect::Lua54];
const PUC_LUA_GE_52: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const LUA_GOTO_DIALECTS: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
    LuaCaseDialect::Luajit,
];
const PUC_LUA_GE_53: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
];
const PUC_LUA_GE_54: &[LuaCaseDialect] = &[LuaCaseDialect::Lua54, LuaCaseDialect::Lua55];
const PUC_LUA_GE_55: &[LuaCaseDialect] = &[LuaCaseDialect::Lua55];
const LUAU_ONLY: &[LuaCaseDialect] = &[LuaCaseDialect::Luau];
const LUAJIT_ONLY: &[LuaCaseDialect] = &[LuaCaseDialect::Luajit];
const LUAU_O0_ONLY: &[LuaCaseVariant] = &[LuaCaseVariant::LuauO0];
const LUAU_ALL_OPTIMIZATION_VARIANTS: &[LuaCaseVariant] = &[
    LuaCaseVariant::LuauO0,
    LuaCaseVariant::LuauO1,
    LuaCaseVariant::LuauO2,
];
const LUAU_OPTIMIZED_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    retain_debug: false,
    ignore_debug: false,
    naming_mode: None,
    luau_optimization_level: Some(2),
    luau_vector: None,
    recompile_rounds: None,
};
const LUAU_OPTIMIZED_CONVERGENCE_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    recompile_rounds: Some(3),
    ..LUAU_OPTIMIZED_OPTIONS
};
const LUAU_VECTOR_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    retain_debug: false,
    ignore_debug: false,
    naming_mode: None,
    luau_optimization_level: Some(2),
    luau_vector: Some(LuauVectorCaseOptions {
        library: Some("vector"),
        constructor: "create",
        components: 3,
    }),
    recompile_rounds: None,
};
const NO_RECOMPILE_STRESS_OPTIONS: LuaCaseOptions = LuaCaseOptions {
    recompile_rounds: Some(0),
    ..LuaCaseOptions::DEFAULT
};

pub(crate) fn unit_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries(UNIT_CASES)
}

pub(crate) fn regression_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    [
        REGRESSION_CASES_001_100,
        REGRESSION_CASES_101_200,
        REGRESSION_CASES_201_318,
        REGRESSION_CASES_319,
        REGRESSION_CASES_320,
        REGRESSION_CASES_321,
        REGRESSION_CASES_322,
        REGRESSION_CASES_323,
        REGRESSION_CASES_324,
        REGRESSION_CASES_325,
        REGRESSION_CASES_326,
        REGRESSION_CASES_327,
        REGRESSION_CASES_328,
        REGRESSION_CASES_329,
        REGRESSION_CASES_330,
        REGRESSION_CASES_331,
        REGRESSION_CASES_332,
        REGRESSION_CASES_333,
        REGRESSION_CASES_334,
        REGRESSION_CASES_335,
        REGRESSION_CASES_336,
        REGRESSION_CASES_337,
        REGRESSION_CASES_338,
        REGRESSION_CASES_339,
        REGRESSION_CASES_340,
        REGRESSION_CASES_341,
    ]
    .into_iter()
    .flat_map(manifest_entries)
}

fn manifest_entries(
    cases: &'static [LuaCaseMatrixEntry],
) -> impl Iterator<Item = LuaCaseManifestEntry> {
    cases.iter().flat_map(|entry| {
        entry.dialects.iter().copied().flat_map(move |dialect| {
            std::iter::once(None)
                .filter(move |_| entry.variants.is_empty())
                .chain(entry.variants.iter().copied().map(Some))
                .map(move |variant| {
                    let mut options = entry.options;
                    if let Some(variant) = variant {
                        variant.apply(&mut options);
                    }
                    LuaCaseManifestEntry {
                        path: entry.path,
                        dialect,
                        variant,
                        options,
                        expectation: entry.expectation,
                        structure_contracts: entry.structure_contracts,
                    }
                })
        })
    })
}
