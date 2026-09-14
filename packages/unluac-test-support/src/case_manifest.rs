//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 目录区分 `unit` / `regression`；矩阵集中声明方言、编译选项和验证合同。
//! 每个 suite 展开时签发实例 ID，让调度与产物路径直接保留完整条目身份；
//! 例如同一 Lua 5.4 源码的 stripped/debug 两项分别执行，不由展示标签反向重建选项。

use strum_macros::{Display, IntoStaticStr};
use unluac::ast::NamingMode;
use unluac::decompile::DecompileDialect;

mod regressions_001_100;
mod regressions_101_200;
mod regressions_201_318;
mod regressions_319_400;
mod regressions_401_500;
mod regressions_501_600;
mod regressions_601_700;
mod unit_cases;

use regressions_001_100::REGRESSION_CASES_001_100;
use regressions_101_200::REGRESSION_CASES_101_200;
use regressions_201_318::REGRESSION_CASES_201_318;
use regressions_319_400::REGRESSION_CASES_319_400;
use regressions_401_500::REGRESSION_CASES_401_500;
use regressions_501_600::REGRESSION_CASES_501_600;
use regressions_601_700::REGRESSION_CASES_601_700;
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
    GlobalDeclResidual,
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

/// 同一 suite 的矩阵展开顺序签发的实例身份；选项相异的条目不能靠 path/dialect 重新匹配。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseId(pub usize);

/// 已展开并具有独立执行与产物身份的测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub id: LuaCaseId,
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub variant: Option<LuaCaseVariant>,
    pub(crate) options: LuaCaseOptions,
    pub(crate) expectation: LuaCaseExpectation,
    pub(crate) structure_contracts: &'static [LuaCaseStructureContract],
}

impl LuaCaseManifestEntry {
    /// 展示编译档位和 debug 策略；实例选择始终使用矩阵签发的 id。
    pub fn variant_label(self) -> String {
        let mut labels = Vec::new();
        if let Some(variant) = self.variant {
            labels.push(variant.label());
        }
        if self.options.retain_debug {
            labels.push("retain-debug");
        }
        if self.options.ignore_debug {
            labels.push("ignore-debug");
        }
        labels.join(",")
    }
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
    manifest_entries(UNIT_CASES.iter())
}

pub(crate) fn regression_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries(
        [
            REGRESSION_CASES_001_100,
            REGRESSION_CASES_101_200,
            REGRESSION_CASES_201_318,
            REGRESSION_CASES_319_400,
            REGRESSION_CASES_401_500,
            REGRESSION_CASES_501_600,
            REGRESSION_CASES_601_700,
        ]
        .into_iter()
        .flatten(),
    )
}

fn manifest_entries(
    cases: impl Iterator<Item = &'static LuaCaseMatrixEntry>,
) -> impl Iterator<Item = LuaCaseManifestEntry> {
    cases
        .flat_map(|entry| {
            entry.dialects.iter().copied().flat_map(move |dialect| {
                std::iter::once(None)
                    .filter(move |_| entry.variants.is_empty())
                    .chain(entry.variants.iter().copied().map(Some))
                    .map(move |variant| (entry, dialect, variant))
            })
        })
        .enumerate()
        .map(|(id, (entry, dialect, variant))| {
            let mut options = entry.options;
            if let Some(variant) = variant {
                variant.apply(&mut options);
            }
            LuaCaseManifestEntry {
                id: LuaCaseId(id),
                path: entry.path,
                dialect,
                variant,
                options,
                expectation: entry.expectation,
                structure_contracts: entry.structure_contracts,
            }
        })
}
