//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 每份源码只登记一次，标签和保护边界归属于源码；配置数组声明方言、编译选项和验证合同。
//! 全部主题统一展开实例 ID，让调度与产物路径直接保留完整条目身份；
//! 例如同一 Lua 5.4 源码的 stripped/debug 两项分别执行，不由展示标签反向重建选项。

use strum_macros::{Display, IntoStaticStr};
use unluac::ast::NamingMode;
use unluac::decompile::DecompileDialect;

mod bindings;
mod calls;
mod closures;
mod control_flow;
mod lifetime;
mod literals;
mod operators;
mod protocol;
mod runtime;
mod stress;
mod syntax;
mod tables;
const CASE_GROUPS: &[&[LuaCaseDefinition]] = &[
    bindings::CASES,
    calls::CASES,
    closures::CASES,
    control_flow::CASES,
    lifetime::CASES,
    literals::CASES,
    operators::CASES,
    protocol::CASES,
    runtime::CASES,
    stress::CASES,
    syntax::CASES,
    tables::CASES,
];

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

/// 源码是唯一登记单位，多个标签表达交叉主题，配置数组保留各实例完整合同。
#[derive(Debug, Clone, Copy)]
pub(crate) struct LuaCaseDefinition {
    path: &'static str,
    tags: &'static [&'static str],
    purpose: &'static str,
    configurations: &'static [LuaCaseConfiguration],
}

impl LuaCaseDefinition {
    const fn new(
        path: &'static str,
        tags: &'static [&'static str],
        purpose: &'static str,
        configurations: &'static [LuaCaseConfiguration],
    ) -> Self {
        Self {
            path,
            tags,
            purpose,
            configurations,
        }
    }
}

/// 一个源码合同可展开多组配置；配置不重复声明源码路径和主题元信息。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseConfiguration {
    pub(crate) dialects: &'static [LuaCaseDialect],
    pub(crate) options: LuaCaseOptions,
    pub(crate) variants: &'static [LuaCaseVariant],
    pub(crate) expectation: LuaCaseExpectation,
    pub(crate) structure_contracts: &'static [LuaCaseStructureContract],
}

impl LuaCaseConfiguration {
    const fn new(dialects: &'static [LuaCaseDialect]) -> Self {
        Self {
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

/// 全部主题统一签发实例身份；选项相异的条目不能靠 path/dialect 重新匹配。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseId(pub usize);

/// 已展开并具有独立执行与产物身份的测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub tags: &'static [&'static str],
    pub purpose: &'static str,
    pub id: LuaCaseId,
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub variant: Option<LuaCaseVariant>,
    pub(crate) options: LuaCaseOptions,
    pub(crate) expectation: LuaCaseExpectation,
    pub(crate) structure_contracts: &'static [LuaCaseStructureContract],
}

impl LuaCaseManifestEntry {
    /// 目录主分类只决定归属；交叉语义由 tags 表达。
    pub fn category(self) -> &'static str {
        self.path
            .split('/')
            .nth(1)
            .and_then(|part| part.strip_prefix("case_"))
            .expect("case paths must carry a category directory")
    }

    /// 导出展开后的配置，索引与迁移核对不从展示标签猜测配置。
    pub fn configuration_description(self) -> String {
        format!(
            "{:?}; {:?}; {:?}",
            self.options, self.expectation, self.structure_contracts
        )
    }

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

fn case_definitions() -> impl Iterator<Item = &'static LuaCaseDefinition> {
    CASE_GROUPS.iter().flat_map(|group| group.iter())
}

/// 目录分类、唯一登记与索引字段是源码合同的输入约束；列表阶段一次校验，执行实例不重复扫描。
pub fn validate_case_catalog() -> Result<(), String> {
    let mut paths = std::collections::BTreeSet::new();
    let mut group_numbers = std::collections::BTreeSet::new();
    for case in case_definitions() {
        if !paths.insert(case.path) {
            return Err(format!(
                "case source registered more than once: {}",
                case.path
            ));
        }
        let relative = case
            .path
            .strip_prefix("tests/case_")
            .ok_or_else(|| format!("case path lacks a category: {}", case.path))?;
        let (category, filename) = relative
            .split_once('/')
            .ok_or_else(|| format!("case path lacks a filename: {}", case.path))?;
        let mut name = filename.strip_suffix(".lua").unwrap_or("").splitn(3, '_');
        let subtopic = name.next().unwrap_or("");
        let number = name.next().unwrap_or("");
        let title = name.next().unwrap_or("");
        if category.is_empty()
            || !category
                .bytes()
                .all(|ch| ch.is_ascii_lowercase() || ch == b'_')
            || subtopic.is_empty()
            || !subtopic
                .bytes()
                .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit())
            || number.len() != 2
            || !number.bytes().all(|ch| ch.is_ascii_digit())
            || number == "00"
            || title.is_empty()
            || title.contains(['/', '\\'])
        {
            return Err(format!(
                "invalid category/subtopic_number_title case path: {}",
                case.path
            ));
        }
        if !group_numbers.insert((category, subtopic, number)) {
            return Err(format!(
                "duplicate case number in {category}/{subtopic}: {number} ({})",
                case.path
            ));
        }
        if case.purpose.trim().is_empty()
            || case.purpose.contains(['\t', '\r', '\n'])
            || case.tags.is_empty()
            || case.configurations.is_empty()
        {
            return Err(format!(
                "case needs a one-line purpose, tags and configurations: {}",
                case.path
            ));
        }
        let mut tags = std::collections::BTreeSet::new();
        for tag in case.tags {
            if tag.is_empty()
                || !tag
                    .bytes()
                    .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == b'-')
                || !tags.insert(tag)
            {
                return Err(format!("invalid or repeated tag {tag:?} in {}", case.path));
            }
        }
    }
    Ok(())
}

pub(crate) fn manifest_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    case_definitions()
        .flat_map(|case| {
            case.configurations.iter().flat_map(move |config| {
                config.dialects.iter().copied().flat_map(move |dialect| {
                    std::iter::once(None)
                        .filter(move |_| config.variants.is_empty())
                        .chain(config.variants.iter().copied().map(Some))
                        .map(move |variant| (case, config, dialect, variant))
                })
            })
        })
        .enumerate()
        .map(|(id, (case, config, dialect, variant))| {
            let mut options = config.options;
            if let Some(variant) = variant {
                variant.apply(&mut options);
            }
            LuaCaseManifestEntry {
                id: LuaCaseId(id),
                path: case.path,
                tags: case.tags,
                purpose: case.purpose,
                dialect,
                variant,
                options,
                expectation: config.expectation,
                structure_contracts: config.structure_contracts,
            }
        })
}
