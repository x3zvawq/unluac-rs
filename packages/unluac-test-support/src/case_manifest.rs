//! 这个模块集中声明仓库里的 Lua case 测试矩阵。
//!
//! 真正的事实源是“一个 case 支持哪些 dialect、进入哪些 suite”。
//! `unit` 和 `regression` 再从这份矩阵里展开成具体的 `(case, dialect)` 测试单元，
//! 这样后续给 common case 显式挂多个 dialect 时，不需要回到“每行一个组合”的散乱写法。

use unluac::decompile::DecompileDialect;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LuaCaseDialect {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
    Luajit,
    Luau,
}

impl LuaCaseDialect {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
            Self::Lua54 => "lua5.4",
            Self::Lua55 => "lua5.5",
            Self::Luajit => "luajit",
            Self::Luau => "luau",
        }
    }

    pub(crate) const fn decompile_dialect(self) -> Option<DecompileDialect> {
        match self {
            Self::Lua51 => Some(DecompileDialect::Lua51),
            Self::Lua52 => Some(DecompileDialect::Lua52),
            Self::Lua53 => Some(DecompileDialect::Lua53),
            Self::Lua54 => Some(DecompileDialect::Lua54),
            Self::Lua55 => Some(DecompileDialect::Lua55),
            Self::Luajit => Some(DecompileDialect::Luajit),
            Self::Luau => Some(DecompileDialect::Luau),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseSuites {
    pub(crate) case_health: bool,
    pub(crate) decompile_pipeline_health: bool,
}

impl LuaCaseSuites {
    pub(crate) const fn all() -> Self {
        Self {
            case_health: true,
            decompile_pipeline_health: true,
        }
    }

    pub(crate) const fn case_health_only() -> Self {
        Self {
            case_health: true,
            decompile_pipeline_health: false,
        }
    }
}

/// 矩阵里的单个 case 定义。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct LuaCaseMatrixEntry {
    pub(crate) path: &'static str,
    pub(crate) dialects: &'static [LuaCaseDialect],
    pub(crate) suites: LuaCaseSuites,
}

impl LuaCaseMatrixEntry {
    const fn new(path: &'static str, dialects: &'static [LuaCaseDialect]) -> Self {
        Self::new_with_suites(path, dialects, LuaCaseSuites::all())
    }

    const fn new_with_suites(
        path: &'static str,
        dialects: &'static [LuaCaseDialect],
        suites: LuaCaseSuites,
    ) -> Self {
        Self {
            path,
            dialects,
            suites,
        }
    }
}

/// 展开后的 `(case, dialect)` 测试单元。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct LuaCaseManifestEntry {
    pub path: &'static str,
    pub dialect: LuaCaseDialect,
    pub(crate) suites: LuaCaseSuites,
}

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
const PUC_LUA_51: &[LuaCaseDialect] = &[LuaCaseDialect::Lua51];
const PUC_LUA_GE_52: &[LuaCaseDialect] = &[
    LuaCaseDialect::Lua52,
    LuaCaseDialect::Lua53,
    LuaCaseDialect::Lua54,
    LuaCaseDialect::Lua55,
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

pub(crate) const ALL_CASES: &[LuaCaseMatrixEntry] = &[
    // ── common cases ──
    // 每个文件内部以 `local function test_xxx()` 包裹，print 首参带 file#N 标签以便逐 proto 定位。
    LuaCaseMatrixEntry::new("tests/lua_cases/common_01_basics.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_02_control_flow.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_03_repeat_until.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_04_generic_for.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_05_boolean_expr.lua", ALL_DIALECTS),
    // boolean_regression 包含原 tricky/32、33（ALL_NON_LUAU），取最严格的 dialect 集
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common_06_boolean_regression.lua",
        ALL_NON_LUAU_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/common_07_return_and_multiret.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_08_closures.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_09_method_and_self.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_10_tables.lua", ALL_DIALECTS),
    LuaCaseMatrixEntry::new("tests/lua_cases/common_11_runtime.lua", ALL_DIALECTS),
    // ── dialect-specific cases ──
    LuaCaseMatrixEntry::new("tests/lua_cases/lua51_01.lua", PUC_LUA_51),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua52_01_env.lua", PUC_LUA_GE_52),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua52_02_goto.lua", PUC_LUA_GE_52),
    // lua52_03_extraarg_boundary 太大，保留但不注册
    LuaCaseMatrixEntry::new("tests/lua_cases/lua53_01.lua", PUC_LUA_GE_53),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua54_01_close.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua54_02_const.lua", PUC_LUA_GE_54),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua55_01_global.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/lua_cases/lua55_02_named_vararg.lua", PUC_LUA_GE_55),
    LuaCaseMatrixEntry::new("tests/lua_cases/luajit_01.lua", LUAJIT_ONLY),
    LuaCaseMatrixEntry::new("tests/lua_cases/luau_01.lua", LUAU_ONLY),
    // ── regression / adversarial cases ──
    // 这些 case 暴露了已知反编译 bug，单独建文件避免 decompile/runtime 失败波及同文件其他 proto。
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/regress_01_boolean_adversarial.lua",
        ALL_DIALECTS,
    ),
    LuaCaseMatrixEntry::new(
        "tests/lua_cases/regress_02_repeat_inner_ref.lua",
        ALL_DIALECTS,
    ),
];

pub(crate) fn case_health_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries().filter(|entry| entry.suites.case_health)
}

pub(crate) fn decompile_pipeline_health_cases() -> impl Iterator<Item = LuaCaseManifestEntry> {
    manifest_entries().filter(|entry| entry.suites.decompile_pipeline_health)
}

fn manifest_entries() -> impl Iterator<Item = LuaCaseManifestEntry> {
    ALL_CASES.iter().flat_map(|entry| {
        entry
            .dialects
            .iter()
            .copied()
            .map(move |dialect| LuaCaseManifestEntry {
                path: entry.path,
                dialect,
                suites: entry.suites,
            })
    })
}
