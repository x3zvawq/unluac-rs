//! 这个文件定义主 pipeline 的公共选项。
//!
//! 入口层集中补默认值，比把默认逻辑散在各阶段里更稳；后续阶段变多后，
//! 仍然只需要维护这一处归一化逻辑。

use crate::ast::{NamingMode, NamingOptions};
use crate::debug::{DebugColorMode, DebugDetail, DebugFilters};
use crate::generate::GenerateOptions;
use crate::parser::{ParseMode, ParseOptions, StringDecodeMode, StringEncoding};
use strum_macros::{Display, EnumString, IntoStaticStr};

use super::state::DecompileStage;

/// 供主 pipeline 和 CLI 共享的调试选项。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugOptions {
    pub enable: bool,
    pub output_stages: Vec<DecompileStage>,
    pub timing: bool,
    pub color: DebugColorMode,
    pub detail: DebugDetail,
    pub filters: DebugFilters,
    pub dump_passes: Vec<String>,
}

/// 调用方请求解析的目标 dialect。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
pub enum DecompileDialect {
    #[default]
    #[strum(serialize = "auto")]
    Auto,
    #[strum(serialize = "lua5.1", serialize = "lua51")]
    Lua51,
    #[strum(serialize = "lua5.2", serialize = "lua52")]
    Lua52,
    #[strum(serialize = "lua5.3", serialize = "lua53")]
    Lua53,
    #[strum(serialize = "lua5.4", serialize = "lua54")]
    Lua54,
    #[strum(serialize = "lua5.5", serialize = "lua55")]
    Lua55,
    #[strum(serialize = "luajit")]
    Luajit,
    #[strum(serialize = "luau")]
    Luau,
}

/// 控制结构恢复与 AST lowering 共同依赖的目标语法能力。
///
/// 这两个能力会直接改变 CFG edge 能否表达为正常源码，因此放在 pipeline 共享层；
/// Structure 不需要反向依赖 AST，AST 也不再维护另一份方言控制流表。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct ControlFlowCaps {
    pub goto_label: bool,
    pub continue_stmt: bool,
}

/// HIR 与 AST readability 共同消费的源码形状阈值。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReadabilityOptions {
    pub return_inline_max_complexity: usize,
    pub index_inline_max_complexity: usize,
    pub args_inline_max_complexity: usize,
    pub access_base_inline_max_complexity: usize,
}

impl Default for ReadabilityOptions {
    fn default() -> Self {
        Self {
            return_inline_max_complexity: 10,
            index_inline_max_complexity: 10,
            args_inline_max_complexity: 6,
            access_base_inline_max_complexity: 5,
        }
    }
}

impl DecompileDialect {
    /// 返回目标方言原生支持的控制流语法。
    pub const fn control_flow_caps(self) -> ControlFlowCaps {
        match self {
            Self::Lua52 | Self::Lua53 | Self::Lua54 | Self::Lua55 | Self::Luajit => {
                ControlFlowCaps {
                    goto_label: true,
                    continue_stmt: false,
                }
            }
            Self::Luau => ControlFlowCaps {
                goto_label: false,
                continue_stmt: true,
            },
            Self::Auto | Self::Lua51 => ControlFlowCaps {
                goto_label: false,
                continue_stmt: false,
            },
        }
    }

    /// 目标 VM 的字符串顺序比较是否固定为无符号字节词典序。
    ///
    /// PUC Lua 5.1-5.5 使用当前 `LC_COLLATE` 下的 `strcoll`；只有 LuaJIT 与 Luau
    /// 的 VM 顺序与反编译器内部 [`crate::LuaString`] 的字节序严格一致。
    pub(crate) const fn literal_string_order_is_binary(self) -> bool {
        matches!(self, Self::Luajit | Self::Luau)
    }
}

impl DecompileDialect {
    /// HIR 候选字段与 AST/Generate 共用的目标裸标识符规则。
    pub(crate) fn is_identifier_name(self, name: &str) -> bool {
        let mut chars = name.chars();
        let Some(first) = chars.next() else {
            return false;
        };
        if !(first == '_' || first.is_ascii_alphabetic()) {
            return false;
        }
        if !chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
            return false;
        }
        !self.is_keyword(name)
    }

    /// 判断 `name` 是否是该方言版本下禁止作为标识符的硬关键字。
    ///
    /// PUC Lua 5.2+ 的 `goto` 是硬关键字；LuaJIT `goto`、Luau `continue` 和
    /// Lua 5.5 `global` 只在对应语句上下文中有特殊含义，仍可作为普通名字。
    pub fn is_keyword(self, name: &str) -> bool {
        if is_base_lua_keyword(name) {
            return true;
        }
        match name {
            "goto" => matches!(self, Self::Lua52 | Self::Lua53 | Self::Lua54 | Self::Lua55),
            _ => false,
        }
    }

    /// 判断 `name` 是否在 **任意** 受支持方言中可能是关键字或上下文语法词。
    ///
    /// Naming 在目标方言未知时使用此保守全集，避免主动分配容易与语句语法冲突的名字；
    /// 目标明确的已有 global / field 名仍由 `is_keyword` 按标识符位置精确判断。
    pub fn is_keyword_in_any_dialect(name: &str) -> bool {
        is_base_lua_keyword(name) || matches!(name, "goto" | "continue" | "global")
    }
}

/// 所有方言共有的 21 个基础关键字（Lua 5.1 关键字集）。
fn is_base_lua_keyword(name: &str) -> bool {
    matches!(
        name,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
    )
}

/// 一次主反编译调用的顶层选项。
#[derive(Debug, Clone, PartialEq)]
pub struct DecompileOptions {
    pub dialect: DecompileDialect,
    pub parse: ParseOptions,
    pub target_stage: DecompileStage,
    pub debug: DebugOptions,
    pub readability: ReadabilityOptions,
    pub naming: NamingOptions,
    pub generate: GenerateOptions,
}

impl Default for DecompileOptions {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Auto,
            parse: ParseOptions {
                mode: ParseMode::Permissive,
                string_encoding: StringEncoding::Auto,
                string_decode_mode: StringDecodeMode::Strict,
                ignore_debug: false,
            },
            // 默认更偏向直接拿到最终源码，仓库内 CLI / wasm / 集成调用方都共享这套预期。
            target_stage: DecompileStage::Generate,
            debug: DebugOptions::default(),
            readability: ReadabilityOptions::default(),
            naming: NamingOptions {
                mode: NamingMode::DebugLike,
                debug_like_include_function: true,
            },
            generate: GenerateOptions::default(),
        }
    }
}

impl DecompileOptions {
    pub(crate) fn normalized(mut self) -> Self {
        if self.debug.enable && self.debug.output_stages.is_empty() && !self.debug.timing {
            self.debug.output_stages.push(self.target_stage);
        }
        self
    }
}
