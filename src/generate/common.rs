//! Generate 层共享类型。
//!
//! 这些类型需要同时被 decompile 入口、renderer 和调试输出复用，所以单独抽到这里，
//! 避免把“生成选项”“宿主构造器配置”“注释元信息”和“最终产物”散落在 emit/render 两边。

use crate::ast::DecompileDialect;
use crate::hir::{HirModule, HirProtoRef, ProtoLineRange, ProtoSignature};
use strum_macros::{Display, EnumString, IntoStaticStr};

/// 最终生成的源码结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedChunk {
    pub dialect: DecompileDialect,
    pub source: String,
    pub warnings: Vec<String>,
}

impl Default for GeneratedChunk {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Lua51,
            source: String::new(),
            warnings: Vec::new(),
        }
    }
}

/// 代码生成选项。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateOptions {
    pub mode: GenerateMode,
    pub indent_width: usize,
    pub max_line_length: usize,
    pub number_format: NumberFormat,
    pub quote_style: QuoteStyle,
    pub table_style: TableStyle,
    pub conservative_output: bool,
    pub comment: bool,
    /// 把 Luau vector 常量重新表达成源码时使用的宿主构造器。
    pub luau_vector_constructor: Option<LuauVectorConstructor>,
}

impl Default for GenerateOptions {
    fn default() -> Self {
        Self {
            mode: GenerateMode::Strict,
            indent_width: 4,
            max_line_length: 100,
            number_format: NumberFormat::Decimal,
            quote_style: QuoteStyle::MinEscape,
            table_style: TableStyle::Balanced,
            conservative_output: true,
            comment: true,
            luau_vector_constructor: None,
        }
    }
}

/// Luau 宿主用于构造原生 vector 值的源码入口。
///
/// `library = Some("vector")`、`constructor = "create"` 表示 `vector.create(...)`；
/// `library = None` 表示全局函数。bytecode 不保存这份宿主身份，因此必须由调用方显式提供。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LuauVectorConstructor {
    pub library: Option<String>,
    pub constructor: String,
    pub size: LuauVectorSize,
}

/// Luau VM 编译时选择的原生 vector 分量数。
///
/// bytecode 无法区分三维 vector 与 `w = 0` 的四维 vector，因此不能从常量值推断。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LuauVectorSize {
    Three,
    Four,
}

/// Generate 注释模式需要的只读元信息。
///
/// 这些字段都来自 parser/HIR 已经稳定产出的事实；Generate 只消费它们来决定注释文本，
/// 不会再反推或修补前层语义。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateCommentMetadata {
    pub chunk: GenerateChunkCommentMetadata,
    pub functions: Vec<GenerateFunctionCommentMetadata>,
}

impl GenerateCommentMetadata {
    pub(crate) fn from_hir(hir: &HirModule, encoding: &str) -> Self {
        let entry_source = hir
            .protos
            .get(hir.entry.index())
            .and_then(|proto| proto.source.clone());
        Self {
            chunk: GenerateChunkCommentMetadata {
                file_name: entry_source,
                encoding: encoding.to_owned(),
            },
            functions: hir
                .protos
                .iter()
                .map(|proto| GenerateFunctionCommentMetadata {
                    function: proto.id,
                    source: proto.source.clone(),
                    line_range: proto.line_range,
                    signature: proto.signature,
                    local_count: proto.locals.len(),
                    upvalue_count: proto.upvalues.len(),
                })
                .collect(),
        }
    }

    pub fn function(&self, function: HirProtoRef) -> Option<&GenerateFunctionCommentMetadata> {
        self.functions.get(function.index())
    }
}

/// chunk 级注释要展示的元信息。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateChunkCommentMetadata {
    pub file_name: Option<String>,
    pub encoding: String,
}

/// proto 级注释要展示的元信息。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateFunctionCommentMetadata {
    pub function: HirProtoRef,
    pub source: Option<String>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub local_count: usize,
    pub upvalue_count: usize,
}

/// 输出层在遇到目标方言不支持的语法时该如何处理。
///
/// - `Permissive`：无论如何都尝试输出代码，无法恢复的错误通过 Lua 注释占位。
/// - `Strict`：遇到任何反编译错误或目标 dialect 不支持的语法时直接报错并终止。
///
/// 库层默认为 `Strict`（最安全的编程接口约定）；CLI 层默认为 `Permissive`。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum GenerateMode {
    #[default]
    Strict,
    Permissive,
}

/// 数字字面量输出策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum NumberFormat {
    #[default]
    Decimal,
    Hex,
}

/// 字符串引号策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum QuoteStyle {
    PreferDouble,
    PreferSingle,
    #[default]
    MinEscape,
}

/// 表构造器布局策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum TableStyle {
    Compact,
    #[default]
    Balanced,
    Expanded,
}
