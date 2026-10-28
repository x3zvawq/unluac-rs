//! Generate 层共享类型。
//!
//! 这些类型需要同时被 decompile 入口、renderer 和调试输出复用，所以单独抽到这里，
//! 避免把“生成选项”“宿主构造器配置”“注释元信息”和“最终产物”散落在 emit/render 两边。

use crate::LuaString;
use crate::ast::DecompileDialect;
use crate::hir::{HirModule, HirProtoRef, ProtoLineRange, ProtoSignature};
use strum_macros::{Display, EnumString, IntoStaticStr};

/// 最终生成的源码结果。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeneratedChunk {
    pub dialect: DecompileDialect,
    pub kind: GeneratedChunkKind,
    pub source: String,
}

impl Default for GeneratedChunk {
    fn default() -> Self {
        Self {
            dialect: DecompileDialect::Lua51,
            kind: GeneratedChunkKind::Source,
            source: String::new(),
        }
    }
}

/// 生成文本是否仍是目标方言源码。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum GeneratedChunkKind {
    #[default]
    Source,
    DiagnosticPseudocode,
}

/// 代码生成选项。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateOptions {
    pub mode: GenerateMode,
    pub indent_width: usize,
    pub max_line_length: usize,
    pub number_format: NumberFormat,
    pub quote_style: QuoteStyle,
    /// 优先将已解码字符串作为 UTF-8 文本输出；关闭时保留原字节值。
    pub readable_strings: bool,
    pub table_style: TableStyle,
    /// Align record keys on `=` in multi-line aligned tables.
    pub table_align_eq: bool,
    /// Cap on the number of spaces between a key and `=` when aligning records: a
    /// run cannot stretch the gap beyond this threshold, otherwise the
    /// field starts a new run so that one long key does not stretch every row.
    /// Zero disables the alignment entirely.
    pub table_align_eq_max_spaces: usize,
    /// Fold redundant explicit index keys `[1]..[n]` into positional fields of the
    /// constructor. The bytecode stores such keys faithfully (the source wrote them
    /// out explicitly), so the fold is opt-in: it only changes the unspecified
    /// `pairs` order (the hash part becomes an array).
    pub table_drop_index_keys: bool,
    /// Aligned style only: maximum rendered row width (including indentation) of a
    /// space-aligned table grid. Rows never exceed this budget unless a single cell
    /// alone is wider. When unset (`None`) the grid follows `max_line_length`, so
    /// the row budget always matches the global line budget unless overridden.
    pub table_align_width: Option<usize>,
    /// Aligned style only: maximum rendered width (including quotes) of a string
    /// literal allowed inside a space-aligned table grid; wider strings make the
    /// whole table fall back to the one-entry-per-line layout.
    pub table_align_string_width: usize,
    /// Aligned style only: horizontal alignment of grid cells. `Auto` picks the
    /// direction per cell kind: numbers right-align so digits and trailing commas
    /// line up, every other primitive (strings, names, booleans, nil) left-aligns
    /// so word-like values share a common left edge. `Left`/`Right` force one
    /// direction for all kinds.
    pub table_align_cells: TableCellAlign,
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
            readable_strings: true,
            table_style: TableStyle::Balanced,
            table_align_eq: true,
            table_align_eq_max_spaces: 8,
            table_drop_index_keys: false,
            table_align_width: None,
            table_align_string_width: 16,
            table_align_cells: TableCellAlign::Auto,
            comment: true,
            luau_vector_constructor: None,
        }
    }
}

impl GenerateOptions {
    /// Row budget for `aligned` grids: `table_align_width` when set, otherwise
    /// `max_line_length` (the default coupling; see the field docs).
    pub fn resolved_table_align_width(&self) -> usize {
        self.table_align_width.unwrap_or(self.max_line_length)
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
                    local_count: proto.local_count,
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
    pub file_name: Option<LuaString>,
    pub encoding: String,
}

/// proto 级注释要展示的元信息。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenerateFunctionCommentMetadata {
    pub function: HirProtoRef,
    pub source: Option<LuaString>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub local_count: usize,
    pub upvalue_count: usize,
}

/// 生成层面对无法由目标方言表达的控制流采取的策略。
///
/// `Permissive` 允许用 goto/label 和 Error 占位尽量展示恢复结果，并把包含缺口的产物
/// 标为诊断伪源码；`Strict` 要求得到目标方言可表达的源码。
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
///
/// `Aligned` 在三种布局之间按表内容自动选择：放得下就保持单行；放不下且全部字段是
/// 同类小字面量（数字、短字符串、布尔、nil 或普通名字）时输出空格对齐的网格；
/// 其余情况（包括任何字典）每行一条记录。网格行宽与字符串宽度上限由
/// `table_align_width` / `table_align_string_width` 控制。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum TableStyle {
    Compact,
    #[default]
    Balanced,
    Aligned,
    Expanded,
}

/// Horizontal alignment of cells inside an `aligned` grid.
///
/// Grids are homogeneous (every cell has the same kind), so `Auto` resolves the
/// direction once per grid from that kind: numbers right-align (digits of mixed
/// magnitude stay comparable and trailing commas line up), while strings, names,
/// booleans and nil left-align (word-like values share a common left edge, which
/// reads better for text). nil grids are alignment-invariant (all cells render as
/// `nil`), the direction only decides where the separator padding goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum TableCellAlign {
    #[default]
    Auto,
    Left,
    Right,
}
