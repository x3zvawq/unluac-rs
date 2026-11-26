//! 统一 AST 数据模型与稳定绑定身份。
//!
//! 仅保留目标 Lua 语法、语义属性及 Naming/Generate 所需的纯净元数据。

use std::collections::BTreeSet;
use std::fmt;

use strum_macros::{Display, IntoStaticStr};

use crate::LuaString;
use crate::decompile::DecompileDialect;
use crate::parser::{Origin, ProtoLineRange, ProtoSignature};

// ── 稳定身份 ID ─────────────────────────────────────────────

/// 函数 proto 身份（与 `AstModule::protos` 及 DFS 先序编号一一对应）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ProtoId(pub usize);

impl ProtoId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 参数身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ParamId(pub usize);

impl ParamId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 局部绑定身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct LocalId(pub usize);

impl LocalId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 上值身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct UpvalueId(pub usize);

impl UpvalueId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// AST 合成局部身份（如状态机 `_state` 或并行交换临时变量）。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct AstSyntheticLocalId(pub usize);

impl AstSyntheticLocalId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// Label 身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct AstLabelId(pub usize);

impl AstLabelId {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for AstLabelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "L{}", self.0)
    }
}

// ── 模块与函数元数据 ────────────────────────────────────────

/// 捕获方式。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstCaptureMode {
    ByReference,
    ByValue,
}

/// 被子闭包捕获的父绑定身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AstCaptureBinding {
    Param(ParamId),
    Local(LocalId),
    SyntheticLocal(AstSyntheticLocalId),
    Upvalue(UpvalueId),
}

/// 单条闭包捕获记录。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AstCapture {
    pub binding: AstCaptureBinding,
    pub mode: AstCaptureMode,
}

/// 单个 proto 附带的只读元数据（供 Naming 与 Generate 注释消费）。
#[derive(Debug, Clone, PartialEq)]
pub struct AstProtoMeta {
    pub id: ProtoId,
    pub source: Option<LuaString>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub params: Vec<ParamId>,
    pub param_debug_hints: Vec<Option<String>>,
    pub local_count: usize,
    pub local_debug_hints: Vec<Option<String>>,
    pub vararg_param_local: Option<LocalId>,
    pub lexical_environment_local: Option<LocalId>,
    pub upvalues: Vec<UpvalueId>,
    pub upvalue_debug_hints: Vec<Option<String>>,
    pub environment_upvalues: Vec<UpvalueId>,
    /// 若本 proto 由父函数闭包创建，记录其父函数及捕获列表，供 Naming 继承父绑定名。
    pub parent_captures: Option<(ProtoId, Vec<AstCapture>)>,
    /// 本 proto 对应的原始字节码 `RawProto` 位置（合成包装 proto 为 `None`）。
    pub source_origin: Option<Origin>,
    /// 本 proto 是否触发了 Lua 5.1/Luau 局部状态机兜底（供测试与质量监控观测）。
    pub state_machine_count: usize,
}

/// AST 根对象。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct AstModule {
    pub entry_function: ProtoId,
    pub body: AstBlock,
    /// DFS 先序排列的全部 proto 元数据。
    pub protos: Vec<AstProtoMeta>,
    /// 本模块的目标方言（供 Naming 执行方言精确关键字与 `_ENV` 保留）。
    pub target_dialect: Option<DecompileDialect>,
    pub(crate) next_synthetic_local: usize,
}

impl AstModule {
    pub fn proto(&self, id: ProtoId) -> Option<&AstProtoMeta> {
        self.protos.get(id.index())
    }
}

// ── 语句与表达式 ────────────────────────────────────────────

/// AST 语句块。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct AstBlock {
    pub stmts: Vec<AstStmt>,
}

/// AST 语句。
#[derive(Debug, Clone, PartialEq)]
pub enum AstStmt {
    LocalDecl(Box<AstLocalDecl>),
    GlobalDecl(Box<AstGlobalDecl>),
    Assign(Box<AstAssign>),
    CallStmt(Box<AstCallStmt>),
    Return(Box<AstReturn>),
    If(Box<AstIf>),
    While(Box<AstWhile>),
    Repeat(Box<AstRepeat>),
    NumericFor(Box<AstNumericFor>),
    GenericFor(Box<AstGenericFor>),
    Break,
    Continue,
    Goto(Box<AstGoto>),
    Label(Box<AstLabel>),
    DoBlock(Box<AstBlock>),
    FunctionDecl(Box<AstFunctionDecl>),
    LocalFunctionDecl(Box<AstLocalFunctionDecl>),
    /// 宽松模式下无法恢复的语句诊断占位。
    Error(String),
}

/// AST 表达式。
#[derive(Debug, Clone, PartialEq)]
pub enum AstExpr {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(LuaString),
    Int64(i64),
    UInt64(u64),
    Complex {
        real: f64,
        imag: f64,
    },
    Vector(crate::parser::VectorLiteral),
    Var(AstNameRef),
    FieldAccess(Box<AstFieldAccess>),
    IndexAccess(Box<AstIndexAccess>),
    Unary(Box<AstUnaryExpr>),
    Binary(Box<AstBinaryExpr>),
    LogicalAnd(Box<AstLogicalExpr>),
    LogicalOr(Box<AstLogicalExpr>),
    IfExpr(Box<AstIfExpr>),
    Call(Box<AstCallExpr>),
    MethodCall(Box<AstMethodCallExpr>),
    /// 显式单值截断 `(expr)`，用于保护多返回调用在尾位置不被错误展开。
    SingleValue(Box<AstExpr>),
    VarArg,
    TableConstructor(Box<AstTableConstructor>),
    FunctionExpr(Box<AstFunctionExpr>),
    /// 宽松模式下无法恢复的表达式占位。
    Error(String),
}

/// 赋值语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstAssign {
    pub targets: Vec<AstLValue>,
    pub values: Vec<AstExpr>,
    /// Luau 复合赋值标记（如 `x += y`）；普通赋值为 `None`。
    pub compound_op: Option<AstBinaryOpKind>,
}

/// 赋值左值。
#[derive(Debug, Clone, PartialEq)]
pub enum AstLValue {
    Name(AstNameRef),
    FieldAccess(Box<AstFieldAccess>),
    IndexAccess(Box<AstIndexAccess>),
}

/// 变量/绑定引用。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstNameRef {
    Param(ParamId),
    Local(LocalId),
    SyntheticLocal(AstSyntheticLocalId),
    Upvalue(UpvalueId),
    /// PUC Lua 5.2+ 的词法环境 `_ENV`。
    Environment,
    Global(AstGlobalName),
}

/// 可在 `local` / `for` 中声明的绑定身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstBindingRef {
    Local(LocalId),
    SyntheticLocal(AstSyntheticLocalId),
}

impl AstBindingRef {
    pub fn from_name_ref(name: &AstNameRef) -> Option<Self> {
        match name {
            AstNameRef::Local(local) => Some(Self::Local(*local)),
            AstNameRef::SyntheticLocal(local) => Some(Self::SyntheticLocal(*local)),
            AstNameRef::Param(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Environment
            | AstNameRef::Global(_) => None,
        }
    }

    pub const fn to_name_ref(self) -> AstNameRef {
        match self {
            Self::Local(local) => AstNameRef::Local(local),
            Self::SyntheticLocal(local) => AstNameRef::SyntheticLocal(local),
        }
    }

    pub fn matches_name_ref(self, name: &AstNameRef) -> bool {
        Self::from_name_ref(name) == Some(self)
    }
}

/// 全局名。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct AstGlobalName {
    pub text: String,
}

/// 返回语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstReturn {
    pub values: Vec<AstExpr>,
}

/// 函数表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFunctionExpr {
    pub function: ProtoId,
    pub params: Vec<ParamId>,
    pub is_vararg: bool,
    pub named_vararg: Option<AstBindingRef>,
    pub body: AstBlock,
    pub captured_bindings: BTreeSet<AstBindingRef>,
    pub captured_params: BTreeSet<ParamId>,
    pub capture_write_names: BTreeSet<AstNameRef>,
}

/// 顶层/表字段函数声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFunctionDecl {
    pub target: AstFunctionName,
    pub global_declaration: bool,
    pub func: AstFunctionExpr,
}

/// `local function` 声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalFunctionDecl {
    pub name: AstBindingRef,
    pub func: AstFunctionExpr,
}

/// 函数声明名。
#[derive(Debug, Clone, PartialEq)]
pub enum AstFunctionName {
    Plain(AstNamePath),
    Method(AstNamePath, String),
}

/// `a.b.c` 名字路径。
#[derive(Debug, Clone, PartialEq)]
pub struct AstNamePath {
    pub root: AstNameRef,
    pub fields: Vec<String>,
}

/// 目标语法方言与能力集。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstTargetDialect {
    pub version: DecompileDialect,
    pub caps: AstDialectCaps,
}

/// AST 关心的语法能力。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstDialectCaps {
    pub goto_label: bool,
    pub continue_stmt: bool,
    pub if_expr: bool,
    pub local_const: bool,
    pub local_close: bool,
    pub global_decl: bool,
    pub global_const: bool,
}

/// AST/Generate 关心的可选语法特性。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash, Display, IntoStaticStr)]
pub enum AstFeature {
    #[strum(serialize = "goto")]
    GotoLabel,
    #[strum(serialize = "continue")]
    ContinueStmt,
    #[strum(serialize = "if-expression")]
    IfExpr,
    #[strum(serialize = "local<const>")]
    LocalConst,
    #[strum(serialize = "local<close>")]
    LocalClose,
    #[strum(serialize = "global")]
    GlobalDecl,
    #[strum(serialize = "global<const>")]
    GlobalConst,
}

impl AstTargetDialect {
    pub const fn new(version: DecompileDialect) -> Self {
        let control = version.control_flow_caps();
        let caps = AstDialectCaps {
            goto_label: control.goto_label,
            continue_stmt: control.continue_stmt,
            if_expr: matches!(version, DecompileDialect::Luau),
            local_const: matches!(version, DecompileDialect::Lua54 | DecompileDialect::Lua55),
            local_close: matches!(version, DecompileDialect::Lua54 | DecompileDialect::Lua55),
            global_decl: matches!(version, DecompileDialect::Lua55),
            global_const: matches!(version, DecompileDialect::Lua55),
        };
        Self { version, caps }
    }

    pub const fn supports_feature(self, feature: AstFeature) -> bool {
        self.caps.supports(feature)
    }
}

impl AstDialectCaps {
    pub const fn supports(self, feature: AstFeature) -> bool {
        match feature {
            AstFeature::GotoLabel => self.goto_label,
            AstFeature::ContinueStmt => self.continue_stmt,
            AstFeature::IfExpr => self.if_expr,
            AstFeature::LocalConst => self.local_const,
            AstFeature::LocalClose => self.local_close,
            AstFeature::GlobalDecl => self.global_decl,
            AstFeature::GlobalConst => self.global_decl && self.global_const,
        }
    }
}

/// `local` 声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalDecl {
    pub bindings: Vec<AstLocalBinding>,
    pub values: Vec<AstExpr>,
}

/// `global` 声明（Lua 5.5）。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGlobalDecl {
    pub bindings: Vec<AstGlobalBinding>,
    pub values: Vec<AstExpr>,
}

/// `local` 绑定。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalBinding {
    pub id: AstBindingRef,
    pub attr: AstLocalAttr,
    pub is_debug_hinted: bool,
}

/// `global` 绑定。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGlobalBinding {
    pub target: AstGlobalBindingTarget,
    pub attr: AstGlobalAttr,
}

/// `global` 声明的绑定目标。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstGlobalBindingTarget {
    Name(AstGlobalName),
    Wildcard,
}

/// 局部声明属性。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstLocalAttr {
    None,
    Const,
    Close,
}

/// 全局声明属性。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstGlobalAttr {
    None,
    Const,
}

/// 字段访问 `base.field`。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFieldAccess {
    pub base: AstExpr,
    pub field: String,
}

/// 索引访问 `base[index]`。
#[derive(Debug, Clone, PartialEq)]
pub struct AstIndexAccess {
    pub base: AstExpr,
    pub index: AstExpr,
}

/// 一元表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstUnaryExpr {
    pub op: AstUnaryOpKind,
    pub expr: AstExpr,
}

/// 二元表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstBinaryExpr {
    pub op: AstBinaryOpKind,
    pub lhs: AstExpr,
    pub rhs: AstExpr,
}

/// 逻辑表达式（`and` / `or`）。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLogicalExpr {
    pub lhs: AstExpr,
    pub rhs: AstExpr,
}

/// Luau 条件表达式 `if cond then a else b`。
#[derive(Debug, Clone, PartialEq)]
pub struct AstIfExpr {
    pub cond: AstExpr,
    pub then_expr: AstExpr,
    pub else_expr: AstExpr,
}

/// 普通调用。
#[derive(Debug, Clone, PartialEq)]
pub struct AstCallExpr {
    pub callee: AstExpr,
    pub args: Vec<AstExpr>,
}

/// 方法调用 `receiver:method(args)`。
#[derive(Debug, Clone, PartialEq)]
pub struct AstMethodCallExpr {
    /// 若为 Luau 字符串插值，保留各静态片段。
    pub interpolation: Option<Vec<LuaString>>,
    pub receiver: AstExpr,
    pub method: String,
    pub args: Vec<AstExpr>,
}

/// 调用语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstCallStmt {
    pub call: AstCallKind,
}

/// 调用统一承载。
#[derive(Debug, Clone, PartialEq)]
pub enum AstCallKind {
    Call(Box<AstCallExpr>),
    MethodCall(Box<AstMethodCallExpr>),
}

/// 表构造器。
#[derive(Debug, Clone, PartialEq)]
pub struct AstTableConstructor {
    pub fields: Vec<AstTableField>,
    /// PUC 批量表初始化标记（供 Generate `table_drop_index_keys` 安全判断）。
    pub is_puc_batched: bool,
}

/// 表字段。
#[derive(Debug, Clone, PartialEq)]
pub enum AstTableField {
    Array(AstExpr),
    Record(AstRecordField),
}

/// 键值字段。
#[derive(Debug, Clone, PartialEq)]
pub struct AstRecordField {
    pub key: AstTableKey,
    pub value: AstExpr,
}

/// 键值字段的键。
#[derive(Debug, Clone, PartialEq)]
pub enum AstTableKey {
    Name(String),
    Expr(AstExpr),
}

/// `if` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstIf {
    pub cond: AstExpr,
    pub then_block: AstBlock,
    pub else_block: Option<AstBlock>,
}

/// `while` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstWhile {
    pub cond: AstExpr,
    pub body: AstBlock,
}

/// `repeat ... until` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstRepeat {
    pub body: AstBlock,
    pub cond: AstExpr,
}

/// 数值 `for` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstNumericFor {
    pub binding: AstBindingRef,
    pub start: AstExpr,
    pub limit: AstExpr,
    pub step: AstExpr,
    pub body: AstBlock,
}

/// 泛型 `for` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGenericFor {
    pub bindings: Vec<AstBindingRef>,
    pub iterator: Vec<AstExpr>,
    pub body: AstBlock,
}

/// `goto` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGoto {
    pub target: AstLabelId,
}

/// label 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLabel {
    pub id: AstLabelId,
}

/// 一元运算种类。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstUnaryOpKind {
    Not,
    Neg,
    BitNot,
    Length,
}

/// 二元运算种类。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstBinaryOpKind {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Pow,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Concat,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// 提取 `AstExpr` 可静态判定的精确整数表键（供 Generate `table_drop_index_keys` 使用）。
impl AstExpr {
    pub(crate) fn table_integer_key(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            Self::Number(value) => (value.is_finite()
                && value.fract() == 0.0
                && value.abs() <= ((1_u64 << f64::MANTISSA_DIGITS) as f64))
            .then_some(*value as i64),
            Self::SingleValue(inner) => inner.table_integer_key(),
            _ => None,
        }
    }

    /// 静态判断表达式结果是否保证为布尔值。
    pub(crate) fn is_boolean_valued(&self) -> bool {
        match self {
            Self::Boolean(_) => true,
            Self::Unary(u) => u.op == AstUnaryOpKind::Not,
            Self::Binary(b) => matches!(
                b.op,
                AstBinaryOpKind::Eq
                    | AstBinaryOpKind::Lt
                    | AstBinaryOpKind::Le
                    | AstBinaryOpKind::Gt
                    | AstBinaryOpKind::Ge
            ),
            Self::LogicalAnd(l) | Self::LogicalOr(l) => {
                l.lhs.is_boolean_valued() && l.rhs.is_boolean_valued()
            }
            Self::SingleValue(inner) => inner.is_boolean_valued(),
            _ => false,
        }
    }

    /// 静态判断表达式结果是否绝对为真（永不为 `false` 或 `nil`），
    /// 用于安全判定 `a and b or c` 折叠（规避 Lua falsy 陷阱）。
    pub(crate) fn is_guaranteed_truthy(&self) -> bool {
        match self {
            Self::Boolean(true)
            | Self::Integer(_)
            | Self::Number(_)
            | Self::String(_)
            | Self::Int64(_)
            | Self::UInt64(_)
            | Self::Complex { .. }
            | Self::Vector(_)
            | Self::TableConstructor(_)
            | Self::FunctionExpr(_) => true,
            Self::SingleValue(inner) => inner.is_guaranteed_truthy(),
            _ => false,
        }
    }
}
