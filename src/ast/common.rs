//! 这个文件集中声明 AST 层的共享语法节点。
//!
//! AST 是 target-dialect-aware 的语法树：它不再做控制流恢复，但要把 HIR 已经确定
//! 的结构落成“某个目标 Lua 方言真正允许出现”的语法节点。

use std::fmt;

use crate::hir::{HirLabelId, LocalId, ParamId, TempId, UpvalueId};

/// AST 根对象。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct AstModule {
    pub body: AstBlock,
}

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
}

/// AST 表达式。
#[derive(Debug, Clone, PartialEq)]
pub enum AstExpr {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(String),
    Var(AstNameRef),
    FieldAccess(Box<AstFieldAccess>),
    IndexAccess(Box<AstIndexAccess>),
    Unary(Box<AstUnaryExpr>),
    Binary(Box<AstBinaryExpr>),
    LogicalAnd(Box<AstLogicalExpr>),
    LogicalOr(Box<AstLogicalExpr>),
    Call(Box<AstCallExpr>),
    MethodCall(Box<AstMethodCallExpr>),
    VarArg,
    TableConstructor(Box<AstTableConstructor>),
    FunctionExpr(Box<AstFunctionExpr>),
}

/// 赋值语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstAssign {
    pub targets: Vec<AstLValue>,
    pub values: Vec<AstExpr>,
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
    Temp(TempId),
    Upvalue(UpvalueId),
    Global(AstGlobalName),
}

/// 可在 `local` 中声明的 binding。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstBindingRef {
    Local(LocalId),
    Temp(TempId),
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
    pub params: Vec<ParamId>,
    pub is_vararg: bool,
    pub body: AstBlock,
}

/// 顶层/表字段函数声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFunctionDecl {
    pub target: AstFunctionName,
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

/// `a.b.c` 这类名字路径。
#[derive(Debug, Clone, PartialEq)]
pub struct AstNamePath {
    pub root: AstNameRef,
    pub fields: Vec<String>,
}

/// 目标语法方言。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstTargetDialect {
    pub version: AstDialectVersion,
    pub caps: AstDialectCaps,
}

/// AST 关心的语法能力。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AstDialectCaps {
    pub goto_label: bool,
    pub continue_stmt: bool,
    pub local_const: bool,
    pub local_close: bool,
    pub global_decl: bool,
    pub global_const: bool,
}

/// 当前支持的目标方言版本。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstDialectVersion {
    Lua51,
    Lua52,
    Lua53,
    Lua54,
    Lua55,
}

impl AstDialectVersion {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Lua51 => "lua5.1",
            Self::Lua52 => "lua5.2",
            Self::Lua53 => "lua5.3",
            Self::Lua54 => "lua5.4",
            Self::Lua55 => "lua5.5",
        }
    }
}

impl fmt::Display for AstDialectVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

impl AstTargetDialect {
    pub const fn new(version: AstDialectVersion) -> Self {
        let caps = match version {
            AstDialectVersion::Lua51 => AstDialectCaps {
                goto_label: false,
                continue_stmt: false,
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            AstDialectVersion::Lua52 | AstDialectVersion::Lua53 => AstDialectCaps {
                goto_label: true,
                continue_stmt: false,
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            AstDialectVersion::Lua54 => AstDialectCaps {
                goto_label: true,
                continue_stmt: false,
                local_const: true,
                local_close: true,
                global_decl: false,
                global_const: false,
            },
            AstDialectVersion::Lua55 => AstDialectCaps {
                goto_label: true,
                continue_stmt: false,
                local_const: true,
                local_close: true,
                global_decl: true,
                global_const: true,
            },
        };
        Self { version, caps }
    }
}

/// `local` 声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalDecl {
    pub bindings: Vec<AstLocalBinding>,
    pub values: Vec<AstExpr>,
}

/// `global` 声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGlobalDecl {
    pub bindings: Vec<AstGlobalBinding>,
    pub values: Vec<AstExpr>,
}

/// `local` binding。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalBinding {
    pub id: AstBindingRef,
    pub attr: AstLocalAttr,
}

/// `global` binding。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGlobalBinding {
    pub name: AstGlobalName,
    pub attr: AstGlobalAttr,
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

/// 字段访问。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFieldAccess {
    pub base: AstExpr,
    pub field: String,
}

/// 索引访问。
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

/// 逻辑表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLogicalExpr {
    pub lhs: AstExpr,
    pub rhs: AstExpr,
}

/// 普通调用。
#[derive(Debug, Clone, PartialEq)]
pub struct AstCallExpr {
    pub callee: AstExpr,
    pub args: Vec<AstExpr>,
}

/// 方法调用。
#[derive(Debug, Clone, PartialEq)]
pub struct AstMethodCallExpr {
    pub receiver: AstExpr,
    pub method: String,
    pub args: Vec<AstExpr>,
}

/// 调用语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstCallStmt {
    pub call: AstCallKind,
}

/// 调用表达式/语句的统一承载。
#[derive(Debug, Clone, PartialEq)]
pub enum AstCallKind {
    Call(Box<AstCallExpr>),
    MethodCall(Box<AstMethodCallExpr>),
}

/// 表构造器。
#[derive(Debug, Clone, PartialEq)]
pub struct AstTableConstructor {
    pub fields: Vec<AstTableField>,
}

/// 表字段。
#[derive(Debug, Clone, PartialEq)]
pub enum AstTableField {
    Array(AstExpr),
    Record(AstRecordField),
}

/// 记录字段。
#[derive(Debug, Clone, PartialEq)]
pub struct AstRecordField {
    pub key: AstTableKey,
    pub value: AstExpr,
}

/// 记录 key。
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

/// `repeat` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstRepeat {
    pub body: AstBlock,
    pub cond: AstExpr,
}

/// `numeric for` 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct AstNumericFor {
    pub binding: AstBindingRef,
    pub start: AstExpr,
    pub limit: AstExpr,
    pub step: AstExpr,
    pub body: AstBlock,
}

/// `generic for` 语句。
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

/// AST label 身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct AstLabelId(pub usize);

impl AstLabelId {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl From<HirLabelId> for AstLabelId {
    fn from(value: HirLabelId) -> Self {
        Self(value.index())
    }
}

/// 一元运算。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstUnaryOpKind {
    Not,
    Neg,
    BitNot,
    Length,
}

/// 二元运算。
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
}
