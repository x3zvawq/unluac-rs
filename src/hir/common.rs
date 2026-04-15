//! 这个文件集中声明 HIR 层的共享类型。
//!
//! HIR 已经进入“变量世界”，因此这里的核心职责是提供稳定的绑定身份、结构化
//! 语句节点以及少量受控 fallback 节点，供 AST/Readability/Naming 继续消费。

use crate::parser::{ProtoLineRange, ProtoSignature};

/// 整个 chunk 的 HIR 根对象。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirModule {
    pub entry: HirProtoRef,
    pub protos: Vec<HirProto>,
}

/// 单个 proto 的 HIR 结果。
#[derive(Debug, Clone, PartialEq)]
pub struct HirProto {
    pub id: HirProtoRef,
    pub source: Option<String>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub params: Vec<ParamId>,
    pub param_debug_hints: Vec<Option<String>>,
    pub locals: Vec<LocalId>,
    pub local_debug_hints: Vec<Option<String>>,
    pub upvalues: Vec<UpvalueId>,
    pub upvalue_debug_hints: Vec<Option<String>>,
    pub temps: Vec<TempId>,
    pub temp_debug_locals: Vec<Option<String>>,
    pub body: HirBlock,
    pub children: Vec<HirProtoRef>,
}

/// proto 的稳定引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct HirProtoRef(pub usize);

impl HirProtoRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 参数身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct ParamId(pub usize);

impl ParamId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 局部绑定身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct LocalId(pub usize);

impl LocalId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// upvalue 身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct UpvalueId(pub usize);

impl UpvalueId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 恢复过程里的临时绑定身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct TempId(pub usize);

impl TempId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// fallback label 的稳定身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct HirLabelId(pub usize);

impl HirLabelId {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 一段 HIR 语句块。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirBlock {
    pub stmts: Vec<HirStmt>,
}

/// HIR 语句。
#[derive(Debug, Clone, PartialEq)]
pub enum HirStmt {
    LocalDecl(Box<HirLocalDecl>),
    Assign(Box<HirAssign>),
    TableSetList(Box<HirTableSetList>),
    ErrNil(Box<HirErrNil>),
    ToBeClosed(Box<HirToBeClosed>),
    Close(Box<HirClose>),
    CallStmt(Box<HirCallStmt>),
    Return(Box<HirReturn>),
    If(Box<HirIf>),
    While(Box<HirWhile>),
    Repeat(Box<HirRepeat>),
    NumericFor(Box<HirNumericFor>),
    GenericFor(Box<HirGenericFor>),
    Break,
    Continue,
    Goto(Box<HirGoto>),
    Label(Box<HirLabel>),
    Block(Box<HirBlock>),
    Unstructured(Box<HirUnstructured>),
}

/// HIR 表达式。
#[derive(Debug, Clone, PartialEq)]
pub enum HirExpr {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(String),
    Int64(i64),
    UInt64(u64),
    Complex { real: f64, imag: f64 },
    ParamRef(ParamId),
    LocalRef(LocalId),
    UpvalueRef(UpvalueId),
    TempRef(TempId),
    GlobalRef(HirGlobalRef),
    TableAccess(Box<HirTableAccess>),
    Unary(Box<HirUnaryExpr>),
    Binary(Box<HirBinaryExpr>),
    LogicalAnd(Box<HirLogicalExpr>),
    LogicalOr(Box<HirLogicalExpr>),
    Decision(Box<HirDecisionExpr>),
    Call(Box<HirCallExpr>),
    VarArg,
    TableConstructor(Box<HirTableConstructor>),
    Closure(Box<HirClosureExpr>),
    Unresolved(Box<HirUnresolvedExpr>),
}

impl HirExpr {
    /// 对表达式取逻辑否定，自动消除双重 `not`。
    pub fn negate(self) -> Self {
        match self {
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => unary.expr,
            expr => HirExpr::Unary(Box::new(HirUnaryExpr {
                op: HirUnaryOpKind::Not,
                expr,
            })),
        }
    }
}

/// HIR 赋值左值。
#[derive(Debug, Clone, PartialEq)]
pub enum HirLValue {
    Temp(TempId),
    Local(LocalId),
    Upvalue(UpvalueId),
    Global(HirGlobalRef),
    TableAccess(Box<HirTableAccess>),
}

/// 全局引用。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct HirGlobalRef {
    pub name: String,
}

/// 表访问。
#[derive(Debug, Clone, PartialEq)]
pub struct HirTableAccess {
    pub base: HirExpr,
    pub key: HirExpr,
}

/// 一元表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirUnaryExpr {
    pub op: HirUnaryOpKind,
    pub expr: HirExpr,
}

/// 二元表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirBinaryExpr {
    pub op: HirBinaryOpKind,
    pub lhs: HirExpr,
    pub rhs: HirExpr,
}

/// 逻辑短路表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirLogicalExpr {
    pub lhs: HirExpr,
    pub rhs: HirExpr,
}

/// 共享决策 DAG 表达式。
///
/// 这类表达式只服务 HIR 内部的恢复与收敛：当共享短路子图如果立刻树化会明显重复展开时，
/// 先用 DAG 暂存共享关系，再由 HIR simplify 把它重新线性化成普通表达式或
/// `local + if + assign`。它不应该继续流到最终 AST。
#[derive(Debug, Clone, PartialEq)]
pub struct HirDecisionExpr {
    pub entry: HirDecisionNodeRef,
    pub nodes: Vec<HirDecisionNode>,
}

/// 决策 DAG 中的稳定节点引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct HirDecisionNodeRef(pub usize);

impl HirDecisionNodeRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 决策 DAG 的一个节点。
///
/// `test` 表示当前分支真正求值的 Lua 值；如果某条边选择 `CurrentValue`，表示直接把这次
/// 求值得到的原值继续往上返回，而不是重新求值 `test`。
#[derive(Debug, Clone, PartialEq)]
pub struct HirDecisionNode {
    pub id: HirDecisionNodeRef,
    pub test: HirExpr,
    pub truthy: HirDecisionTarget,
    pub falsy: HirDecisionTarget,
}

/// 决策 DAG 上的目标。
#[derive(Debug, Clone, PartialEq)]
pub enum HirDecisionTarget {
    Node(HirDecisionNodeRef),
    CurrentValue,
    Expr(HirExpr),
}

/// 一元运算。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum HirUnaryOpKind {
    Not,
    Neg,
    BitNot,
    Length,
}

/// 二元运算。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum HirBinaryOpKind {
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

/// 调用表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirCallExpr {
    pub callee: HirExpr,
    pub args: Vec<HirExpr>,
    pub multiret: bool,
    pub method: bool,
    /// 来自 `SELF` / `NAMECALL` 的 method 名事实。
    ///
    /// 这一层显式保留字段名，是为了避免后面的 AST build 再去猜
    /// `obj.method(obj, ...)` 是否可以收回 `obj:method(...)`。
    pub method_name: Option<String>,
}

/// 调用语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirCallStmt {
    pub call: HirCallExpr,
}

/// 局部声明。
#[derive(Debug, Clone, PartialEq)]
pub struct HirLocalDecl {
    pub bindings: Vec<LocalId>,
    pub values: Vec<HirExpr>,
}

/// 普通赋值。
#[derive(Debug, Clone, PartialEq)]
pub struct HirAssign {
    pub targets: Vec<HirLValue>,
    pub values: Vec<HirExpr>,
}

/// 表数组段批量写入。
///
/// `SETLIST` 这类写入在语义上仍然属于“往现有表里顺序填充一段数组槽位”，如果在 HIR
/// 里直接拆成若干低保真的 `Assign`，或者更糟糕地退回字符串化的 `Unstructured`，
/// 后面的构造器恢复就只能靠猜。这里先把它保留成受控语义节点，让 simplify 可以在
/// 看清前后文之后决定是折叠进 `TableConstructor`，还是继续保守保留。
#[derive(Debug, Clone, PartialEq)]
pub struct HirTableSetList {
    pub base: HirExpr,
    pub start_index: u32,
    pub values: Vec<HirExpr>,
    pub trailing_multivalue: Option<HirExpr>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirErrNil {
    pub value: HirExpr,
    pub name: Option<String>,
}

/// 标记某个绑定在当前词法作用域结束时需要执行 Lua 5.4 的 to-be-closed 语义。
///
/// 这一层先显式保留 “哪个绑定被标记为 `<close>`” 这个语义事实，而不是继续退回
/// `unstructured "tbc rX"`。后续 AST 可以再根据 target dialect 把它收成真正的
/// `<close>` 局部声明形式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirToBeClosed {
    /// 对应 Lua VM 里的寄存器槽位。
    ///
    /// 这里额外保留 `tbc rX` 的原始槽位，不是为了把后面的 AST 再次绑定回寄存器，
    /// 而是为了让 HIR 还能在结构层之后重建“这条 `<close>` 词法块究竟在什么位置结束”。
    /// 对于像 Lua 5.4 `goto` 反复进入同一块、以及多条退出路径都触发 cleanup 的 case，
    /// 单靠 `value: HirExpr` 已经不足以把多个 `close from rX` 重新配对回同一条声明。
    pub reg_index: usize,
    pub value: HirExpr,
}

/// 显式表示一次 Lua VM `Close` cleanup 边界。
///
/// 这里先保留“从哪个寄存器槽位开始关闭”活动值这个语义事实，避免在 HIR 里继续退回
/// `unstructured "close from rX"`。后续 AST 可以基于它和 `ToBeClosed` 的组合，
/// 再决定是否能恢复成 `<close>` 变量的词法块边界。
#[derive(Debug, Clone, PartialEq)]
pub struct HirClose {
    pub from_reg: usize,
}

/// 返回语句。
///
/// `trailing_multiret` 标记最后一个值是否会展开为多个返回值（对应字节码层面的 Open pack）。
/// 当为 `false` 时，所有值都是"固定"的，AST 层面需要对末尾的 Call/VarArg 加上 `()`
/// 来阻止多返回展开（即包裹为 `SingleValue`）。
#[derive(Debug, Clone, PartialEq)]
pub struct HirReturn {
    pub values: Vec<HirExpr>,
    pub trailing_multiret: bool,
}

/// if 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirIf {
    pub cond: HirExpr,
    pub then_block: HirBlock,
    pub else_block: Option<HirBlock>,
}

/// while 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirWhile {
    pub cond: HirExpr,
    pub body: HirBlock,
}

/// repeat 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirRepeat {
    pub body: HirBlock,
    pub cond: HirExpr,
}

/// 数值 for。
#[derive(Debug, Clone, PartialEq)]
pub struct HirNumericFor {
    pub binding: LocalId,
    pub start: HirExpr,
    pub limit: HirExpr,
    pub step: HirExpr,
    pub body: HirBlock,
}

/// 泛型 for。
#[derive(Debug, Clone, PartialEq)]
pub struct HirGenericFor {
    pub bindings: Vec<LocalId>,
    pub iterator: Vec<HirExpr>,
    pub body: HirBlock,
}

/// goto 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirGoto {
    pub target: HirLabelId,
}

/// label 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirLabel {
    pub id: HirLabelId,
}

/// 保守 fallback 区域。
#[derive(Debug, Clone, PartialEq)]
pub struct HirUnstructured {
    pub body: HirBlock,
    pub summary: Option<String>,
}

/// 表构造器。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirTableConstructor {
    pub fields: Vec<HirTableField>,
    pub trailing_multivalue: Option<HirExpr>,
}

/// 表构造器字段。
///
/// 这里刻意保留字段顺序，而不是拆成“数组字段列表 + 记录字段列表”。原因是 Lua
/// 构造器允许数组段和 keyed field 交错出现，求值顺序和覆盖顺序都可能影响语义；
/// 如果在 HIR 里过早打散顺序，后面再想把 `NewTable + SetTable + SetList` 折回构造器时
/// 就只能靠不安全的重排去兜。
#[derive(Debug, Clone, PartialEq)]
pub enum HirTableField {
    Array(HirExpr),
    Record(HirRecordField),
}

/// 表记录字段。
#[derive(Debug, Clone, PartialEq)]
pub struct HirRecordField {
    pub key: HirTableKey,
    pub value: HirExpr,
}

/// 表字段 key。
#[derive(Debug, Clone, PartialEq)]
pub enum HirTableKey {
    Name(String),
    Expr(HirExpr),
}

/// 闭包表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirClosureExpr {
    pub proto: HirProtoRef,
    pub captures: Vec<HirCapture>,
}

/// 闭包 capture。
#[derive(Debug, Clone, PartialEq)]
pub struct HirCapture {
    pub value: HirExpr,
}

/// 未解析表达式。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirUnresolvedExpr {
    pub summary: String,
}
