//! 这个文件集中声明 HIR 层的共享类型。
//!
//! HIR 已经进入“变量世界”，因此这里的核心职责是提供稳定的绑定身份、结构化
//! 语句节点、保真的纯字面量以及少量受控 fallback 节点，供 AST/Readability/Naming 继续消费。

use std::collections::{BTreeMap, BTreeSet};

use crate::LuaString;
use crate::parser::{ProtoLineRange, ProtoSignature};
use crate::recovery::ProtoFailure;
use crate::transformer::FastCallArgs;
use crate::transformer::InstrRef;

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
    /// 已分配的 LocalId 编号域为 `0..local_count`；debug 映射按 ID 下标访问。
    ///
    /// lowering 与 simplify 只追加身份，删除源码声明或合并绑定不缩减编号域。
    pub local_count: usize,
    /// 函数入口由 VM 变参参数寄存器承载的 local 身份。
    ///
    /// 该身份在 binding 分配时冻结；AST 是否把它写进形参列表仍由签名种类和真实使用决定。
    pub vararg_param_local: Option<LocalId>,
    pub local_debug_hints: Vec<Option<String>>,
    /// `local_debug_hints` 对应的源码局部作用域身份；合成 local 为 `None`。
    pub local_debug_scopes: Vec<Option<usize>>,
    /// Structure 已接受的源码 debug local 区间，按原 debug scope identity 索引。
    pub debug_scopes: Vec<Option<HirDebugScope>>,
    /// Temps with a HIR-proven physical GC-root lifetime not represented by ordinary uses.
    ///
    /// These have not been promoted to HIR locals, so AST build must transfer the root identity
    /// when it materializes the temp as a source local.
    pub physical_root_temps: BTreeSet<TempId>,
    /// Locals with a HIR-proven physical GC-root lifetime not represented by ordinary uses.
    ///
    /// AST cleanup must not remove or shorten these declarations: the VM stack slot can keep a
    /// call result, escaped allocation, or closure-observable value alive after its last HIR use.
    pub physical_root_locals: BTreeSet<LocalId>,
    /// HIR 对后续表达式重写拥有的结论，按当前 binding 身份保存。
    ///
    /// `temp-inline` 只在已经证明删除会破坏 VM/HIR 语义时写入 `Preserve`；没有记录
    /// 仍是显式的 `Unknown`，不能被解释成 HIR 已经批准 AST 删除。locals promotion 会把
    /// temp 结论并入对应 local，使 AST 不必重新构造 home/capture/value-epoch 证明。
    pub inline_dispositions: HirInlineDispositions,
    pub upvalues: Vec<UpvalueId>,
    /// 由 VM 证明为当前词法环境的 upvalue cell 身份。
    ///
    /// 集合成员仍使用普通 `UpvalueId`，使读写、capture、mutability 和 root/lifetime
    /// consumer 共享同一身份；AST 只消费这项 role 事实决定是否写成 `_ENV`。
    pub environment_upvalues: BTreeSet<UpvalueId>,
    /// Upvalues that this proto or one of its descendant closures may write.
    ///
    /// The set is transitive through by-reference captures. A by-value capture may mutate the
    /// child's private snapshot, but does not make the parent binding mutable.
    pub mutable_upvalues: BTreeSet<UpvalueId>,
    pub upvalue_debug_hints: Vec<Option<String>>,
    /// bindings 分配的 TempId 编号域为 `0..temp_count`，debug 映射按 ID 下标访问。
    ///
    /// simplify 可退役或复用身份，但不缩减编号域；这不是当前活跃 temp 的数量。
    pub temp_count: usize,
    pub temp_debug_locals: Vec<Option<String>>,
    /// `temp_debug_locals` 对应的源码局部作用域身份；编译器内部槽位为 `None`。
    pub temp_debug_scopes: Vec<Option<usize>>,
    /// HIR 退出时仍需由 AST 满足或报告的事实。
    ///
    /// 这些事实已经脱离 Structure/SSA 的类型空间；AST 只消费这里冻结的索引和值语义，
    /// 不得再读取 StructureFacts 重新解释 lowering 结果。simplify 结束时按当前语义树
    /// 退役已消失的控制语法要求；失败与 unresolved 诊断保留原始证据。
    pub exit_requirements: Vec<HirExitRequirement>,
    pub body: HirBlock,
    pub children: Vec<HirProtoRef>,
    /// 当前 proto 无法继续降低时保留的分层诊断；成功 proto 为 `None`。
    pub failure: Option<ProtoFailure>,
    /// 失败父节点无法恢复原 closure 放置时，仍以诊断 local 展示的直接子 proto。
    pub detached_children: Vec<(LocalId, HirProtoRef)>,
}

/// HIR 对某个 binding 的表达式重写结论。
///
/// 当前迁移阶段只发布负向结论。`Unknown` 仍允许既有 AST 路径工作，但不代表正向证明；
/// 后续会以具体 definition/transaction 为身份增加可消费的正向 certificate。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum HirInlineDisposition {
    #[default]
    Unknown,
    Preserve(BTreeSet<HirInlineRetentionReason>),
}

impl HirInlineDisposition {
    pub const fn must_preserve(&self) -> bool {
        matches!(self, Self::Preserve(_))
    }

    fn note_preservation(&mut self, reason: HirInlineRetentionReason) -> bool {
        match self {
            Self::Unknown => {
                *self = Self::Preserve(BTreeSet::from([reason]));
                true
            }
            Self::Preserve(reasons) => reasons.insert(reason),
        }
    }

    fn merge(&mut self, other: &Self) {
        let Self::Preserve(reasons) = other else {
            return;
        };
        for reason in reasons {
            let _ = self.note_preservation(*reason);
        }
    }
}

/// HIR 已证明必须保留 binding 的原因。
///
/// 原因是跨层 capability 的说明，不携带 Structure/SSA 的 home slot 或 def 类型。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirInlineRetentionReason {
    /// 删除快照会让引用捕获观察到另一个 value epoch。
    CapturedValueEpoch,
    /// 常量替换会改变运行时建表与模板复制的分配方式。
    TableInitialization,
}

/// 单个 proto 内跨 temp/local 身份提升保存的重写结论。
///
/// 查询借用当前结论；跨层发布独立快照时显式复制，promotion 直接合并来源原因。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HirInlineDispositions {
    temps: BTreeMap<TempId, HirInlineDisposition>,
    locals: BTreeMap<LocalId, HirInlineDisposition>,
}

impl HirInlineDispositions {
    pub fn temp(&self, temp: TempId) -> &HirInlineDisposition {
        self.temps
            .get(&temp)
            .unwrap_or(&HirInlineDisposition::Unknown)
    }

    pub fn local(&self, local: LocalId) -> &HirInlineDisposition {
        self.locals
            .get(&local)
            .unwrap_or(&HirInlineDisposition::Unknown)
    }

    pub fn preserve_temp(&mut self, temp: TempId, reason: HirInlineRetentionReason) -> bool {
        self.temps
            .entry(temp)
            .or_default()
            .note_preservation(reason)
    }

    pub fn preserve_local(&mut self, local: LocalId, reason: HirInlineRetentionReason) -> bool {
        self.locals
            .entry(local)
            .or_default()
            .note_preservation(reason)
    }

    /// 把 canonical temp 的全部负向结论并入提升后的 local。
    ///
    /// 同一 TempId 可覆盖多个 definition epoch，而多个 temp 也可合并成同一个 local；
    /// AST 最终只看见 binding 身份，因此这里必须取并集，不能挑选某一次定义的结论。
    pub fn promote_temp_to_local(&mut self, temp: TempId, local: LocalId) {
        let Some(disposition) = self.temps.get(&temp) else {
            return;
        };
        self.locals.entry(local).or_default().merge(disposition);
    }
}

/// HIR 边界保留的 typed requirement/residual。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HirExitRequirement {
    RequiredControlFlow {
        /// 原始 proto 树的先序身份，用于与 Structure/bytecode dump 对齐。
        source_proto: usize,
        feature: HirControlFlowFeature,
    },
    UnresolvedValue {
        /// 原始 proto 树的先序身份，用于与 Structure/bytecode dump 对齐。
        source_proto: usize,
        /// 原 Structure phi 的稳定数字身份，仅用于定位诊断。
        phi: usize,
        /// 原 CFG block 的稳定数字身份，仅用于定位诊断。
        block: usize,
        /// 原 VM register 的稳定数字身份，仅用于定位诊断。
        register: usize,
    },
}

/// HIR 语义树要求 AST 提供的控制流表达能力。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirControlFlowFeature {
    GotoLabel,
    ContinueStatement,
}

/// 已由 Structure 绑定到唯一 SSA 身份的源码 debug local 区间。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HirDebugScope {
    pub start_pc: u32,
    pub end_pc: u32,
    /// 该 debug 区间在函数终结 Return 指令执行前结束。
    pub ends_before_return: bool,
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

/// `locals` 已证明可由 AST 合回 initializer 的单次 storage transaction 身份。
///
/// token 只连接最终 HIR 中一条空 `LocalDecl` 与其紧邻的 multi-call `Assign`；它不代表
/// binding 的通用定义身份，也不授权其它删除、内联或生命周期缩短。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HirInitializerMergeTransactionId {
    proto: HirProtoRef,
    ordinal: usize,
}

/// HIR 已证明可原子收回 method callee setup 的单次事务身份。
///
/// token 只连接最终 HIR 中一条 method lookup assignment 与紧邻的 method call；它不把
/// `method_key` 升格为通用删除许可，也不授权 AST 独立推断物理根生命周期。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HirMethodRewriteTransactionId {
    proto: HirProtoRef,
    ordinal: usize,
}

/// low/SSA 已验证的单个 method setup/call 协议身份。
///
/// 该身份只用于把具体 call occurrence 接回 HIR 私有协议；它本身不是 producer 删除许可。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HirMethodSetupProtocolId(usize);

impl HirMethodSetupProtocolId {
    pub(crate) const fn new(index: usize) -> Self {
        Self(index)
    }

    pub(crate) const fn index(self) -> usize {
        self.0
    }
}

impl HirMethodRewriteTransactionId {
    pub(crate) const fn new(proto: HirProtoRef, ordinal: usize) -> Self {
        Self { proto, ordinal }
    }

    pub(crate) const fn matches_protocol(
        self,
        proto: HirProtoRef,
        protocol: HirMethodSetupProtocolId,
    ) -> bool {
        self.proto.0 == proto.0 && self.ordinal == protocol.index()
    }
}

impl HirInitializerMergeTransactionId {
    pub(crate) const fn new(proto: HirProtoRef, ordinal: usize) -> Self {
        Self { proto, ordinal }
    }
}

/// 一次 generic-for initializer transaction 的不透明 HIR 身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HirGenericForInitializerTransactionId {
    proto: HirProtoRef,
    ordinal: usize,
}

impl HirGenericForInitializerTransactionId {
    pub(crate) const fn new(proto: HirProtoRef, ordinal: usize) -> Self {
        Self { proto, ordinal }
    }
}

/// initializer transaction 内一条 producer assignment occurrence 的不透明身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct HirGenericForInitializerProducerId {
    transaction: HirGenericForInitializerTransactionId,
    ordinal: usize,
}

impl HirGenericForInitializerProducerId {
    pub(crate) const fn new(
        transaction: HirGenericForInitializerTransactionId,
        ordinal: usize,
    ) -> Self {
        Self {
            transaction,
            ordinal,
        }
    }

    pub(crate) const fn transaction(self) -> HirGenericForInitializerTransactionId {
        self.transaction
    }
}

/// producer 在 generic-for semantic iterator pack 中贡献的连续区间。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct HirGenericForInitializerSpan {
    pub producer: HirGenericForInitializerProducerId,
    pub value_start: usize,
    pub value_count: usize,
}

/// lowering 已证明的 initializer producer ownership；不授权任何源码改写。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirGenericForInitializerTransaction {
    pub id: HirGenericForInitializerTransactionId,
    /// 原始协议宽度独立于 simplify 后可能已裁掉的 trailing nil。
    pub iterator_width: usize,
    pub producers: Vec<HirGenericForInitializerSpan>,
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
    GlobalDecl(Box<HirGlobalDecl>),
    Assign(Box<HirAssign>),
    /// 在已证明的交接或 dispatch 终点清除源码 local 的额外 GC 根。
    /// 只写该 LocalId，不覆盖其 provenance 中的 VM home；例如 `local new=old`
    /// 后释放 old，不能让物理槽分析误认为 new 也已被清零。
    LocalRootRelease(LocalId),
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
}

impl HirStmt {
    /// 借用单 temp、单固定 RHS、无尾包的赋值；不证明该定义可内联、删除或移动。
    pub(crate) fn scalar_temp_assignment(&self) -> Option<(TempId, &HirExpr)> {
        let Self::Assign(assign) = self else {
            return None;
        };
        let ([HirLValue::Temp(temp)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        Some((*temp, value))
    }
}

/// HIR 表达式。
#[derive(Debug, Clone, PartialEq)]
pub enum HirExpr {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(LuaString),
    Int64(i64),
    UInt64(u64),
    Complex { real: f64, imag: f64 },
    Vector(crate::parser::VectorLiteral),
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
    Param(ParamId),
    Temp(TempId),
    Local(LocalId),
    Upvalue(UpvalueId),
    Global(HirGlobalRef),
    TableAccess(Box<HirTableAccess>),
}

/// 已由前层环境访问协议证明的全局引用。
///
/// key 保留 VM 常量的原始字节身份；能否写成目标方言的裸标识符由
/// AST lowering 验证，不得反向影响 HIR 对环境访问的分类。
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct HirGlobalRef {
    pub key: LuaString,
}

/// 表访问。
#[derive(Debug, Clone, PartialEq)]
pub struct HirTableAccess {
    pub base: HirExpr,
    pub key: HirExpr,
    /// 仅标记来自同一 low method setup 的 canonical GetTable producer。
    pub(crate) method_setup_protocol: Option<HirMethodSetupProtocolId>,
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
    /// 原始参数槽交给该 call 的事实；只供 HIR 消费，不向 AST 泄漏物理槽协议。
    pub argument_roots: Vec<HirCallArgumentRoot>,
    /// 原始 caller home 在该精确 dispatch 处结束的 call result 身份。
    /// 此前可能已有观察；消费者须核对当前值流与 callee/参数求值顺序，不能提前释放。
    pub(crate) frame_root_ends: Vec<TempId>,
    pub callee: HirExpr,
    pub args: HirValuePack,
    pub method: bool,
    /// Luau FASTCALL 协议证明 fallback callee setup 位于参数物化之后，仅用于恢复源码求值顺序。
    pub fastcall: Option<FastCallArgs>,
    /// 来自 `SELF` / `NAMECALL` 的 method raw key 事实。
    ///
    /// 这一层显式保留字段的原始字节，是为了避免后面的 AST build 再去猜
    /// `obj[key](obj, ...)` 的协议身份；只有 AST 才决定 key 能否写成 `obj:method(...)`。
    pub method_key: Option<LuaString>,
    /// HIR 对当前 call occurrence 发布的 callee 物理根交接证明。
    ///
    /// 该证明来自仍有效的底层 method-setup 协议；AST 可以据此把承载 method callee
    /// 的机械 producer 收回到这个调用点，但不得从 `method_key` 或当前表达式形状重建它。
    pub callee_root_handoff: Option<HirCallRootHandoff>,
    /// 与 method lookup producer 配对的一次性 HIR 改写事务。
    pub method_rewrite_transaction: Option<HirMethodRewriteTransactionId>,
}

/// 一个 canonical definition 的原始 home 在该参数位置交给 callee。
///
/// producer 仍须在当前 HIR 中唯一，参数必须仍直接读取它；clone、合并或树化后不得
/// 单凭绑定名沿用。交接只终止 caller 对该槽的独立持有，不证明对象已被回收。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HirCallArgumentRoot {
    pub(crate) producer: TempId,
    pub(crate) argument: usize,
}

/// 调用点接管底层物理根的方式。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum HirCallRootHandoff {
    /// method setup 的 callee 槽由当前调用消费，强根终点正是这个 call occurrence。
    MethodCallee(HirMethodSetupProtocolId),
}

impl HirCallExpr {
    pub(crate) fn transfers_argument_root(&self, temp: TempId) -> bool {
        self.argument_roots.iter().any(|root| {
            root.producer == temp
                && self.args.fixed.get(root.argument) == Some(&HirExpr::TempRef(temp))
        })
    }

    /// 返回由前层 method 协议证明的 receiver 与字段名。
    pub(crate) fn method_receiver(&self) -> Option<(&HirExpr, &LuaString)> {
        if !self.method {
            return None;
        }
        let method_key = self.method_key.as_ref()?;
        let receiver = self.args.first()?;
        matches!(&self.callee,
            HirExpr::TableAccess(access)
                if access.base == *receiver
                    && matches!(&access.key,
                        HirExpr::String(key) if key == method_key))
        .then_some((receiver, method_key))
    }
}

/// Lua 表达式列表：若存在尾包，它是列表中唯一会展开的值。
///
/// 普通 `HirExpr` 始终只产生一个标量值；开放结果不能再借普通 temp/local 保存。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirValuePack {
    pub fixed: Vec<HirExpr>,
    pub tail: Option<HirPackTail>,
}

impl HirValuePack {
    pub fn fixed(values: Vec<HirExpr>) -> Self {
        Self {
            fixed: values,
            tail: None,
        }
    }

    pub fn expanding(fixed: Vec<HirExpr>, tail: HirPackTail) -> Self {
        Self {
            fixed,
            tail: Some(tail),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &HirExpr> {
        self.fixed
            .iter()
            .chain(self.tail.iter().map(HirPackTail::as_expr))
    }

    pub fn is_empty(&self) -> bool {
        self.fixed.is_empty() && self.tail.is_none()
    }

    /// 返回源码表达式槽数；exact tail 仍只占一个槽，结果宽度见 `exact_result_len`。
    pub fn expr_len(&self) -> usize {
        self.fixed.len() + usize::from(self.tail.is_some())
    }

    pub fn exact_result_len(&self) -> Option<usize> {
        Some(
            self.fixed.len()
                + match &self.tail {
                    Some(tail) => tail.exact_width()?,
                    None => 0,
                },
        )
    }

    /// 调整到接收位置后的结果来源；超过已知结果宽度时返回 None，表示补 nil。
    ///
    /// 多个尾结果共享同一个 producer，例如 `a,b=f()` 的两个位置都指向 f()；
    /// 这不表示重复求值，也不证明两个结果具有相同的值或生命周期。
    pub fn result_source(&self, index: usize) -> Option<&HirExpr> {
        if let Some(value) = self.fixed.get(index) {
            return Some(value);
        }
        let tail = self.tail.as_ref()?;
        let tail_index = index - self.fixed.len();
        tail.exact_width()
            .is_none_or(|width| tail_index < width)
            .then(|| tail.as_expr())
    }

    pub fn first(&self) -> Option<&HirExpr> {
        self.fixed
            .first()
            .or_else(|| self.tail.as_ref().map(HirPackTail::as_expr))
    }

    pub fn last(&self) -> Option<&HirExpr> {
        self.tail
            .as_ref()
            .map(HirPackTail::as_expr)
            .or_else(|| self.fixed.last())
    }
}

impl From<Vec<HirExpr>> for HirValuePack {
    fn from(values: Vec<HirExpr>) -> Self {
        Self::fixed(values)
    }
}

fn pack_tail_expr(tail: &HirPackTail) -> &HirExpr {
    tail.as_expr()
}

impl<'a> IntoIterator for &'a HirValuePack {
    type Item = &'a HirExpr;
    type IntoIter = std::iter::Chain<
        std::slice::Iter<'a, HirExpr>,
        std::iter::Map<std::option::Iter<'a, HirPackTail>, fn(&'a HirPackTail) -> &'a HirExpr>,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.fixed.iter().chain(
            self.tail
                .iter()
                .map(pack_tail_expr as fn(&'a HirPackTail) -> &'a HirExpr),
        )
    }
}

/// 只能出现在显式多值尾槽中的展开值。
///
/// 普通值列表使用 [`HirValuePack::tail`]，表构造器使用
/// [`HirTableConstructor::trailing_multivalue`]；其它位置不得承载展开语义。
#[derive(Debug, Clone, PartialEq)]
pub struct HirPackTail {
    expr: HirExpr,
    exact_width: Option<usize>,
}

impl HirPackTail {
    pub fn open(expr: HirExpr) -> Self {
        assert!(matches!(expr, HirExpr::Call(_) | HirExpr::VarArg));
        Self {
            expr,
            exact_width: None,
        }
    }

    pub fn exact(expr: HirExpr, width: usize) -> Self {
        assert!(width > 1);
        assert!(matches!(expr, HirExpr::Call(_) | HirExpr::VarArg));
        Self {
            expr,
            exact_width: Some(width),
        }
    }

    pub fn as_expr(&self) -> &HirExpr {
        &self.expr
    }

    /// 返回开放尾调用的可变内容，但不暴露可替换根节点的 `&mut HirExpr`。
    pub fn call_mut(&mut self) -> Option<&mut HirCallExpr> {
        match &mut self.expr {
            HirExpr::Call(call) => Some(call.as_mut()),
            HirExpr::VarArg => None,
            _ => unreachable!("pack tail root must remain a call or vararg"),
        }
    }

    pub fn into_expr(self) -> HirExpr {
        self.expr
    }

    pub fn map_call(self, map: impl FnOnce(HirCallExpr) -> HirCallExpr) -> Self {
        let expr = match self.expr {
            HirExpr::Call(call) => HirExpr::Call(Box::new(map(*call))),
            HirExpr::VarArg => HirExpr::VarArg,
            _ => unreachable!("pack tail root must remain a call or vararg"),
        };
        Self {
            expr,
            exact_width: self.exact_width,
        }
    }

    pub fn try_map_call(
        self,
        map: impl FnOnce(HirCallExpr) -> Option<HirCallExpr>,
    ) -> Option<Self> {
        let expr = match self.expr {
            HirExpr::Call(call) => HirExpr::Call(Box::new(map(*call)?)),
            HirExpr::VarArg => HirExpr::VarArg,
            _ => unreachable!("pack tail root must remain a call or vararg"),
        };
        Some(Self {
            expr,
            exact_width: self.exact_width,
        })
    }

    pub fn into_open(self) -> Self {
        Self::open(self.expr)
    }

    pub fn exact_width(&self) -> Option<usize> {
        self.exact_width
    }
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
    pub values: HirValuePack,
    /// 仅授权与同 token、紧邻且形状仍匹配的 assignment 合回 initializer。
    pub initializer_merge_transaction: Option<HirInitializerMergeTransactionId>,
}

/// Lua 5.5 `global` 初始化声明。
///
/// `ERRNNIL` 是编译器为该语法发出的显式协议；初始化先完整求值 RHS，再按 names 逆序
/// probe/store。HIR 直接保留源码顺序：单结果使用 fixed pack，多结果调用保留 exact tail，
/// 避免把结果物化成会漂移的局部根。
#[derive(Debug, Clone, PartialEq)]
pub struct HirGlobalDecl {
    pub names: Vec<LuaString>,
    pub values: HirValuePack,
}

/// 普通赋值。
#[derive(Debug, Clone, PartialEq)]
pub struct HirAssign {
    pub targets: Vec<HirLValue>,
    pub values: HirValuePack,
    /// 仅授权与同 token、紧邻且形状仍匹配的 empty local declaration 合并。
    pub initializer_merge_transaction: Option<HirInitializerMergeTransactionId>,
    /// 只证明该 assignment occurrence 属于某个 generic-for initializer；删除、移动、
    /// 展开与 capture/lifetime 合法性仍由 consumer 重新验证。
    pub generic_for_initializer_producer: Option<HirGenericForInitializerProducerId>,
    /// 与紧邻 method call 配对的一次性 HIR 改写事务。
    pub method_rewrite_transaction: Option<HirMethodRewriteTransactionId>,
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
    pub values: HirValuePack,
}

#[derive(Debug, Clone, PartialEq)]
pub struct HirErrNil {
    pub value: HirExpr,
    pub name: Option<String>,
}

/// 标记某个绑定在当前词法作用域结束时需要执行 Lua 5.4 的 to-be-closed 语义。
///
/// 这一层显式保留 “哪个绑定被标记为 `<close>`” 这个语义事实，后续 AST 可以再根据
/// target dialect 把它收成真正的 `<close>` 局部声明形式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirToBeClosed {
    /// 原始 `TBC` 指令 identity；与 label 的冻结 active-set 精确配对，避免寄存器复用
    /// 让 close-scope materialization 把 goto target 放到错误的词法块。
    pub origin: InstrRef,
    /// 原始槽位只参与 HIR 候选 epoch 与覆盖阈值查询；资源配对以 origin 为准。
    pub reg_index: usize,
    pub value: HirExpr,
}

/// 当前 HIR 快照中与 TBC 精确配对的声明；借用原 value pack，不重新证明 SSA 或槽位身份。
#[derive(Debug, Clone, Copy)]
pub enum HirTbcDeclaration<'a> {
    Local {
        local: LocalId,
        declaration: &'a HirLocalDecl,
    },
    Temps {
        close_temp: TempId,
        assignment: &'a HirAssign,
    },
}

impl HirToBeClosed {
    /// 查询紧邻前句是否完整定义当前 TBC 绑定。调用方负责提供同块的前句；这里不推断 scope 终点。
    /// 例如 `t0, t1 = exact_call(); TBC t1` 包含整组 temp 声明，不能只声明最后一个资源。
    pub fn declaration<'a>(&self, previous: &'a HirStmt) -> Option<HirTbcDeclaration<'a>> {
        match (previous, &self.value) {
            (HirStmt::LocalDecl(declaration), HirExpr::LocalRef(local))
                if declaration.bindings.as_slice() == [*local] =>
            {
                Some(HirTbcDeclaration::Local {
                    local: *local,
                    declaration,
                })
            }
            (HirStmt::Assign(assignment), HirExpr::TempRef(temp))
                if assignment.values.exact_result_len() == Some(assignment.targets.len())
                    && assignment.targets.last() == Some(&HirLValue::Temp(*temp))
                    && assignment
                        .targets
                        .iter()
                        .all(|target| matches!(target, HirLValue::Temp(_))) =>
            {
                Some(HirTbcDeclaration::Temps {
                    close_temp: *temp,
                    assignment,
                })
            }
            _ => None,
        }
    }
}

/// HIR 中待词法化的实际清理事件；Structure 发布身份和执行位置，HIR 消费后才进入 AST。
#[derive(Debug, Clone, PartialEq)]
pub struct HirClose {
    /// 原始 cleanup 协议由 Transformer 生产，HIR 不再按槽位猜测 frame 返回边界。
    pub kind: crate::transformer::CloseKind,
    pub from_reg: usize,
    /// Structure 证明的、尚待词法 owner 消费的显式 TBC origin。作用域提交时逐项退休；
    /// 全部退休后删除事件。初始空集合只关闭普通 upvalue。
    pub origins: Vec<InstrRef>,
}

/// 返回语句。
///
#[derive(Debug, Clone, PartialEq)]
pub struct HirReturn {
    /// 尚待 HIR 消费的 frame cleanup 事务身份；严格配对的 cleanup 被消费时一起退休。
    /// 普通返回和前层已完成 cleanup 的返回没有此标记，不以诊断来源阻止语义合并。
    pub source_instr: Option<InstrRef>,
    pub values: HirValuePack,
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
    /// 针对这个 repeat 条件边界、在最终 HIR 上证明的生命周期事实。
    ///
    /// 这里只回答“哪些正文词法 binding 的 VM/HIR root 可以在执行条件前结束”；它不
    /// 授权删除或移动 definition。AST 仍须针对自己的具体候选证明词法作用域、属性和
    /// 控制流合法性。
    pub lifetime: HirRepeatConditionLifetimeFacts,
}

/// `repeat` 条件入口处可由 AST 消费的窄生命周期事实。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HirRepeatConditionLifetimeFacts {
    /// 在这个 repeat 的 condition 边界前结束，不会丢失原 VM/HIR 物理 root 的 binding。
    pub may_end_before_condition: BTreeSet<HirRepeatBinding>,
}

/// repeat 条件生命周期事实中的 HIR binding 身份。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HirRepeatBinding {
    Local(LocalId),
    Temp(TempId),
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
    pub iterator: HirValuePack,
    pub body: HirBlock,
    /// 原始 producer occurrence 与 semantic iterator span 的 owner-scoped 证书。
    /// SSA def、寄存器与指令 identity 已在 lowering 中消费；该证书只证明 ownership，
    /// 不授权 simplify 改写。
    pub initializer_transaction: Option<HirGenericForInitializerTransaction>,
    /// 该 owner 的一次性 ordinary initializer call operand 中，由 low CFG 与
    /// Promotion 共同证明必须继续物化到原 scope endpoint 的 physical roots。
    ///
    /// 这里只保存最终 HIR `TempId`，不把 SSA def 链、寄存器或相邻语句形状泄漏给
    /// simplify/AST；它与每轮隐式调用写 result home 的 `dispatch_results` 是独立事务。
    pub initializer_roots: Vec<TempId>,
    /// 每次隐式 iterator dispatch 都会写入的固定 VM result endpoint。
    ///
    /// `result_def` 是 Structure 已冻结的 `GenericForCall` fixed def 在 HIR 中的
    /// canonical identity；它只标识静态物理写入点，不代表各轮共享同一个动态值。
    /// 旧 result home 在调用 iterator 期间已经不属于 caller root prefix，而
    /// `success_binding` 只在首结果允许进入 body 的边上获得源码 binding 身份。
    pub dispatch_results: Vec<HirGenericForDispatchResult>,
}

impl HirGenericFor {
    /// 改写 iterator 时只撤销实际变化区间的 producer 证书。
    ///
    /// 每个 span 独立拥有固定的语义槽；改变 callee 不应丢弃另一段未变 nil producer。
    /// fixed 槽被删除、移动或改写时，该段须重新由 owner 证明，不能按新文本猜回协议。
    pub(crate) fn retain_unchanged_initializer_spans(&mut self, before: &HirValuePack) -> bool {
        let Some(transaction) = &mut self.initializer_transaction else {
            return false;
        };
        let count = transaction.producers.len();
        transaction.producers.retain(|span| {
            let range = span.value_start..span.value_start + span.value_count;
            before
                .fixed
                .get(range.clone())
                .is_some_and(|values| self.iterator.fixed.get(range) == Some(values))
        });
        let changed = transaction.producers.len() != count;
        if transaction.producers.is_empty() {
            self.initializer_transaction = None;
        }
        changed
    }

    /// 在 iterator 的局部改写边界统一维护 producer 身份，避免各 pass 丢弃整份证明。
    pub(crate) fn rewrite_iterator<R>(
        &mut self,
        rewrite: impl FnOnce(&mut HirValuePack) -> R,
    ) -> R {
        let before = self
            .initializer_transaction
            .as_ref()
            .map(|_| self.iterator.clone());
        let result = rewrite(&mut self.iterator);
        if let Some(before) = before {
            self.retain_unchanged_initializer_spans(&before);
        }
        result
    }
}

/// Generic-for 隐式 dispatch 的一个固定 result endpoint。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HirGenericForDispatchResult {
    pub result_def: TempId,
    pub success_binding: LocalId,
}

/// goto 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirGoto {
    pub target: HirLabelId,
}

/// label 语句。
#[derive(Debug, Clone, PartialEq)]
pub struct HirLabel {
    /// 跳转到该 label 时跨过的真实 cleanup origins；不等同于 must-active barrier 的补集。
    pub entry_cleanup: Vec<InstrRef>,
    pub id: HirLabelId,
    /// Structure 在目标 block 冻结的活跃 TBC 声明。
    pub tbc_barriers: Vec<InstrRef>,
}

/// 表构造器。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirTableConstructor {
    pub fields: Vec<HirTableField>,
    pub trailing_multivalue: Option<HirPackTail>,
    /// 前层发布的分配语义；模板默认值已进入 fields，但复制布局与普通预分配不同。
    pub allocation: HirTableAllocation,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum HirTableAllocation {
    /// HIR 自行生成的 capture 数组盒，没有原始 VM 表分配。
    #[default]
    Synthetic,
    /// Luau NEWTABLE 的精确预分配，与模板复制保持区别。
    Luau(crate::value_semantics::table::allocation::TablePreallocation),
    /// DUPTABLE 的原始有序键身份，不能由吸收后续写入的字段重新推算。
    LuauTemplate {
        hash_keys: std::sync::Arc<[crate::value_semantics::table::TableTemplateKey]>,
    },
    PucBatched(crate::value_semantics::table::allocation::TablePreallocation),
    Indexed {
        array_capacity: u32,
        hash_bits: u8,
    },
    Template {
        /// 包含索引 0；零槽与仅有索引 0 的模板必须区分。
        array_slots: u32,
        /// 含 nil marker 的原始 hash 键集合；普通字段写入不能增添模板键。
        hash_keys: std::sync::Arc<[crate::value_semantics::table::TableTemplateKey]>,
    },
}

impl HirTableAllocation {
    /// Luau 的纯 hash NEWTABLE 必须保留 bracket 字段；裸名字可能启用数组或模板预分配。
    /// 例如 `{["a"]=x,[1]=y}` 与 `{a=x,[1]=y}` 的容量不同，键值相同不足以证明等价。
    pub(crate) fn permits_named_record_keys(&self) -> bool {
        !matches!(self, Self::Luau(allocation) if allocation.array_capacity == 0)
    }

    /// 完成后的候选字段数是否复现批次预分配；None 表示该分配使用其它协议。
    /// 增量扫描的未完成前缀不能用此查询代替完整构造区域证明。
    pub(crate) fn batched_capacity_matches(&self, arrays: usize, records: usize) -> Option<bool> {
        match self {
            Self::PucBatched(allocation) => Some(allocation.matches(arrays, records)),
            _ => None,
        }
    }

    /// 原模板对新增 record 键的许可；不代替容量、求值顺序和根生命周期证明。
    /// Luau 模板扩大后，即使最终键值相同，也可能改变后续 pairs 顺序。
    pub(crate) fn permits_record_key(
        &self,
        key: Option<crate::value_semantics::table::TableTemplateKey>,
    ) -> bool {
        match self {
            Self::LuauTemplate { hash_keys } => key.is_some_and(|key| hash_keys.contains(&key)),
            _ => true,
        }
    }

    /// 原分配约束候选的模板初始化；已有模板也不能因新常量而扩大数组。
    pub(crate) fn initialization_constraint(
        &self,
    ) -> Option<crate::value_semantics::table::TableInitializationConstraint<'_>> {
        use crate::value_semantics::table::TableInitializationConstraint;
        match self {
            Self::Indexed {
                array_capacity: 1..,
                ..
            } => Some(TableInitializationConstraint::Runtime),
            Self::Template {
                array_slots,
                hash_keys,
            } => Some(TableInitializationConstraint::Template {
                array_slots: *array_slots,
                hash_keys,
            }),
            _ => None,
        }
    }

    pub(in crate::hir) fn indexed_array_capacity(&self) -> Option<u32> {
        match self {
            Self::Synthetic | Self::Luau(_) | Self::LuauTemplate { .. } | Self::PucBatched(_) => {
                None
            }
            Self::Indexed { array_capacity, .. } => Some(*array_capacity),
            Self::Template { array_slots, .. } => Some(array_slots.saturating_sub(1)),
        }
    }
}

impl HirTableConstructor {
    /// 比较候选与原 NEWTABLE 的完整预分配；PUC 不因此获得 indexed 写入协议的许可。
    pub(in crate::hir) fn matches_allocation_capacity(&self, array_fields: usize) -> bool {
        self.allocation
            .batched_capacity_matches(array_fields, self.fields.len() - array_fields)
            .unwrap_or_else(|| self.matches_indexed_array_capacity(array_fields))
    }

    /// 完整字段数能否重现索引式构造器的数组预分配（含 VM 最小/饱和容量规则）。
    /// 这里只检查容量；调用者另证字段均为顺序数组索引且求值/写入顺序不变。
    pub(in crate::hir) fn matches_indexed_array_capacity(&self, count: usize) -> bool {
        let Some(capacity) = self.allocation.indexed_array_capacity() else {
            return false;
        };
        if matches!(self.allocation, HirTableAllocation::Template { .. }) {
            return crate::hir::table_layout::candidate_template_array_capacity(self, count)
                == Some(capacity);
        }
        let count = count + usize::from(self.trailing_multivalue.is_some());
        let generated = if count == 0 {
            0
        } else if count >= 2046 {
            2048
        } else {
            count.max(2) as u32
        };
        let records = self
            .fields
            .iter()
            .filter(|field| {
                matches!(field,
            HirTableField::Record(record) if record.key != HirExpr::Integer(0))
            })
            .count();
        let HirTableAllocation::Indexed { hash_bits, .. } = self.allocation else {
            unreachable!()
        };
        capacity == generated && hash_bits == indexed_hash_bits(records)
    }
}

pub(in crate::hir) fn indexed_hash_bits(entries: usize) -> u8 {
    if entries == 0 {
        0
    } else {
        (usize::BITS - (entries - 1).leading_zeros()).max(1) as u8
    }
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
    /// 字段键的语义表达式；是否能写成 `name = value` 由目标 AST 方言决定。
    pub key: HirExpr,
    pub value: HirExpr,
}

/// 闭包表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct HirClosureExpr {
    pub proto: HirProtoRef,
    pub captures: Vec<HirCapture>,
}

/// 闭包捕获父级值的方式。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum HirCaptureMode {
    /// 创建闭包时保存当前值，不与父级寄存器的后续复用共享写入。
    ByValue,
    /// 捕获父级词法绑定，后续写入仍可由闭包观察。
    ByReference,
}

/// 当前 proto 的词法绑定身份，供捕获、对象流与后层命名共享。
///
/// 闭包捕获引用创建点的父 proto，不能承载待求值的复合表达式。
/// lowering 消费寄存器与 upvalue 的绑定事实后确定身份，后续 pass 只能做已证明的
/// 身份改写。例如 `local x; return function() return x end` 捕获的是父级 Local，
/// 即使 x 的初始值为 nil，也不能把这个 cell 换成 Nil 表达式。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum HirBinding {
    Param(ParamId),
    Local(LocalId),
    Temp(TempId),
    Upvalue(UpvalueId),
}

impl HirBinding {
    /// 为读取、对象流及 visitor 投影一次父级引用，不展开绑定定义或子 proto。
    pub const fn expr(self) -> HirExpr {
        match self {
            Self::Param(id) => HirExpr::ParamRef(id),
            Self::Local(id) => HirExpr::LocalRef(id),
            Self::Temp(id) => HirExpr::TempRef(id),
            Self::Upvalue(id) => HirExpr::UpvalueRef(id),
        }
    }

    pub(crate) fn from_expr(expr: &HirExpr) -> Option<Self> {
        match *expr {
            HirExpr::ParamRef(id) => Some(Self::Param(id)),
            HirExpr::LocalRef(id) => Some(Self::Local(id)),
            HirExpr::TempRef(id) => Some(Self::Temp(id)),
            HirExpr::UpvalueRef(id) => Some(Self::Upvalue(id)),
            _ => None,
        }
    }
}

/// 父级绑定与捕获方式独立保存；ByValue 读取快照，ByReference 保留可写 cell。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct HirCapture {
    pub mode: HirCaptureMode,
    pub binding: HirBinding,
}

/// 未解析表达式。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HirUnresolvedExpr {
    pub summary: String,
}
