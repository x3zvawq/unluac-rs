//! AST 层共享的目标方言语法节点。
//!
//! 承接 HIR 已确定的结构，并保留 Readability 所需的来源事实和宿主字面量配置。

use std::collections::BTreeSet;

use crate::LuaString;
use crate::decompile::DecompileDialect;
use crate::hir::{
    HirCallRootHandoff, HirInitializerMergeTransactionId, HirInitializerRootProfile,
    HirInlineDisposition, HirLabelId, HirMethodRewriteTransactionId, HirProtoRef,
    HirRepeatConditionLifetimeFacts, LocalId, ParamId, TempId, UpvalueId,
};
use strum_macros::{Display, IntoStaticStr};

/// 已物化的局部绑定身份；来源与可读性阶段分开，不借编号推断 HIR provenance。
/// 例如 HirTemp(0) 和 Ast(0) 可以共存，后者不能查询前者的 capture、debug 或生命周期事实。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstSyntheticLocalId {
    /// 原 HIR temp，仍属于对应函数的 TempId 域。
    HirTemp(TempId),
    /// AST 模块分配的独立身份，不对应任何 HIR temp。
    Ast(usize),
}

impl AstSyntheticLocalId {
    /// 仅供名字候选与诊断显示；不同来源的同号身份并不相等。
    pub const fn index(self) -> usize {
        match self {
            Self::HirTemp(temp) => temp.index(),
            Self::Ast(index) => index,
        }
    }
}

/// AST 根对象。
#[derive(Debug, Clone, PartialEq, Default)]
pub struct AstModule {
    pub entry_function: HirProtoRef,
    pub body: AstBlock,
    /// 随完整 AST 快照保存分配进度；跨 block、child 和 readability 轮次不复用身份。
    pub(crate) next_synthetic_local: usize,
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
    /// 宽松模式下无法恢复的语句占位。
    Error(String),
}

impl AstStmt {
    /// 本语句向所在块引入的 local；for 的绑定属于子域，不能参与父块的结束边界。
    pub(crate) fn local_bindings(&self) -> impl Iterator<Item = AstLocalBindingView<'_>> {
        let (locals, function): (&[AstLocalBinding], Option<&AstLocalFunctionDecl>) = match self {
            Self::LocalDecl(decl) => (&decl.bindings, None),
            Self::LocalFunctionDecl(decl) => (&[], Some(decl)),
            _ => (&[], None),
        };
        locals
            .iter()
            .map(AstLocalBindingView::from)
            .chain(function.map(|decl| AstLocalBindingView {
                id: decl.name,
                attr: AstLocalAttr::None,
                origin: decl.origin,
                rewrite_authority: &decl.rewrite_authority,
            }))
    }
}

/// AST 表达式。
#[derive(Debug, Clone, PartialEq)]
pub enum AstExpr {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    /// 原捕获初始化事务的不可折叠源码形式，直到发射仍与普通 literal 区分。
    CaptureInitializer(crate::hir::HirCaptureInitializer),
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
    /// HIR 已证明的 Luau 全局原地更新；values 保留完整读取与运算，供分析访问。
    pub(crate) luau_compound_global: bool,
    pub targets: Vec<AstLValue>,
    pub values: Vec<AstExpr>,
    /// 从 HIR 原样传入的、仅供相邻 initializer merge 消费的一次性 token。
    pub initializer_merge_transaction: Option<HirInitializerMergeTransactionId>,
    /// 从 HIR 原样传入的 method setup 原子改写事务。
    pub(crate) method_rewrite_transaction: Option<HirMethodRewriteTransactionId>,
}

impl AstAssign {
    /// 只检查 HIR 证书的剩余语法形状，不从同名读写重新推断复合更新许可。
    pub(crate) fn compound_global_binary(&self) -> Option<&AstBinaryExpr> {
        let ([AstLValue::Name(AstNameRef::Global(target))], [AstExpr::Binary(binary)]) =
            (self.targets.as_slice(), self.values.as_slice())
        else {
            return None;
        };
        (self.luau_compound_global
            && matches!(&binary.lhs, AstExpr::Var(AstNameRef::Global(input)) if input == target)
            && matches!(
                binary.op,
                AstBinaryOpKind::Add
                    | AstBinaryOpKind::Sub
                    | AstBinaryOpKind::Mul
                    | AstBinaryOpKind::Div
                    | AstBinaryOpKind::Mod
                    | AstBinaryOpKind::Pow
            ))
        .then_some(binary)
    }
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
    SyntheticLocal(AstSyntheticLocalId),
    Upvalue(UpvalueId),
    /// PUC Lua 5.2+ 的词法环境绑定；生成文本固定为 `_ENV`，但它不是普通 global。
    Environment,
    Global(AstGlobalName),
}

/// 可在 `local` 中声明的 binding。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstBindingRef {
    Local(LocalId),
    Temp(TempId),
    SyntheticLocal(AstSyntheticLocalId),
}

impl AstBindingRef {
    pub fn from_name_ref(name: &AstNameRef) -> Option<Self> {
        match name {
            AstNameRef::Local(local) => Some(Self::Local(*local)),
            AstNameRef::Temp(temp) => Some(Self::Temp(*temp)),
            AstNameRef::SyntheticLocal(local) => Some(Self::SyntheticLocal(*local)),
            AstNameRef::Param(_)
            | AstNameRef::Upvalue(_)
            | AstNameRef::Environment
            | AstNameRef::Global(_) => None,
        }
    }

    pub fn to_name_ref(self) -> AstNameRef {
        match self {
            Self::Local(local) => AstNameRef::Local(local),
            Self::Temp(temp) => AstNameRef::Temp(temp),
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
    pub creation: Option<crate::hir::HirClosureCreation>,
    pub function: HirProtoRef,
    pub params: Vec<ParamId>,
    /// HIR 参数身份允许首参命名为 self，且没有待命名的非环境 upvalue 与它冲突。
    /// 这不是原始冒号声明的证明；readability 仍需检查当前函数及后代的自由 self。
    pub(crate) allows_self_param: bool,
    pub is_vararg: bool,
    pub named_vararg: Option<AstBindingRef>,
    pub body: AstBlock,
    /// 这份集合只记录“闭包初始化时显式 capture 了哪些当前词法绑定”。
    ///
    /// 它不是源码语法的一部分，而是给 readability 提供结构事实：
    /// 如果一个函数值仍然依赖某个局部槽位，就不能把那个槽位前推消掉，
    /// 否则像递归 local function 这种形状会失去可见声明。
    pub captured_bindings: BTreeSet<AstBindingRef>,
    /// 同上，但记录被闭包捕获的当前函数参数。
    pub captured_params: BTreeSet<ParamId>,
    /// 当前闭包或其后代可能通过 by-reference capture 写入的父级名字。
    ///
    /// 这是 `captured_bindings` / `captured_params` 的写入子集；只读或 by-value capture
    /// 仍保留在前两者中供词法身份与存活分析使用，但不构成可变快照。
    pub capture_write_names: BTreeSet<AstNameRef>,
}

/// 顶层/表字段函数声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstFunctionDecl {
    pub target: AstFunctionName,
    /// 来自显式 global 声明；普通 `function name()` 仍是赋值，不能打开 global 词法域。
    pub global_declaration: bool,
    pub func: AstFunctionExpr,
}

/// `local function` 声明。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLocalFunctionDecl {
    pub name: AstBindingRef,
    pub origin: AstLocalOrigin,
    pub rewrite_authority: AstRewriteAuthority,
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
        let caps = match version {
            DecompileDialect::Auto => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            DecompileDialect::Lua51 => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            DecompileDialect::Lua52 | DecompileDialect::Lua53 => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            DecompileDialect::Lua54 => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: true,
                local_close: true,
                global_decl: false,
                global_const: false,
            },
            DecompileDialect::Lua55 => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: true,
                local_close: true,
                global_decl: true,
                global_const: true,
            },
            DecompileDialect::Luajit => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
            DecompileDialect::Luau => AstDialectCaps {
                goto_label: control.goto_label,
                continue_stmt: control.continue_stmt,
                if_expr: matches!(version, DecompileDialect::Luau),
                local_const: false,
                local_close: false,
                global_decl: false,
                global_const: false,
            },
        };
        Self { version, caps }
    }

    pub const fn diagnostic_for_lowering(version: DecompileDialect) -> Self {
        let mut target = Self::new(version);
        target.caps.goto_label = true;
        target
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
    /// 从 HIR 原样传入的、仅供相邻 initializer merge 消费的一次性 token。
    pub initializer_merge_transaction: Option<HirInitializerMergeTransactionId>,
    /// HIR value-pack 对每个 initializer 结果槽发布的 root 类别。AST 只消费该事实
    /// 判断自己的 scope rewrite；任何改变 bindings/values 对应关系的改写必须清空它。
    pub(crate) initializer_root_profile: Option<HirInitializerRootProfile>,
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
    pub origin: AstLocalOrigin,
    /// 谁拥有删除、移动或缩短这个 binding 的语义判定。
    ///
    /// HIR 结论与 `origin` 正交：前者约束重写权限，后者只描述 debug/root 来源。
    pub rewrite_authority: AstRewriteAuthority,
}

/// 声明的借用事实视图；`local function` 直接提供自己的身份与权限，不伪造 local 声明。
/// 视图只在原语句快照存活期间有效，例如尾 do 的生命周期索引无需复制 HIR Preserve 原因集。
#[derive(Clone, Copy)]
pub(crate) struct AstLocalBindingView<'a> {
    pub id: AstBindingRef,
    pub attr: AstLocalAttr,
    pub origin: AstLocalOrigin,
    pub rewrite_authority: &'a AstRewriteAuthority,
}

impl<'a> From<&'a AstLocalBinding> for AstLocalBindingView<'a> {
    fn from(binding: &'a AstLocalBinding) -> Self {
        Self {
            id: binding.id,
            attr: binding.attr,
            origin: binding.origin,
            rewrite_authority: &binding.rewrite_authority,
        }
    }
}

/// AST 对 binding 进行生命周期改写时必须服从的上游权限。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AstRewriteAuthority {
    /// binding 由 AST readability 自己创建，语义判断也由 AST 拥有。
    AstOwned,
    /// binding 来自 HIR；当前携带负向结论或仍未迁移的显式 Unknown。
    Hir(HirInlineDisposition),
}

impl AstRewriteAuthority {
    pub const fn must_preserve(&self) -> bool {
        matches!(self, Self::Hir(disposition) if disposition.must_preserve())
    }

    pub const fn may_remove_binding(&self) -> bool {
        !self.must_preserve()
    }

    pub const fn may_move_scope_start(&self) -> bool {
        !self.must_preserve()
    }

    /// 直接函数初始化只改变声明语法，保留同一 binding、原分配槽和初始化事件。
    /// 函数体的显式 capture 身份仍由 AST build/命名维护，不许可吸收转发壳或删声明。
    pub fn may_use_local_function_syntax(&self) -> bool {
        self.may_move_scope_start()
            || matches!(self, Self::Hir(HirInlineDisposition::Preserve(reasons))
                if reasons.iter().all(|reason| *reason == crate::hir::HirInlineRetentionReason::PhysicalFramePrefix))
    }

    /// 无求值事件的空声明或基本字面量声明相邻合并，保持每个槽的原写与完整前缀。
    /// 调用方核对 RHS 类别，其它 HIR 保留理由及 debug/属性限制仍独立检查。
    pub fn may_merge_adjacent_inert_declarations(&self) -> bool {
        self.may_move_scope_start()
            || matches!(self, Self::Hir(HirInlineDisposition::Preserve(reasons))
                if reasons.iter().all(|reason| *reason == crate::hir::HirInlineRetentionReason::PhysicalFramePrefix))
    }

    /// 普通父块的尾 do 合并不移动初始化或声明槽，也不改变共同退出时点。
    /// 调用方必须排除 repeat 尾条件与 debug 可见边界，不能用于一般 scope-start 移动。
    pub fn may_merge_tail_scope(&self) -> bool {
        !self.must_preserve()
            || matches!(self, Self::Hir(HirInlineDisposition::Preserve(reasons))
                if reasons.iter().all(|reason| *reason == crate::hir::HirInlineRetentionReason::PhysicalFramePrefix))
    }

    pub const fn may_shorten_lifetime(&self) -> bool {
        !self.must_preserve()
    }
}

/// `global` binding。
#[derive(Debug, Clone, PartialEq)]
pub struct AstGlobalBinding {
    pub target: AstGlobalBindingTarget,
    pub attr: AstGlobalAttr,
}

/// `global` 声明的绑定目标。
///
/// 这里显式区分普通全局名和 `global *` wildcard，是为了避免把 `*` 塞成一个伪名字。
/// 后续 Generate 只需要按这个稳定结构输出，不需要再猜测当前 binding 到底是不是 wildcard。
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

/// 局部绑定在进入 AST 时的来源。
///
/// 这里不是为了精确复刻 parser 的原始局部声明，而是给 readability 一个稳定边界：
/// 带 parser debug 影子的 local 更接近源码语义名，机械恢复出来的 local 则可以更积极
/// 地继续收回表达式。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AstLocalOrigin {
    Recovered,
    DebugHinted,
    /// HIR proved a physical VM-root lifetime that ordinary AST uses do not express.
    PhysicalRoot,
    /// The source debug identity and the physical VM root are independently observable.
    DebugHintedPhysicalRoot,
}

impl AstLocalOrigin {
    pub const fn is_debug_hinted(self) -> bool {
        matches!(self, Self::DebugHinted | Self::DebugHintedPhysicalRoot)
    }

    pub const fn is_physical_root(self) -> bool {
        matches!(self, Self::PhysicalRoot | Self::DebugHintedPhysicalRoot)
    }
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
    /// 原 NOT/取负等操作的保留义务，与其结果是否已知分开。
    pub(crate) original_operation: bool,
}

/// 二元表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstBinaryExpr {
    pub op: AstBinaryOpKind,
    pub lhs: AstExpr,
    pub rhs: AstExpr,
    /// 原字节码中的操作不能因操作数已知而删除；合成节点没有这项义务。
    pub(crate) original_operation: bool,
}

/// 逻辑表达式。
#[derive(Debug, Clone, PartialEq)]
pub struct AstLogicalExpr {
    pub lhs: AstExpr,
    pub rhs: AstExpr,
    /// HIR 已消费原 Boolean 预写；逻辑外壳负责重发该写，不能按值恒等式删除。
    pub(crate) preserves_boolean_prewrite: bool,
}

/// Luau 条件选值；只求值被选中的一臂，结果始终为单值。
#[derive(Debug, Clone, PartialEq)]
pub struct AstIfExpr {
    pub cond: AstExpr,
    pub then_expr: AstExpr,
    pub else_expr: AstExpr,
}

/// 普通调用。
#[derive(Debug, Clone, PartialEq)]
pub struct AstCallExpr {
    /// 保留 HIR 对该调用的必须内联要求；树化、复制后由 Generate 核对完整 occurrence 集。
    pub(crate) required_luau_inlining: Option<crate::hir::HirSourceSite>,
    pub callee: AstExpr,
    pub args: Vec<AstExpr>,
    /// HIR 已确认的 SELF/NAMECALL 原始字段 key。`Call` 形状仍保留这份
    /// provenance，即使 key 不是目标方言的 identifier，只能渲染成索引调用。
    pub method_key: Option<LuaString>,
    /// HIR 对这个调用 occurrence 发布的 callee 物理根交接证明。
    pub(crate) callee_root_handoff: Option<HirCallRootHandoff>,
    /// 与 method lookup assignment 配对的一次性 HIR 改写事务。
    pub(crate) method_rewrite_transaction: Option<HirMethodRewriteTransactionId>,
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
    /// HIR 发布的初始化方式，约束后续常量替换；AST 不从字段猜原分配协议。
    pub allocation: crate::hir::HirTableAllocation,
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
    /// HIR 标记的原退化 TEST；即使条件已知或两臂为空也要保留检查。
    pub(crate) preserves_empty_test: bool,
    /// 宽常量池要求两臂保持已恢复的发射顺序，否则 RK 会改变临时槽覆盖。
    pub(crate) preserves_arm_order: bool,
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
    /// 条件承载原字节码检查；即使已知恒真，也不能按合成单次包装删除。
    pub preserves_condition: bool,
    /// HIR 在这个 repeat 的条件边界证明的物理生命周期事实。
    ///
    /// 集合里的 binding 只获准在“当前 repeat body -> condition”这一条边界提前结束；
    /// 它不是 binding 级通用 rewrite authority。AST 仍须针对实际 suffix 证明词法可见性、
    /// `<close>`、debug identity、global gate 与 goto 合法性。
    pub lifetime: HirRepeatConditionLifetimeFacts,
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

/// AST label 身份；前层 label 和本层语法化产生的 label 使用独立命名空间。
///
/// synthetic continue label 不需要扫描 HIR 最大编号，也不能与同号 HIR label 合并。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum AstLabelId {
    Hir(HirLabelId),
    Synthetic(usize),
}

impl std::fmt::Display for AstLabelId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Hir(id) => write!(f, "L{}", id.index()),
            Self::Synthetic(id) => write!(f, "C{id}"),
        }
    }
}

impl From<HirLabelId> for AstLabelId {
    fn from(value: HirLabelId) -> Self {
        Self::Hir(value)
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
    /// 原比较准备顺序要求左侧先求值，不能交换回 Lt。
    Gt,
    /// 原比较准备顺序要求左侧先求值，不能交换回 Le。
    Ge,
}
