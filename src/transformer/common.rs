//! 这个文件集中声明 transformer 层的统一 low-IR 类型。
//!
//! 之所以把这些定义收拢到一个 common 模块，是因为 low-IR 是后续 CFG、
//! Dataflow、HIR 共同依赖的稳定契约；具体某个 dialect 的 lowering 规则可以
//! 分目录演进，但这里的类型应该尽量保持统一、明确、可复用。

use std::{collections::BTreeMap, fmt, sync::Arc};

use super::debug_locals::DebugLocals;
pub(crate) use super::debug_locals::normalize_debug_locals;

use crate::parser::{
    ChunkHeader, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawConstPool,
    RawDebugInfo, RawProto, RawString, RawUpvalueInfo,
};

/// transformer 层的根对象，保留 chunk 级元数据和主 proto。
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredChunk {
    pub header: ChunkHeader,
    pub main: LoweredProto,
    pub origin: Origin,
}

/// 一个已经完成 dialect-specific lowering 的 proto。
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredProto {
    pub source: Option<RawString>,
    /// 方言直接记录的函数/debug name；当前主要来自 Luau proto debug table。
    pub debug_name: Option<RawString>,
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub frame: ProtoFrameInfo,
    pub constants: RawConstPool,
    pub upvalues: RawUpvalueInfo,
    /// 当前 proto 中由 VM 绑定为词法环境的 upvalue，按 upvalue 索引升序保存。
    ///
    /// 这是 PUC Lua 5.2+ 的 cell 身份，不等同于 Lua 5.1/LuaJIT/Luau 全局指令使用的
    /// 隐式环境 base；后层必须继续把它当作普通 upvalue identity 参与读写与 capture。
    pub environment_upvalues: Vec<UpvalueRef>,
    pub debug_info: RawDebugInfo,
    /// 已按方言协议归一到寄存器与生命周期的局部变量调试事实。
    pub debug_locals: DebugLocals,
    /// Lowered child templates are immutable.  `Arc` keeps closure instances cheap:
    /// creating a second closure from one child copies only the current proto
    /// payload and shares its descendants instead of recursively cloning a subtree.
    pub children: Vec<Arc<LoweredProto>>,
    pub instrs: Vec<LowInstr>,
    pub lowering_map: LoweringMap,
    pub origin: Origin,
}

/// 调试局部变量是否对应源码可见 binding。
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum DebugLocalKind {
    Source,
    CompilerInternal,
}

/// 一个已经从方言编码归一到 VM 寄存器的局部变量调试事实。
#[derive(Debug, Clone, PartialEq)]
pub struct DebugLocalFact {
    pub name: RawString,
    pub reg: Reg,
    /// 作用域首条原始指令执行前的位置；该指令的重绑定不属于 local 初始化。
    pub start_pc: u32,
    pub end_pc: u32,
    pub kind: DebugLocalKind,
}

impl DebugLocalFact {
    pub const fn is_source(&self) -> bool {
        matches!(self.kind, DebugLocalKind::Source)
    }

    pub const fn is_active_at(&self, pc: u32) -> bool {
        self.start_pc <= pc && pc < self.end_pc
    }
}

/// 基于 proto upvalue 描述符和父链传播结果，恢复当前 proto 哪些 upvalue 表示根环境。
///
/// debug 中名为 `_ENV` 的 upvalue 也可能捕获父函数的同名局部表；只有根 proto 的首个
/// upvalue 和子 proto 沿非 in-stack 描述符继承的身份，才能安全升级为裸 global 访问。
pub(crate) fn resolve_env_upvalues(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Vec<bool> {
    let count = usize::from(raw.common.upvalues.common.count);
    let descriptors = &raw.common.upvalues.common.descriptors;
    let mut env_upvalues = vec![false; count];

    if let Some(parent_env_upvalues) = parent_env_upvalues {
        for (index, descriptor) in descriptors.iter().enumerate() {
            if index >= count || descriptor.in_stack {
                continue;
            }
            if parent_env_upvalues
                .get(usize::from(descriptor.index))
                .copied()
                .unwrap_or(false)
            {
                env_upvalues[index] = true;
            }
        }
    } else if !env_upvalues.is_empty() {
        // Lua 5.2+ 根 proto 在 load 时会把第一个 upvalue 绑定到当前环境。
        env_upvalues[0] = true;
    }

    env_upvalues
}

/// low/raw/debug 之间的统一映射关系。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoweringMap {
    pub low_to_raw: Vec<Vec<RawInstrRef>>,
    pub raw_to_low: Vec<Vec<InstrRef>>,
    pc_map: Vec<Vec<u32>>,
    pc_frontier: Vec<(u32, InstrRef)>,
    pub line_hints: Vec<Option<u32>>,
}

impl LoweringMap {
    pub(super) fn new(
        low_to_raw: Vec<Vec<RawInstrRef>>,
        raw_to_low: Vec<Vec<InstrRef>>,
        pc_map: Vec<Vec<u32>>,
        line_hints: Vec<Option<u32>>,
    ) -> Self {
        // raw 来源可以多值、乱序或缺失；只有前缀最大 PC 首次提高的位置能成为查询答案。
        // 例如 [2], [1,5], [], [3] 对 PC=4 的最早 low 仍是第二项，不能二分原 pc_map。
        let mut pc_frontier = Vec::new();
        for (index, pcs) in pc_map.iter().enumerate() {
            if let Some(pc) = pcs.iter().copied().max()
                && pc_frontier
                    .last()
                    .is_none_or(|&(previous, _)| previous < pc)
            {
                pc_frontier.push((pc, InstrRef(index)));
            }
        }
        Self {
            low_to_raw,
            raw_to_low,
            pc_map,
            pc_frontier,
            line_hints,
        }
    }

    pub fn pc_map(&self) -> &[Vec<u32>] {
        &self.pc_map
    }

    /// 返回原始来源中含有 PC >= boundary 的最早 low 指令；没有后继指令时返回 None。
    /// 索引与映射由同一个 lowering 事务冻结，debug 消费者不重扫或假定 raw/low 单调对应。
    pub fn low_instr_at_or_after_pc(&self, boundary: u32) -> Option<InstrRef> {
        let position = self.pc_frontier.partition_point(|&(pc, _)| pc < boundary);
        self.pc_frontier.get(position).map(|&(_, instr)| instr)
    }
}

/// low-IR 指令的稳定索引。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InstrRef(pub usize);

impl InstrRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for InstrRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.0)
    }
}

/// raw 指令在线性 proto 指令数组里的稳定索引。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct RawInstrRef(pub usize);

impl RawInstrRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// VM 寄存器引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Reg(pub usize);

impl Reg {
    pub const fn index(self) -> usize {
        self.0
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

/// 一段连续寄存器区间。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct RegRange {
    pub start: Reg,
    pub len: usize,
}

impl RegRange {
    pub const fn new(start: Reg, len: usize) -> Self {
        Self { start, len }
    }
}

/// 当前 proto 常量池里的常量引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ConstRef(pub usize);

impl ConstRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 以 bit-pattern 保留的数值字面量。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct NumberLiteral(pub u64);

impl NumberLiteral {
    pub fn from_f64(value: f64) -> Self {
        Self(value.to_bits())
    }

    pub fn to_f64(self) -> f64 {
        f64::from_bits(self.0)
    }
}

/// 当前 proto upvalue 表里的引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct UpvalueRef(pub usize);

impl UpvalueRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 当前 proto 子 proto 表里的引用。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ProtoRef(pub usize);

impl ProtoRef {
    pub const fn index(self) -> usize {
        self.0
    }
}

/// 当前 proto 常量表中可复用的闭包对象身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct SharedClosureRef(pub usize);

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ClosureCreation {
    Fresh,
    Reusable(SharedClosureRef),
}

/// raw bytecode 原本就允许 RK 的位置，在 low-IR 里继续保留寄存器/常量二选一。
///
/// `Nil` / `Boolean` 主要服务于 LuaJIT 的立即数 upvalue 写入指令
/// (`USETP` / 形如 `local x = nil` / `local x = true`)：这些字节码并不会把
/// 字面量先放入常量池，而是直接通过 KPRI 立即数表达，因此 low-IR 在这里
/// 显式承载 nil/布尔，避免下游再去合成虚拟寄存器或假常量项。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ValueOperand {
    Reg(Reg),
    Const(ConstRef),
    Integer(i64),
    Nil,
    Boolean(bool),
}

/// 统一 low-IR 指令枚举。
#[derive(Debug, Clone, PartialEq)]
pub enum LowInstr {
    Move(MoveInstr),
    LoadNil(LoadNilInstr),
    LoadBool(LoadBoolInstr),
    LoadConst(LoadConstInstr),
    LoadInteger(LoadIntegerInstr),
    LoadNumber(LoadNumberInstr),
    UnaryOp(UnaryOpInstr),
    BinaryOp(BinaryOpInstr),
    Concat(ConcatInstr),
    GetUpvalue(GetUpvalueInstr),
    SetUpvalue(SetUpvalueInstr),
    GetTable(GetTableInstr),
    SetTable(SetTableInstr),
    ErrNil(ErrNilInstr),
    TypeGuard(TypeGuardInstr),
    NewTable(NewTableInstr),
    SetList(SetListInstr),
    Call(CallInstr),
    TailCall(TailCallInstr),
    VarArg(VarArgInstr),
    Return(ReturnInstr),
    Closure(ClosureInstr),
    Close(CloseInstr),
    Tbc(TbcInstr),
    NumericForInit(NumericForInitInstr),
    NumericForLoop(NumericForLoopInstr),
    GenericForPrep(GenericForPrepInstr),
    GenericForCall(GenericForCallInstr),
    GenericForLoop(GenericForLoopInstr),
    Jump(JumpInstr),
    Branch(BranchInstr),
}

impl LowInstr {
    pub fn is_control_terminator(&self) -> bool {
        matches!(
            self,
            Self::Jump(_)
                | Self::Branch(_)
                | Self::Return(_)
                | Self::TailCall(_)
                | Self::NumericForInit(_)
                | Self::NumericForLoop(_)
                | Self::GenericForLoop(_)
        )
    }
}

/// 一元运算种类。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UnaryOpKind {
    Not,
    Neg,
    BitNot,
    Length,
}

/// 二元运算种类。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BinaryOpKind {
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
}

/// Luau FASTCALL 参数是否由当前调用直接物化。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum FastCallArgs {
    All,
    Mask { direct_fixed: u8, direct_tail: bool },
}

impl FastCallArgs {
    pub const fn fixed_is_direct(self, index: usize) -> bool {
        match self {
            Self::All => true,
            Self::Mask { direct_fixed, .. } => {
                index < u8::BITS as usize && direct_fixed & (1 << index) != 0
            }
        }
    }

    pub const fn tail_is_direct(self) -> bool {
        match self {
            Self::All => true,
            Self::Mask { direct_tail, .. } => direct_tail,
        }
    }
}

/// 调用形态，区分普通调用、方法糖与 Luau fastcall fallback 协议。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CallKind {
    Normal,
    Method,
    FastCall(FastCallArgs),
}

/// 方言 method setup 协议在 low-IR 上携带的 method 名提示。
///
/// 这里只保留“常量池里的字段名索引”，避免在 transformer 层过早解码字符串；
/// 到 HIR / AST 再按各层自己的字符串语义恢复。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct MethodNameHint {
    pub const_ref: ConstRef,
}

/// 参数值包。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ValuePack {
    Fixed(RegRange),
    Open(Reg),
}

/// 结果值包。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ResultPack {
    Fixed(RegRange),
    Open(Reg),
    Ignore,
}

/// 表访问的 base。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum AccessBase {
    Reg(Reg),
    /// 没有源码级词法 upvalue 身份的隐式全局环境。
    Env,
    /// PUC Lua 5.2+ 由真实 upvalue cell 承载的词法环境。
    EnvironmentUpvalue(UpvalueRef),
    Upvalue(UpvalueRef),
}

/// 上值读写的语义目标。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UpvalueOperand {
    Env(UpvalueRef),
    Upvalue(UpvalueRef),
}

impl From<UpvalueRef> for UpvalueOperand {
    fn from(upvalue: UpvalueRef) -> Self {
        Self::Upvalue(upvalue)
    }
}

/// 表访问的 key。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum AccessKey {
    Reg(Reg),
    Const(ConstRef),
    Integer(i64),
}

/// 闭包 capture 来源。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CaptureSource {
    /// 创建闭包时复制寄存器当前值，后续复用该寄存器不会更新 upvalue。
    ByValue(Reg),
    /// 捕获寄存器对应的可写词法槽位。
    ByReference(Reg),
    Upvalue(UpvalueRef),
}

/// 一个闭包捕获项。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Capture {
    pub source: CaptureSource,
}

/// 条件跳转的谓词。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BranchPredicate {
    Eq,
    Lt,
    Le,
}

/// 条件操作数。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CondOperand {
    Reg(Reg),
    Const(ConstRef),
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(NumberLiteral),
}

/// 条件的完整语义本体；truthiness 与二元比较在类型层互斥。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BranchSubject {
    Truthy(CondOperand),
    Compare {
        predicate: BranchPredicate,
        lhs: CondOperand,
        rhs: CondOperand,
    },
}

/// 无副作用条件本体。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BranchCond {
    pub subject: BranchSubject,
    pub negated: bool,
}

impl BranchCond {
    pub const fn truthy(operand: CondOperand, negated: bool) -> Self {
        Self {
            subject: BranchSubject::Truthy(operand),
            negated,
        }
    }

    pub const fn compare(
        predicate: BranchPredicate,
        lhs: CondOperand,
        rhs: CondOperand,
        negated: bool,
    ) -> Self {
        Self {
            subject: BranchSubject::Compare {
                predicate,
                lhs,
                rhs,
            },
            negated,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct MoveInstr {
    pub dst: Reg,
    pub src: Reg,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct LoadNilInstr {
    pub dst: RegRange,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct LoadBoolInstr {
    pub dst: Reg,
    pub value: bool,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct LoadConstInstr {
    pub dst: Reg,
    pub value: ConstRef,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LoadIntegerInstr {
    pub dst: Reg,
    pub value: i64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LoadNumberInstr {
    pub dst: Reg,
    pub value: f64,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct UnaryOpInstr {
    pub dst: Reg,
    pub op: UnaryOpKind,
    pub src: Reg,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BinaryOpInstr {
    pub dst: Reg,
    pub op: BinaryOpKind,
    pub lhs: ValueOperand,
    pub rhs: ValueOperand,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ConcatInstr {
    pub dst: Reg,
    pub src: RegRange,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GetUpvalueInstr {
    pub dst: Reg,
    pub src: UpvalueOperand,
}

/// 上值写入。
///
/// LuaJIT 把"给上值赋值"按 RHS 形态拆成了 `USETV/USETS/USETN/USETP` 四个指令，
/// 分别对应寄存器 / 字符串常量 / 数值常量 / KPRI 原语；puc-lua 系列则只发寄存器
/// 形态的 `SETUPVAL`。这里把 `src` 升格为 `ValueOperand`，让 LuaJIT 的常量直写
/// 形态可以无损落到同一条 low-IR 上，下游统一通过 `expr_for_value_operand`
/// 还原表达式即可，避免在 lowering 里临时凑寄存器。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SetUpvalueInstr {
    pub dst: UpvalueOperand,
    pub src: ValueOperand,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GetTableInstr {
    pub dst: Reg,
    pub base: AccessBase,
    pub key: AccessKey,
    pub kind: GetTableKind,
}

/// 表读取在源字节码中的协议身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum GetTableKind {
    Normal,
    /// LuaJIT `TGETR` 的 raw integer-key 读取，不触发 `__index`。
    Raw,
    /// Luau `GETIMPORT` 展开的稳定路径读取。
    Import,
    /// 来自方言 method setup 协议的 method-load。
    ///
    /// Lua 的 `obj:name(args)` 会由 `SELF` / `NAMECALL` 单指令，或 LuaJIT 的 split
    /// `MOV + TGETS/TGETV` 展开成 receiver snapshot、method lookup 和 CALL。
    /// `CallInstr.method_name` 保存可读性事实，
    /// 但 GetTable 仍是会触发 `__index` 的真实求值事件；该标志只描述 setup 协议，不能
    /// 作为删除或跨参数副作用移动 lookup 的依据。
    Method,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SetTableInstr {
    pub base: AccessBase,
    pub key: AccessKey,
    pub value: ValueOperand,
    pub kind: SetTableKind,
}

/// 表写入在源字节码中的协议身份。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SetTableKind {
    Normal,
    /// LuaJIT `TSETR` 的 raw integer-key 写入，不触发 `__newindex`。
    Raw,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ErrNilInstr {
    pub subject: Reg,
    pub name: Option<ConstRef>,
}

/// VM 内建函数的参数类型守卫。
///
/// 这类指令会在类型不匹配时抛出参数错误，部分种类还会原地做 LuaJIT 隐式转换；
/// 统一 IR 保留这条不可丢弃的语义边界，不把它伪装成普通条件分支。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TypeGuardInstr {
    pub subject: Reg,
    pub kind: TypeGuardKind,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum TypeGuardKind {
    String,
    Function,
    Table,
    Integer,
    Number,
}

impl TypeGuardKind {
    pub const fn label(self) -> &'static str {
        match self {
            Self::String => "string",
            Self::Function => "function",
            Self::Table => "table",
            Self::Integer => "integer",
            Self::Number => "number",
        }
    }

    /// 成功路径会把参数槽规范化成目标类型；后续读取必须使用 guard 之后的 SSA 值。
    pub const fn normalizes_subject(self) -> bool {
        matches!(self, Self::String | Self::Integer | Self::Number)
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct NewTableInstr {
    pub dst: Reg,
    pub allocation: TableAllocation,
}

/// 分配与初始化是一条 VM 事件。模板里的 nil 槽和 hash key 是初始布局事实，
/// 不能展开为有独立求值/观察语义的普通 SetTable 再让后层恢复。
#[derive(Debug, Clone, Default, Eq, PartialEq, Hash)]
pub enum TableAllocation {
    #[default]
    Empty,
    /// 正整数数组槽数，不含 VM 的索引 0。
    Indexed {
        array_capacity: u32,
        hash_bits: u8,
    },
    Template(TableTemplate),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TableTemplate {
    /// 包含索引 0；每个元素均引用本 proto 的常量池。
    pub array: Vec<ConstRef>,
    /// 包含 nil-valued 预置项，保留模板键集合。
    pub hash: Vec<(ConstRef, ConstRef)>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SetListInstr {
    pub base: Reg,
    pub values: ValuePack,
    pub start_index: u32,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CallInstr {
    pub callee: Reg,
    pub args: ValuePack,
    pub results: ResultPack,
    pub kind: CallKind,
    pub method_name: Option<MethodNameHint>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TailCallInstr {
    pub callee: Reg,
    pub args: ValuePack,
    pub kind: CallKind,
    pub method_name: Option<MethodNameHint>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct VarArgInstr {
    pub results: ResultPack,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ReturnInstr {
    pub values: ValuePack,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClosureInstr {
    pub dst: Reg,
    pub proto: ProtoRef,
    pub captures: Vec<Capture>,
    pub creation: ClosureCreation,
}

pub(crate) fn instantiate_closure_children(
    instrs: &mut [LowInstr],
    children: Vec<Arc<LoweredProto>>,
) -> Vec<Arc<LoweredProto>> {
    let mut instances = children;
    let mut claimed = vec![false; instances.len()];
    let mut shared_instances = BTreeMap::new();

    for closure in instrs.iter_mut().filter_map(|instr| match instr {
        LowInstr::Closure(closure) => Some(closure),
        _ => None,
    }) {
        let source = closure.proto.index();
        closure.proto = match closure.creation {
            ClosureCreation::Fresh => {
                instantiate_closure_child(source, &mut claimed, &mut instances)
            }
            ClosureCreation::Reusable(shared) => *shared_instances
                .entry(shared)
                .or_insert_with(|| instantiate_closure_child(source, &mut claimed, &mut instances)),
        };
    }

    instances
}

fn instantiate_closure_child(
    source: usize,
    claimed: &mut [bool],
    instances: &mut Vec<Arc<LoweredProto>>,
) -> ProtoRef {
    if !std::mem::replace(&mut claimed[source], true) {
        return ProtoRef(source);
    }
    let instance = ProtoRef(instances.len());
    instances.push(Arc::clone(&instances[source]));
    instance
}

/// cleanup 的原始执行协议；不能根据零槽或与 Return 的邻接关系重新推断。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CloseKind {
    /// 独立 CLOSE / JMP-close 操作，后续求值必须发生在关闭之后。
    Explicit,
    /// 同一返回指令的 frame cleanup；返回结果已由 VM 返回协议承接。
    Return(InstrRef),
    /// 同一尾调用关闭旧 frame 的 upvalue；受支持 Lua 的此路径没有待关闭 TBC。
    TailCall(InstrRef),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CloseInstr {
    pub kind: CloseKind,
    pub from: Reg,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TbcInstr {
    pub reg: Reg,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct NumericForInitInstr {
    pub index: Reg,
    pub limit: Reg,
    pub step: Reg,
    pub binding: Reg,
    pub body_target: InstrRef,
    pub exit_target: InstrRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct NumericForLoopInstr {
    pub index: Reg,
    pub limit: Reg,
    pub step: Reg,
    pub binding: Reg,
    pub body_target: InstrRef,
    pub exit_target: InstrRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GenericForPrepInstr {
    pub iterator: Reg,
    pub state: Reg,
    pub control_source: Reg,
    pub closing_source: Reg,
    pub control_target: Reg,
    pub closing_target: Reg,
}

impl GenericForPrepInstr {
    pub(crate) fn source_for_target(self, target: Reg) -> Option<Reg> {
        match target {
            target if target == self.control_target => Some(self.control_source),
            target if target == self.closing_target => Some(self.closing_source),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GenericForCallInstr {
    pub iterator: Reg,
    pub state: Reg,
    pub control: Reg,
    pub results: ResultPack,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GenericForLoopInstr {
    pub control_target: Reg,
    pub bindings: RegRange,
    pub body_target: InstrRef,
    pub exit_target: InstrRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct JumpInstr {
    pub target: InstrRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BranchInstr {
    pub cond: BranchCond,
    pub then_target: InstrRef,
    pub else_target: InstrRef,
}
