//! 这个文件集中声明 transformer 层的统一 low-IR 类型。
//!
//! 之所以把这些定义收拢到一个 common 模块，是因为 low-IR 是后续 CFG、
//! Dataflow、HIR 共同依赖的稳定契约；具体某个 dialect 的 lowering 规则可以
//! 分目录演进，但这里的类型应该尽量保持统一、明确、可复用。

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
    pub line_range: ProtoLineRange,
    pub signature: ProtoSignature,
    pub frame: ProtoFrameInfo,
    pub constants: RawConstPool,
    pub upvalues: RawUpvalueInfo,
    pub debug_info: RawDebugInfo,
    pub children: Vec<LoweredProto>,
    pub instrs: Vec<LowInstr>,
    pub lowering_map: LoweringMap,
    pub origin: Origin,
}

/// 基于 proto upvalue 描述符和父链传播结果，恢复当前 proto 哪些 upvalue 表示 `_ENV`。
///
/// 这里优先使用 debug upvalue 名字；当 chunk 被 `luac -s` 剥掉调试信息后，再退回到
/// “根 proto 的第一个 upvalue 是环境、子 proto 通过 upvalue 链继承环境” 这条
/// 结构事实。这样能把 5.2+ 的全局访问重新落回 `AccessBase::Env`，而不是在后层
/// 继续把 `_ENV` 当普通表 upvalue 猜来猜去。
pub(crate) fn resolve_env_upvalues(
    raw: &RawProto,
    parent_env_upvalues: Option<&[bool]>,
) -> Vec<bool> {
    let count = usize::from(raw.common.upvalues.common.count);
    let descriptors = &raw.common.upvalues.common.descriptors;
    let mut env_upvalues = vec![false; count];

    for (index, name) in raw
        .common
        .debug_info
        .common
        .upvalue_names
        .iter()
        .enumerate()
    {
        if index >= count {
            break;
        }
        if raw_string_value(name).is_some_and(|value| value == "_ENV") {
            env_upvalues[index] = true;
        }
    }

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
    } else if !env_upvalues.iter().any(|is_env| *is_env) && !env_upvalues.is_empty() {
        // Lua 5.2+ 根 proto 在 load 时会把第一个 upvalue 绑定到当前环境。
        env_upvalues[0] = true;
    }

    env_upvalues
}

fn raw_string_value(raw: &RawString) -> Option<&str> {
    raw.text.as_ref().map(|text| text.value.as_str())
}

/// low/raw/debug 之间的统一映射关系。
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LoweringMap {
    pub low_to_raw: Vec<Vec<RawInstrRef>>,
    pub raw_to_low: Vec<Vec<InstrRef>>,
    pub pc_map: Vec<Vec<u32>>,
    pub line_hints: Vec<Option<u32>>,
}

/// low-IR 指令的稳定索引。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InstrRef(pub usize);

impl InstrRef {
    pub const fn index(self) -> usize {
        self.0
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

/// raw bytecode 原本就允许 RK 的位置，在 low-IR 里继续保留寄存器/常量二选一。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ValueOperand {
    Reg(Reg),
    Const(ConstRef),
    Integer(i64),
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
    GenericForCall(GenericForCallInstr),
    GenericForLoop(GenericForLoopInstr),
    Jump(JumpInstr),
    Branch(BranchInstr),
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

/// 调用形态，区分普通调用和方法糖。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum CallKind {
    Normal,
    Method,
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
    Env,
    Upvalue(UpvalueRef),
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
    Reg(Reg),
    Upvalue(UpvalueRef),
}

/// capture 的方言扩展槽位。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Default)]
pub enum DialectCaptureExtra {
    #[default]
    None,
}

/// 一个闭包捕获项。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Capture {
    pub source: CaptureSource,
    pub extra: DialectCaptureExtra,
}

/// 条件跳转的谓词。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BranchPredicate {
    Truthy,
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

/// 条件的操作数形态。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum BranchOperands {
    Unary(CondOperand),
    Binary(CondOperand, CondOperand),
}

/// 无副作用条件本体。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct BranchCond {
    pub predicate: BranchPredicate,
    pub operands: BranchOperands,
    pub negated: bool,
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
    pub src: UpvalueRef,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SetUpvalueInstr {
    pub dst: UpvalueRef,
    pub src: Reg,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GetTableInstr {
    pub dst: Reg,
    pub base: AccessBase,
    pub key: AccessKey,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct SetTableInstr {
    pub base: AccessBase,
    pub key: AccessKey,
    pub value: ValueOperand,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ErrNilInstr {
    pub subject: Reg,
    pub name: Option<ConstRef>,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct NewTableInstr {
    pub dst: Reg,
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
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TailCallInstr {
    pub callee: Reg,
    pub args: ValuePack,
    pub kind: CallKind,
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
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct CloseInstr {
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
pub struct GenericForCallInstr {
    pub state: RegRange,
    pub results: ResultPack,
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct GenericForLoopInstr {
    pub control: Reg,
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
