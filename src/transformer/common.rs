//! 这个文件集中声明 transformer 层的统一 low-IR 类型。
//!
//! 之所以把这些定义收拢到一个 common 模块，是因为 low-IR 是后续 CFG、
//! Dataflow、HIR 共同依赖的稳定契约；具体某个 dialect 的 lowering 规则可以
//! 分目录演进，但这里的类型应该尽量保持统一、明确、可复用。

use crate::parser::{
    ChunkHeader, Origin, ProtoFrameInfo, ProtoLineRange, ProtoSignature, RawConstPool,
    RawDebugInfo, RawString, RawUpvalueInfo,
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
}

/// 统一 low-IR 指令枚举。
#[derive(Debug, Clone, PartialEq)]
pub enum LowInstr {
    Move(MoveInstr),
    LoadNil(LoadNilInstr),
    LoadBool(LoadBoolInstr),
    LoadConst(LoadConstInstr),
    UnaryOp(UnaryOpInstr),
    BinaryOp(BinaryOpInstr),
    Concat(ConcatInstr),
    GetUpvalue(GetUpvalueInstr),
    SetUpvalue(SetUpvalueInstr),
    GetTable(GetTableInstr),
    SetTable(SetTableInstr),
    NewTable(NewTableInstr),
    SetList(SetListInstr),
    Call(CallInstr),
    TailCall(TailCallInstr),
    VarArg(VarArgInstr),
    Return(ReturnInstr),
    Closure(ClosureInstr),
    Close(CloseInstr),
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
}

/// 表访问的 key。
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum AccessKey {
    Reg(Reg),
    Const(ConstRef),
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
