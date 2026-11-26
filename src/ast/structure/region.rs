//! 控制流结构化产出的极简 `RegionTree` 模型。
//!
//! 衔接 `Analysis`（CFG + SSA）与 `Lift`（AST 表达式与语句提升），
//! 不携带任何物理帧或寄存器布局字段。

use crate::analysis::BlockId;
use crate::transformer::{BranchCond, InstrRef, Reg, RegRange};

/// 归约后的复合布尔条件树。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CondExpr {
    True,
    False,
    /// 单个条件测试块；`eval_block` 包含该条件自身的前置纯求值指令。
    Atom {
        block: BlockId,
        cond: BranchCond,
    },
    Not(Box<CondExpr>),
    And(Box<CondExpr>, Box<CondExpr>),
    Or(Box<CondExpr>, Box<CondExpr>),
}

impl CondExpr {
    pub fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Not(inner) => *inner,
            // 原子条件反转极性位（忠实于原字节码条件跳转的另一条边，不改变 NaN 语义）。
            Self::Atom { block, mut cond } => {
                cond.negated = !cond.negated;
                Self::Atom { block, cond }
            }
            Self::And(a, b) => Self::Or(Box::new(a.negate()), Box::new(b.negate())),
            Self::Or(a, b) => Self::And(Box::new(a.negate()), Box::new(b.negate())),
        }
    }
}

/// 局部状态机兜底中的单个状态臂（仅用于无 `goto` 方言遇到真不可规约图时）。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StateArm {
    pub state_id: usize,
    pub block: BlockId,
    pub body: Region,
    pub next: StateTransition,
}

/// 状态机臂结束时的转移动作。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateTransition {
    /// 退出状态机（`_state = 0`）。
    Exit,
    /// 跳转到指定状态编号。
    Jump(usize),
    /// 按条件分支到两个状态编号（None 表示退出状态机）。
    Branch {
        cond: CondExpr,
        then_state: Option<usize>,
        else_state: Option<usize>,
    },
    /// 块内已以 Return/TailCall/Break 结束，无需再更新状态。
    Terminated,
}

/// 控制流结构化区域树。
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Region {
    Empty,
    /// 单个基本块的非控制终结语句（含 Return / TailCall）。
    Block(BlockId),
    /// 仅发射基本块中除最后一条控制指令之外的前缀语句（用于条件/循环头前导代码）。
    BlockPrefix(BlockId),
    /// 仅发射基本块中 `[start_instr, end_instr)` 区间内的非控制语句（用于按 `<close>` 生命周期拆分单块内多个作用域）。
    BlockSlice {
        block: BlockId,
        start_instr: InstrRef,
        end_instr: InstrRef,
    },
    /// 显式 `do ... end` 词法作用域（用于严格保真 Lua 5.4/5.5 `<close>` 资源的声明与关闭边界）。
    DoScope(Box<Region>),
    /// 已折叠的布尔物化写入：`dst = cond`（来自 `CMP/TEST + LOADBOOL false/true`）。
    BoolAssign {
        dst: Reg,
        cond: CondExpr,
        join_block: BlockId,
    },
    /// 顺序执行。
    Sequence(Vec<Region>),
    /// 条件分支。
    If {
        cond: CondExpr,
        then_body: Box<Region>,
        else_body: Option<Box<Region>>,
    },
    /// 显式数值 `for` 循环。
    NumericFor {
        init_block: BlockId,
        init_instr: InstrRef,
        body: Box<Region>,
        index: Reg,
        limit: Reg,
        step: Reg,
        binding: Reg,
    },
    /// 显式泛型 `for` 循环。
    GenericFor {
        prep_block: Option<BlockId>,
        header_block: BlockId,
        call_instr: InstrRef,
        loop_instr: InstrRef,
        body: Box<Region>,
        iterator: Reg,
        state: Reg,
        control: Reg,
        bindings: RegRange,
    },
    /// 前测试 `while cond do body end` 或 `while true do body end`。
    While {
        cond: CondExpr,
        body: Box<Region>,
    },
    /// 后测试 `repeat body until cond`（含单遍 `repeat ... until true` 早退围栏）。
    Repeat {
        body: Box<Region>,
        until_cond: CondExpr,
    },
    Break,
    Continue,
    /// 仅在目标支持 `goto`（Lua 5.2+/LuaJIT）时生成。
    Goto(usize),
    /// 仅在目标支持 `goto` 时生成。
    Labeled(usize, Box<Region>),
    /// 仅在目标无 `goto`（Lua 5.1/Luau）且遇不可规约图时兜底生成。
    StateMachine {
        entry_state: usize,
        states: Vec<StateArm>,
    },
}

impl Region {
    pub fn sequence(items: Vec<Region>) -> Self {
        let mut flat = Vec::new();
        for item in items {
            match item {
                Self::Empty => {}
                Self::Sequence(inner) => flat.extend(inner),
                other => flat.push(other),
            }
        }
        match flat.len() {
            0 => Self::Empty,
            1 => flat.pop().unwrap(),
            _ => Self::Sequence(flat),
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    /// 统计区域树中包含的局部状态机数量（供测试与质量观测）。
    pub fn count_state_machines(&self) -> usize {
        match self {
            Self::StateMachine { states, .. } => {
                1 + states
                    .iter()
                    .map(|s| s.body.count_state_machines())
                    .sum::<usize>()
            }
            Self::Sequence(items) => items.iter().map(Self::count_state_machines).sum(),
            Self::If {
                then_body,
                else_body,
                ..
            } => {
                then_body.count_state_machines()
                    + else_body
                        .as_deref()
                        .map_or(0, Self::count_state_machines)
            }
            Self::NumericFor { body, .. }
            | Self::GenericFor { body, .. }
            | Self::While { body, .. }
            | Self::Repeat { body, .. }
            | Self::Labeled(_, body)
            | Self::DoScope(body) => body.count_state_machines(),
            Self::Empty
            | Self::Block(_)
            | Self::BlockPrefix(_)
            | Self::BlockSlice { .. }
            | Self::BoolAssign { .. }
            | Self::Break
            | Self::Continue
            | Self::Goto(_) => 0,
        }
    }
}
