//! 常量控制合同共用的有序轨迹解释器。
//! 各层提供当前节点的语法视图与合法性证明，这里统一维护状态身份、控制退出和执行预算。

use super::{Action, Trace};
use crate::hir::HirBinaryOpKind;
use std::collections::BTreeMap;

pub(crate) enum Step<'a, B, E> {
    Next,
    If(&'a E, &'a B, Option<&'a B>),
    While(&'a E, &'a B),
    Repeat(&'a B, &'a E),
    /// 次数已由语法层核对目标展开限制；该层另行负责最终成本证明。
    NumericFor(usize, &'a B),
    Block(&'a B),
    Return,
    Break,
    Continue,
}

/// 只解释实际到达的语句；未选中路径中的未知操作不使其它参数配置失效。
pub(crate) trait Syntax {
    type Binding: Ord;
    type Block;
    type Stmt;
    type Expr;

    fn statements(block: &Self::Block) -> &[Self::Stmt];
    fn truth(&self, expr: &Self::Expr) -> Option<bool>;
    /// 数据语句验证通过后记录其操作；控制语句只借用节点，不提前遍历子块。
    fn step<'a>(
        &self,
        stmt: &'a Self::Stmt,
        root: bool,
        state: &mut State<Self::Binding>,
    ) -> Option<Step<'a, Self::Block, Self::Expr>>;
}

pub(crate) struct State<K> {
    locals: BTreeMap<K, usize>,
    trace: Trace,
}

impl<K: Ord> State<K> {
    pub fn initialize(&mut self, binding: K, value: i64) -> Option<()> {
        let slot = self.locals.len();
        if self.locals.insert(binding, slot).is_some() {
            return None;
        }
        self.trace.actions.push(Action::Initialize(value));
        Some(())
    }

    pub fn update(&mut self, binding: &K, op: HirBinaryOpKind, value: i64) -> Option<()> {
        self.trace.actions.push(Action::Update {
            state: *self.locals.get(binding)?,
            op,
            value,
        });
        Some(())
    }

    pub fn returns<'a>(&mut self, bindings: impl IntoIterator<Item = Option<&'a K>>) -> Option<()>
    where
        K: 'a,
    {
        self.trace.returned = bindings
            .into_iter()
            .map(|binding| self.locals.get(binding?).copied())
            .collect::<Option<Vec<_>>>()?;
        Some(())
    }
}

#[derive(PartialEq)]
enum Flow {
    Next,
    Return,
    Break,
    Continue,
}

struct Evaluator<'a, S: Syntax> {
    syntax: &'a S,
    state: State<S::Binding>,
    remaining: usize,
}

impl<S: Syntax> Evaluator<'_, S> {
    fn block(&mut self, block: &S::Block, root: bool) -> Option<Flow> {
        for stmt in S::statements(block) {
            // 候选拒绝[ResourceLimit]：每条轨迹最多解释 256 条已执行语句，避免嵌套展开放大工作量。
            self.remaining = self.remaining.checked_sub(1)?;
            let flow = match self.syntax.step(stmt, root, &mut self.state)? {
                Step::Next => Flow::Next,
                Step::Return => Flow::Return,
                Step::Break => Flow::Break,
                Step::Continue => Flow::Continue,
                Step::Block(block) => self.block(block, false)?,
                Step::If(condition, yes, no) => {
                    if self.syntax.truth(condition)? {
                        self.block(yes, false)?
                    } else if let Some(no) = no {
                        self.block(no, false)?
                    } else {
                        Flow::Next
                    }
                }
                Step::While(condition, body) => {
                    if !self.syntax.truth(condition)? {
                        Flow::Next
                    } else {
                        // 条件仅依赖不可写的控制参数；首轮不退出就不构成有限直线轨迹。
                        match self.block(body, false)? {
                            Flow::Break => Flow::Next,
                            Flow::Return => Flow::Return,
                            _ => return None,
                        }
                    }
                }
                Step::Repeat(body, condition) => match self.block(body, false)? {
                    Flow::Return => Flow::Return,
                    Flow::Break => Flow::Next,
                    Flow::Next | Flow::Continue if self.syntax.truth(condition) == Some(true) => {
                        Flow::Next
                    }
                    _ => return None,
                },
                Step::NumericFor(count, body) => {
                    let mut exit = Flow::Next;
                    for _ in 0..count {
                        match self.block(body, false)? {
                            Flow::Break => break,
                            Flow::Return => {
                                exit = Flow::Return;
                                break;
                            }
                            Flow::Next | Flow::Continue => {}
                        }
                    }
                    exit
                }
            };
            if flow != Flow::Next {
                return Some(flow);
            }
        }
        Some(Flow::Next)
    }
}

pub(crate) fn evaluate<S: Syntax>(syntax: &S, block: &S::Block) -> Option<Trace> {
    let mut evaluator = Evaluator {
        syntax,
        state: State {
            locals: BTreeMap::new(),
            trace: Trace {
                actions: Vec::new(),
                returned: Vec::new(),
            },
        },
        remaining: 256,
    };
    let flow = evaluator.block(block, true)?;
    (flow == Flow::Return && !evaluator.state.trace.returned.is_empty())
        .then_some(evaluator.state.trace)
}
