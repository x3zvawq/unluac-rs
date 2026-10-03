//! 提取常量 Boolean 控制下仍执行的初始化、更新和固定返回。
//! 不按状态值删除计算；调用恢复与最终源码核对共享有序操作合同。

use super::*;
use crate::hir::{HirBinaryOpKind, HirBlock, HirLValue, LocalId};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Action {
    Initialize(i64),
    Update {
        state: usize,
        op: HirBinaryOpKind,
        value: i64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Trace {
    pub actions: Vec<Action>,
    pub returned: Vec<usize>,
}

pub(crate) struct Template {
    /// 相同操作轨迹只保留一个代表实参；不同轨迹属于同一个 callee。
    pub traces: BTreeMap<Trace, u8>,
}

pub(crate) fn truth(expr: &HirExpr, parameters: usize, mask: u8) -> Option<bool> {
    match expr {
        HirExpr::Boolean(value) => Some(*value),
        HirExpr::ParamRef(param) if param.index() + 1 < parameters => {
            Some(mask & (1 << param.index()) != 0)
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            Some(!truth(&unary.expr, parameters, mask)?)
        }
        HirExpr::LogicalAnd(logical) => {
            if truth(&logical.lhs, parameters, mask)? {
                truth(&logical.rhs, parameters, mask)
            } else {
                Some(false)
            }
        }
        HirExpr::LogicalOr(logical) => {
            if truth(&logical.lhs, parameters, mask)? {
                Some(true)
            } else {
                truth(&logical.rhs, parameters, mask)
            }
        }
        _ => None,
    }
}

#[derive(PartialEq)]
enum Flow {
    Next,
    Return,
    Break,
    Continue,
}

struct Evaluator {
    parameters: usize,
    mask: u8,
    locals: BTreeMap<LocalId, usize>,
    trace: Trace,
    remaining: usize,
}

impl Evaluator {
    // 当前连续槽合同只覆盖函数根上的状态声明；嵌套词法声明还需要显式
    // 出域轨迹，不能以初始化总数替代其物理栈位置。
    fn block(&mut self, block: &HirBlock, root: bool) -> Option<Flow> {
        for stmt in &block.stmts {
            self.remaining = self.remaining.checked_sub(1)?;
            let flow = match stmt {
                HirStmt::LocalDecl(decl)
                    if root
                        && decl.values.tail.is_none()
                        && decl.bindings.len() == decl.values.fixed.len()
                        && decl.initializer_merge_transaction.is_none()
                        && decl.generic_for_initializer_producer.is_none() =>
                {
                    for (&local, value) in decl.bindings.iter().zip(&decl.values.fixed) {
                        let state = self.locals.len();
                        if self.locals.insert(local, state).is_some() {
                            return None;
                        }
                        self.trace
                            .actions
                            .push(Action::Initialize(small_integer(value)?));
                    }
                    Flow::Next
                }
                HirStmt::Assign(assign)
                    if assign.values.tail.is_none()
                        && assign.initializer_merge_transaction.is_none()
                        && assign.generic_for_initializer_producer.is_none()
                        && assign.root_release.is_none()
                        && assign.method_rewrite_transaction.is_none()
                        && assign.parallel_nil_frame.is_none() =>
                {
                    // 树化后原算术可直接写入 phi carrier；来源仍在 Binary 上。
                    // 这里只解释显式同状态更新，不把无来源的 phi COPY 当作一次计算。
                    let ([HirLValue::Local(local)], [HirExpr::Binary(binary)]) =
                        (assign.targets.as_slice(), assign.values.fixed.as_slice())
                    else {
                        return None;
                    };
                    if binary.lhs != HirExpr::LocalRef(*local)
                        || !matches!(
                            binary.op,
                            HirBinaryOpKind::Add
                                | HirBinaryOpKind::Sub
                                | HirBinaryOpKind::Mul
                                | HirBinaryOpKind::Div
                                | HirBinaryOpKind::Mod
                                | HirBinaryOpKind::Pow
                        )
                        || binary.source_site.is_none()
                    {
                        return None;
                    }
                    self.trace.actions.push(Action::Update {
                        state: *self.locals.get(local)?,
                        op: binary.op,
                        value: small_integer(&binary.rhs)?,
                    });
                    Flow::Next
                }
                HirStmt::If(branch) => {
                    if truth(&branch.cond, self.parameters, self.mask)? {
                        self.block(&branch.then_block, false)?
                    } else if let Some(other) = &branch.else_block {
                        self.block(other, false)?
                    } else {
                        Flow::Next
                    }
                }
                HirStmt::While(loop_) => {
                    if !truth(&loop_.cond, self.parameters, self.mask)? {
                        Flow::Next
                    } else {
                        // 条件只读取不可写的 Boolean 参数；首轮不退出就不是有限直线轨迹。
                        match self.block(&loop_.body, false)? {
                            Flow::Break => Flow::Next,
                            Flow::Return => Flow::Return,
                            _ => return None,
                        }
                    }
                }
                HirStmt::NumericFor(loop_) => {
                    let count = crate::hir::luau_loop_cost::trips(
                        small_integer(&loop_.start)?,
                        small_integer(&loop_.limit)?,
                        small_integer(&loop_.step)?,
                    )?;
                    // 候选拒绝[TargetConstraint]：pinned Luau 最多展开 25 轮；最终 AST 另核对成本。
                    if count > 25 {
                        return None;
                    }
                    let mut exit = Flow::Next;
                    for _ in 0..count {
                        match self.block(&loop_.body, false)? {
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
                HirStmt::Repeat(loop_) => match self.block(&loop_.body, false)? {
                    Flow::Return => Flow::Return,
                    Flow::Break => Flow::Next,
                    Flow::Next | Flow::Continue
                        if truth(&loop_.cond, self.parameters, self.mask) == Some(true) =>
                    {
                        Flow::Next
                    }
                    _ => return None,
                },
                HirStmt::Return(ret)
                    if ret.values.tail.is_none() && ret.pending_cleanup_source.is_none() =>
                {
                    self.trace.returned = ret
                        .values
                        .fixed
                        .iter()
                        .map(|value| {
                            let HirExpr::LocalRef(local) = value else {
                                return None;
                            };
                            self.locals.get(local).copied()
                        })
                        .collect::<Option<Vec<_>>>()?;
                    Flow::Return
                }
                HirStmt::Break => Flow::Break,
                HirStmt::Continue => Flow::Continue,
                HirStmt::Block(block) => self.block(block, false)?,
                // 候选拒绝[ProofIncomplete:Specialization]：未知控制或执行中的观察不属于这份直线操作证书。
                _ => return None,
            };
            if flow != Flow::Next {
                return Some(flow);
            }
        }
        Some(Flow::Next)
    }
}

pub(crate) fn trace(proto: &HirProto, mask: u8) -> Option<Trace> {
    let mut evaluator = Evaluator {
        parameters: proto.params.len(),
        mask,
        locals: BTreeMap::new(),
        trace: Trace {
            actions: Vec::new(),
            returned: Vec::new(),
        },
        remaining: 256,
    };
    let flow = evaluator.block(&proto.body, true)?;
    (flow == Flow::Return && !evaluator.trace.returned.is_empty()).then_some(evaluator.trace)
}

pub(crate) fn template(proto: &HirProto) -> Option<Template> {
    // 候选搜索裁剪[ResourceLimit]：最多七个 Boolean 维度、每条轨迹至多 256 条语句；
    // 每个函数只建一次有限参数表，调用位置按轨迹索引，不逐候选重扫函数。
    if !(2..=8).contains(&proto.params.len())
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    struct ParameterWrites(bool);
    impl crate::hir::visit::HirVisitor<'_> for ParameterWrites {
        fn visit_lvalue(&mut self, value: &HirLValue) {
            self.0 |= matches!(value, HirLValue::Param(_));
        }
    }
    let mut writes = ParameterWrites(false);
    crate::hir::visit::visit_stmts(&proto.body.stmts, &mut writes);
    if writes.0 {
        return None;
    }
    let mut traces = BTreeMap::new();
    for mask in 0..1u8 << (proto.params.len() - 1) {
        let Some(trace) = trace(proto, mask) else {
            continue;
        };
        traces.entry(trace).or_insert(mask);
    }
    (!traces.is_empty()).then_some(Template { traces })
}
