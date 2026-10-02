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
    pub truth_mask: u8,
    pub trace: Trace,
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
                        && !assign.is_phi_transfer
                        && assign.initializer_merge_transaction.is_none()
                        && assign.generic_for_initializer_producer.is_none()
                        && assign.root_release.is_none()
                        && assign.method_rewrite_transaction.is_none()
                        && assign.parallel_nil_frame.is_none() =>
                {
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
                HirStmt::While(loop_)
                    if truth(&loop_.cond, self.parameters, self.mask) == Some(false) =>
                {
                    Flow::Next
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
    (flow == Flow::Return
        && !evaluator.trace.returned.is_empty()
        && evaluator
            .trace
            .actions
            .iter()
            .any(|action| matches!(action, Action::Update { .. })))
    .then_some(evaluator.trace)
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
    let mut selected: Option<Template> = None;
    for mask in 0..1u8 << (proto.params.len() - 1) {
        let Some(trace) = trace(proto, mask) else {
            continue;
        };
        if let Some(known) = &selected {
            // 候选拒绝[ProofIncomplete:Specialization]：当前 callee 合同只发布一个直线轨迹；
            // 不同轨迹需由多模板 owner 区分，不能随意选择一个掩盖另一条路径。
            if known.trace != trace {
                return None;
            }
        } else {
            selected = Some(Template {
                truth_mask: mask,
                trace,
            });
        }
    }
    selected
}
