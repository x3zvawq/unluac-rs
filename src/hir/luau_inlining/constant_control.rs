//! 提取常量 Boolean 控制下仍执行的初始化、更新和固定返回。
//! 不按状态值删除计算；调用恢复与最终源码核对共享有序操作合同。

use super::*;
use crate::hir::{HirBinaryOpKind, HirBlock, HirLValue, LocalId};
use std::collections::BTreeMap;

pub(crate) mod trace;
use trace::{State, Step, Syntax};

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

struct HirSyntax {
    parameters: usize,
    mask: u8,
}

impl Syntax for HirSyntax {
    type Binding = LocalId;
    type Block = HirBlock;
    type Stmt = HirStmt;
    type Expr = HirExpr;

    fn statements(block: &HirBlock) -> &[HirStmt] {
        &block.stmts
    }

    fn truth(&self, expr: &HirExpr) -> Option<bool> {
        truth(expr, self.parameters, self.mask)
    }

    fn step<'a>(
        &self,
        stmt: &'a HirStmt,
        root: bool,
        state: &mut State<LocalId>,
    ) -> Option<Step<'a, HirBlock, HirExpr>> {
        Some(match stmt {
            // 连续槽合同只覆盖根上的状态声明；嵌套声明还缺少显式的出域轨迹。
            HirStmt::LocalDecl(decl)
                if root
                    && decl.values.tail.is_none()
                    && decl.bindings.len() == decl.values.fixed.len()
                    && decl.initializer_merge_transaction.is_none()
                    && decl.generic_for_initializer_producer.is_none() =>
            {
                for (&local, value) in decl.bindings.iter().zip(&decl.values.fixed) {
                    state.initialize(local, small_integer(value)?)?;
                }
                Step::Next
            }
            HirStmt::Assign(assign)
                if assign.values.tail.is_none()
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
                // 显式同状态更新必须仍有原算术来源；phi COPY 不取得这项权限。
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
                state.update(local, binary.op, small_integer(&binary.rhs)?)?;
                Step::Next
            }
            HirStmt::If(branch) => {
                Step::If(&branch.cond, &branch.then_block, branch.else_block.as_ref())
            }
            HirStmt::While(loop_) => Step::While(&loop_.cond, &loop_.body),
            HirStmt::Repeat(loop_) => Step::Repeat(&loop_.body, &loop_.cond),
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
                Step::NumericFor(count, &loop_.body)
            }
            HirStmt::Return(ret)
                if ret.values.tail.is_none() && ret.pending_cleanup_source.is_none() =>
            {
                state.returns(ret.values.fixed.iter().map(|value| match value {
                    HirExpr::LocalRef(local) => Some(local),
                    _ => None,
                }))?;
                Step::Return
            }
            HirStmt::Break => Step::Break,
            HirStmt::Continue => Step::Continue,
            HirStmt::Block(block) => Step::Block(block),
            // 候选拒绝[ProofIncomplete:Specialization]：未知控制或执行中的观察不属于这份直线操作证书。
            _ => return None,
        })
    }
}

pub(crate) fn trace(proto: &HirProto, mask: u8) -> Option<Trace> {
    trace::evaluate(
        &HirSyntax {
            parameters: proto.params.len(),
            mask,
        },
        &proto.body,
    )
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
