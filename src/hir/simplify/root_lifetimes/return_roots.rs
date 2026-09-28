//! 查询返回值消费后跨观察点仍需保留的根。
//!
//! 消费当前定义图与 collector 的值身份，保留表达式求值顺序，不判断 binding 删除许可。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBinaryOpKind, HirExpr, HirValuePack, TempId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::visit::{HirVisitor, visit_expr};

pub(super) fn observed_return_roots<Id: Copy + Ord>(
    values: &HirValuePack,
    definitions: &BTreeMap<TempId, &HirExpr>,
    root_values: &BTreeMap<TempId, Id>,
    safety: HirExprSafety,
) -> Option<BTreeSet<Id>> {
    let mut dependencies = ReturnDependencies {
        root_values,
        remaining: BTreeMap::new(),
        pending: Vec::new(),
        unsupported: false,
    };
    for value in values.iter() {
        visit_expr(value, &mut dependencies);
    }
    while let Some(temp) = dependencies.pending.pop() {
        if dependencies.unsupported {
            return None;
        }
        visit_expr(definitions.get(&temp)?, &mut dependencies);
    }
    if dependencies.unsupported {
        return None;
    }
    let mut context = ReturnRootContext {
        definitions,
        root_values,
        safety,
        remaining: dependencies.remaining,
        cached: BTreeMap::new(),
        resolving: BTreeSet::new(),
    };
    let flow = values
        .iter()
        .try_fold(ReturnRootFlow::default(), |flow, value| {
            Some(flow.then(context.flow(value)?))
        })?;
    Some(flow.needs_independent_root)
}

struct ReturnDependencies<'a, Id> {
    root_values: &'a BTreeMap<TempId, Id>,
    remaining: BTreeMap<TempId, usize>,
    pending: Vec<TempId>,
    unsupported: bool,
}

impl<Id> HirVisitor<'_> for ReturnDependencies<'_, Id> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::TempRef(temp) if !self.root_values.contains_key(temp) => {
                let count = self.remaining.entry(*temp).or_default();
                if *count == 0 {
                    self.pending.push(*temp);
                }
                *count += 1;
            }
            HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => self.unsupported = true,
            _ => {}
        }
    }
}

struct ReturnRootContext<'a, Id> {
    definitions: &'a BTreeMap<TempId, &'a HirExpr>,
    root_values: &'a BTreeMap<TempId, Id>,
    safety: HirExprSafety,
    remaining: BTreeMap<TempId, usize>,
    cached: BTreeMap<TempId, ReturnRootFlow<Id>>,
    resolving: BTreeSet<TempId>,
}

impl<Id: Copy + Ord> ReturnRootContext<'_, Id> {
    fn temp_flow(&mut self, temp: TempId) -> Option<ReturnRootFlow<Id>> {
        if let Some(value) = self.root_values.get(&temp).copied() {
            return Some(ReturnRootFlow::root(value));
        }
        let remaining = self
            .remaining
            .get_mut(&temp)
            .expect("reachable temp must have a reference edge");
        *remaining -= 1;
        let last_use = *remaining == 0;
        if last_use {
            if let Some(flow) = self.cached.remove(&temp) {
                return Some(flow);
            }
        } else if let Some(flow) = self.cached.get(&temp) {
            return Some(flow.clone());
        }
        let value = self.definitions.get(&temp).copied()?;
        if !self.resolving.insert(temp) {
            return None;
        }
        let flow = self.flow(value);
        self.resolving.remove(&temp);
        let flow = flow?;
        if !last_use {
            self.cached.insert(temp, flow.clone());
        }
        Some(flow)
    }

    fn flow(&mut self, expr: &HirExpr) -> Option<ReturnRootFlow<Id>> {
        match expr {
            HirExpr::TempRef(temp) => self.temp_flow(*temp),
            HirExpr::GlobalRef(_) => Some(ReturnRootFlow::observation()),
            HirExpr::TableAccess(access) => Some(
                self.flow(&access.base)?
                    .then(self.flow(&access.key)?)
                    .consume_result(!access.metamethod_free),
            ),
            HirExpr::Unary(unary) => Some(
                self.flow(&unary.expr)?
                    .consume_result(self.safety.unary_operator_may_observe_gc_roots(unary.op)),
            ),
            HirExpr::Binary(binary)
                if binary.op == HirBinaryOpKind::Concat
                    && self.safety.concat_preserves_rightmost_operand() =>
            {
                self.concat_flow(expr)
            }
            HirExpr::Binary(binary) => Some(
                self.flow(&binary.lhs)?
                    .then(self.flow(&binary.rhs)?)
                    .consume_result(self.safety.binary_operator_may_observe_gc_roots(
                        binary.op,
                        &binary.lhs,
                        &binary.rhs,
                    )),
            ),
            HirExpr::Call(call) => {
                let flow = call
                    .args
                    .iter()
                    .try_fold(self.flow(&call.callee)?, |flow, arg| {
                        Some(flow.then(self.flow(arg)?))
                    })?;
                Some(flow.consume_result(true))
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Complex { .. }
            | HirExpr::Vector(_)
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::CaptureInitializer(_)
            | HirExpr::VarArg => Some(ReturnRootFlow::default()),
            HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => None,
        }
    }

    /// 右结合 concat 源码会合成一条 PUC 5.1 CONCAT；求值依然从左到右，合并从右到左。
    /// 最右 operand 的原槽一直保留，中间 operand 的槽会被部分结果覆盖。只在本次 CONCAT
    /// 内延后最右根的释放；返回 caller flow 时所有 operand 都按已消费结果交出。
    fn concat_flow(&mut self, expr: &HirExpr) -> Option<ReturnRootFlow<Id>> {
        let mut operands = Vec::new();
        let mut cursor = expr;
        while let HirExpr::Binary(binary) = cursor
            && binary.op == HirBinaryOpKind::Concat
        {
            operands.push(&binary.lhs);
            cursor = &binary.rhs;
        }
        operands.push(cursor);
        let mut flow = ReturnRootFlow::default();
        let mut operand_roots = Vec::new();
        for operand in operands {
            let next = self.flow(operand)?;
            operand_roots.push(next.handed_roots.clone());
            flow = flow.then(next);
        }
        for roots in operand_roots[..operand_roots.len() - 1].iter().rev() {
            flow.observe();
            flow.pending_releases.extend(roots.iter().copied());
        }
        Some(flow.consume_result(false))
    }
}

#[derive(Clone)]
struct ReturnRootFlow<Id> {
    handed_roots: BTreeSet<Id>,
    pending_releases: BTreeSet<Id>,
    needs_independent_root: BTreeSet<Id>,
    has_observation: bool,
}

impl<Id> Default for ReturnRootFlow<Id> {
    fn default() -> Self {
        Self {
            handed_roots: BTreeSet::new(),
            pending_releases: BTreeSet::new(),
            needs_independent_root: BTreeSet::new(),
            has_observation: false,
        }
    }
}

impl<Id: Copy + Ord> ReturnRootFlow<Id> {
    fn root(value: Id) -> Self {
        Self {
            handed_roots: BTreeSet::from([value]),
            ..Self::default()
        }
    }

    fn observation() -> Self {
        Self {
            has_observation: true,
            ..Self::default()
        }
    }

    /// 观察前已释放的根成为独立保活需求；后续观察不再重扫这些历史根。
    /// 摘要只需保留尚未跨观察的释放，需求集合单调累积，concat 同样消费这个边界。
    fn observe(&mut self) {
        self.needs_independent_root
            .extend(std::mem::take(&mut self.pending_releases));
        self.has_observation = true;
    }

    fn then(mut self, next: Self) -> Self {
        if next.has_observation {
            self.observe();
        }
        self.handed_roots.extend(next.handed_roots);
        self.pending_releases.extend(next.pending_releases);
        self.needs_independent_root
            .extend(next.needs_independent_root);
        self
    }

    fn consume_result(mut self, observes: bool) -> Self {
        if observes {
            self.observe();
        }
        self.pending_releases
            .extend(std::mem::take(&mut self.handed_roots));
        self
    }
}
