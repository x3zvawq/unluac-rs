//! 按当前返回值的定义图计算 lookup 消费后跨观察点所需的根。
//!
//! 值身份来自同一 collector 的 lookup 映射，定义与表达式顺序来自不可变 HIR 快照；
//! 本层不重新解释 VM home，也不决定哪个 binding 可以删除。例如 `a=lookup; b=a+a;
//! c=b+b; return c` 只分析一次 b 的共享定义，各引用仍按原顺序合并相同的观察事实。
//! 引用次数按可达定义图的 TempRef 边统计，不能使用按语句去重的活读位置。仍有后续边
//! 才保存结果，最后一条边移动取出；单用链不复制逐层增长的根集合。失败终止整次查询，
//! 环检测保留在定义求值入口，不把未完成结果当成可复用事实。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBinaryOpKind, HirExpr, HirValuePack, TempId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::visit::{HirVisitor, visit_expr};

use super::LookupValueId;

pub(super) fn observed_return_lookup_roots(
    values: &HirValuePack,
    definitions: &BTreeMap<TempId, &HirExpr>,
    lookup_values: &BTreeMap<TempId, LookupValueId>,
    safety: HirExprSafety,
) -> Option<BTreeSet<LookupValueId>> {
    let mut dependencies = ReturnDependencies {
        lookup_values,
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
    let mut context = ReturnLookupContext {
        definitions,
        lookup_values,
        safety,
        remaining: dependencies.remaining,
        cached: BTreeMap::new(),
        resolving: BTreeSet::new(),
    };
    let flow = values
        .iter()
        .try_fold(ReturnLookupFlow::default(), |flow, value| {
            Some(flow.then(context.flow(value)?))
        })?;
    Some(flow.needs_independent_root)
}

struct ReturnDependencies<'a> {
    lookup_values: &'a BTreeMap<TempId, LookupValueId>,
    remaining: BTreeMap<TempId, usize>,
    pending: Vec<TempId>,
    unsupported: bool,
}

impl HirVisitor for ReturnDependencies<'_> {
    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::TempRef(temp) if !self.lookup_values.contains_key(temp) => {
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

struct ReturnLookupContext<'a> {
    definitions: &'a BTreeMap<TempId, &'a HirExpr>,
    lookup_values: &'a BTreeMap<TempId, LookupValueId>,
    safety: HirExprSafety,
    remaining: BTreeMap<TempId, usize>,
    cached: BTreeMap<TempId, ReturnLookupFlow>,
    resolving: BTreeSet<TempId>,
}

impl ReturnLookupContext<'_> {
    fn temp_flow(&mut self, temp: TempId) -> Option<ReturnLookupFlow> {
        if let Some(value) = self.lookup_values.get(&temp).copied() {
            return Some(ReturnLookupFlow::lookup(value));
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

    fn flow(&mut self, expr: &HirExpr) -> Option<ReturnLookupFlow> {
        match expr {
            HirExpr::TempRef(temp) => self.temp_flow(*temp),
            HirExpr::GlobalRef(_) => Some(ReturnLookupFlow::observation()),
            HirExpr::TableAccess(access) => Some(
                self.flow(&access.base)?
                    .then(self.flow(&access.key)?)
                    .consume_result(true),
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
            | HirExpr::VarArg => Some(ReturnLookupFlow::default()),
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
    fn concat_flow(&mut self, expr: &HirExpr) -> Option<ReturnLookupFlow> {
        let mut operands = Vec::new();
        let mut cursor = expr;
        while let HirExpr::Binary(binary) = cursor
            && binary.op == HirBinaryOpKind::Concat
        {
            operands.push(&binary.lhs);
            cursor = &binary.rhs;
        }
        operands.push(cursor);
        let mut flow = ReturnLookupFlow::default();
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

#[derive(Clone, Default)]
struct ReturnLookupFlow {
    handed_roots: BTreeSet<LookupValueId>,
    pending_releases: BTreeSet<LookupValueId>,
    needs_independent_root: BTreeSet<LookupValueId>,
    has_observation: bool,
}

impl ReturnLookupFlow {
    fn lookup(value: LookupValueId) -> Self {
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
