//! 正常返回包与完整 callee 值身份的共享分析。
//!
//! 复用 HIR CFG、显式 capture 与 LuaValueFacts；缺少 binding 就是未知值，而不是
//! may-holder 的空集合。CALL 先快照 callee 再求参数，任何观察只撤销可能被引用
//! capture 改写的 binding。例如 `f(change_f())` 仍调用参数求值前取得的 f。
//! 返回包保留实际槽与数量，`return` 在单值位置补 nil，不能把 open tail 的首槽
//! 复制给所有结果。字符串/cdata 常量只有执行中的词法祖先仍持有原 proto 时才
//! 发布栈根无关事实；本摘要不授权删除调用、改变 SETLIST 或缩短物理根。
//! 调用查询使用 lowering 发布的原调用身份；同一指令的多个 occurrence 必须合流。
//! 表达式地址只用于单次只读求值的局部缓存，不离开求值器。摘要随 HIR 改写失效。

use std::collections::{BTreeMap, BTreeSet};

use super::super::lexical_cfg::{FlowRefinement, HirFlowNodeKind, HirForBindings};
use super::ProtoFlowFacts;
use crate::hir::common::{
    HirBinding, HirCallExpr, HirExpr, HirLValue, HirModule, HirProtoRef, HirSourceSite, HirStmt,
    HirTableField, HirValuePack,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::traverse::{traverse_hir_expr_children, traverse_hir_stmt_children};
use crate::hir::value_facts::value_facts_with;
use crate::value_semantics::results::LuaValueFacts;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Value {
    facts: LuaValueFacts,
    callee: Option<HirProtoRef>,
    // 该值的无额外栈根证明依赖当前摘要 proto 的常量子树。
    anchored: bool,
}

impl Value {
    const UNKNOWN: Self = Self::plain(LuaValueFacts::UNKNOWN);
    const NIL: Self = Self::plain(LuaValueFacts::NIL);
    const EMPTY: Self = Self::plain(LuaValueFacts::EMPTY);

    const fn plain(facts: LuaValueFacts) -> Self {
        Self {
            facts,
            callee: None,
            anchored: false,
        }
    }

    fn join(self, other: Self) -> Self {
        if self.facts.is_empty() {
            return other;
        }
        if other.facts.is_empty() {
            return self;
        }
        Self {
            facts: self.facts.join(other.facts),
            callee: self.callee.filter(|callee| Some(*callee) == other.callee),
            anchored: self.anchored || other.anchored,
        }
    }
}

/// 实际返回槽的并集与正常返回数量；absent 与显式 nil 在调整为目标宽度前分开。
#[derive(Clone, Default)]
pub(super) struct ReturnSummary {
    slots: BTreeMap<usize, Value>,
    tail: Option<(usize, Value)>,
    minimum: usize,
    maximum: Option<usize>,
    normal: bool,
}

impl ReturnSummary {
    fn unknown() -> Self {
        Self {
            tail: Some((0, Value::UNKNOWN)),
            normal: true,
            ..Self::default()
        }
    }

    fn slot(&self, index: usize) -> Value {
        if !self.normal {
            return Value::UNKNOWN;
        }
        let mut value = self.slots.get(&index).copied().unwrap_or(Value::EMPTY);
        if let Some((start, tail)) = self.tail
            && index >= start
        {
            value = value.join(tail);
        }
        if index >= self.minimum {
            value = value.join(Value::NIL);
        }
        value
    }

    fn join(&mut self, other: &Self) {
        if !other.normal {
            return;
        }
        if !self.normal {
            *self = other.clone();
            return;
        }
        self.minimum = self.minimum.min(other.minimum);
        self.maximum = self.maximum.zip(other.maximum).map(|(a, b)| a.max(b));
        for (&slot, &value) in &other.slots {
            self.slots
                .entry(slot)
                .and_modify(|old| *old = old.join(value))
                .or_insert(value);
        }
        if let Some((start, value)) = other.tail {
            self.tail = Some(self.tail.map_or((start, value), |(old_start, old)| {
                (start.min(old_start), old.join(value))
            }));
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CallTarget {
    callee: Option<HirProtoRef>,
    caller: HirProtoRef,
}

/// 同一模块快照的共享调用结果查询；未知目标、未知递归与捕获返回保持 UNKNOWN。
#[derive(Default)]
pub(in crate::hir::simplify) struct ReturnValueFacts {
    summaries: Vec<ReturnSummary>,
    subtree_start: Vec<usize>,
    subtree_end: Vec<usize>,
    calls: BTreeMap<HirSourceSite, CallTarget>,
}

impl ReturnValueFacts {
    pub(super) fn new(module: &HirModule) -> Self {
        let mut facts = Self {
            summaries: vec![ReturnSummary::default(); module.protos.len()],
            subtree_start: vec![usize::MAX; module.protos.len()],
            subtree_end: vec![0; module.protos.len()],
            ..Self::default()
        };
        // arena 只保证父先于子，兄弟预留使其下标区间不一定就是词法子树。
        let mut clock = 0;
        for root in 0..module.protos.len() {
            if facts.subtree_start[root] != usize::MAX {
                continue;
            }
            let mut pending = vec![(root, false)];
            while let Some((index, exit)) = pending.pop() {
                if exit {
                    facts.subtree_end[index] = clock;
                    continue;
                }
                facts.subtree_start[index] = clock;
                clock += 1;
                pending.push((index, true));
                pending.extend(
                    module.protos[index]
                        .children
                        .iter()
                        .rev()
                        .map(|child| (child.index(), false)),
                );
            }
        }
        facts
    }

    pub(super) fn analyze_proto(&mut self, flow: &ProtoFlowFacts<'_>) {
        let ProtoFlowFacts {
            proto,
            graph,
            live_out,
            reference_cells,
            safety,
            ..
        } = flow;
        let mut summary = ReturnSummary::default();
        let mut calls = BTreeMap::new();
        graph.solve_forward(
            ValueState::default(),
            ValueState::join,
            |id, kind, state| {
                let mut evaluation = Evaluation {
                    state,
                    captured: reference_cells,
                    facts: self,
                    caller: proto.id,
                    safety: *safety,
                    values: BTreeMap::new(),
                    calls: &mut calls,
                };
                match kind {
                    HirFlowNodeKind::Stmt(HirStmt::Return(ret)) => {
                        summary.join(&evaluation.pack(&ret.values))
                    }
                    HirFlowNodeKind::Stmt(stmt) => evaluation.stmt(stmt),
                    HirFlowNodeKind::GenericForInit(flow) => evaluation.stmt(flow.stmt()),
                    HirFlowNodeKind::RepeatCondition(repeat) => {
                        evaluation.expr(&repeat.cond);
                    }
                    HirFlowNodeKind::ForBinding(HirForBindings::Numeric(local)) => {
                        evaluation
                            .state
                            .install(HirBinding::Local(local), Value::UNKNOWN);
                    }
                    HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)) => {
                        for &local in &flow.for_stmt().bindings {
                            evaluation
                                .state
                                .install(HirBinding::Local(local), Value::UNKNOWN);
                        }
                    }
                    HirFlowNodeKind::GenericForDispatch(_) => evaluation.observe(),
                    HirFlowNodeKind::UnknownControl => summary.join(&ReturnSummary::unknown()),
                    HirFlowNodeKind::Exit => summary.join(&ReturnSummary {
                        normal: true,
                        maximum: Some(0),
                        ..ReturnSummary::default()
                    }),
                    HirFlowNodeKind::FunctionExit | HirFlowNodeKind::NumericForDispatch => {}
                }
                // 返回/callee副产物先记录；在共享CFG复制分支状态之前丢弃已无读取的
                // 值身份。只忘记本域事实，不删除原binding或缩短其物理root生命周期。
                evaluation
                    .state
                    .0
                    .retain(|binding, _| live_out[id.index()].contains(binding));
            },
            |_, _, _| FlowRefinement::Unchanged,
        );
        self.summaries[proto.id.index()] = summary;
        self.calls.extend(calls);
    }

    fn project(&self, target: CallTarget, value: Value) -> Value {
        if value.anchored
            && !target.callee.is_some_and(|callee| {
                self.subtree_start[target.caller.index()] <= self.subtree_start[callee.index()]
                    && self.subtree_start[callee.index()] < self.subtree_end[target.caller.index()]
            })
        {
            Value {
                facts: value.facts.join(LuaValueFacts::RESOURCE),
                anchored: false,
                ..value
            }
        } else {
            value
        }
    }

    fn target_slot(&self, target: CallTarget, slot: usize) -> Value {
        target.callee.map_or(Value::UNKNOWN, |callee| {
            self.project(target, self.summaries[callee.index()].slot(slot))
        })
    }

    pub(in crate::hir::simplify) fn call_result(
        &self,
        call: &HirCallExpr,
        slot: usize,
    ) -> LuaValueFacts {
        call.source_site
            .and_then(|site| self.calls.get(&site))
            .map_or(LuaValueFacts::UNKNOWN, |&target| {
                self.target_slot(target, slot).facts
            })
    }

    /// 正常返回的数量范围；未知 callee/递归没有精确宽度证书，零返回不是未知。
    pub(in crate::hir::simplify) fn call_width(
        &self,
        call: &HirCallExpr,
    ) -> Option<(usize, Option<usize>)> {
        let target = self.calls.get(&call.source_site?)?;
        let summary = &self.summaries[target.callee?.index()];
        summary.normal.then_some((summary.minimum, summary.maximum))
    }

    pub(in crate::hir::simplify) fn value_facts(&self, expr: &HirExpr) -> LuaValueFacts {
        value_facts_with(expr, &|expr| match expr {
            HirExpr::Call(call) => Some(self.call_result(call, 0)),
            _ => None,
        })
    }

    /// 对已有 pack 的目标槽执行 Lua 调整；exact/open 尾的 offset 必须保留。
    pub(in crate::hir::simplify) fn pack_slot(
        &self,
        pack: &HirValuePack,
        slot: usize,
    ) -> LuaValueFacts {
        if let Some(value) = pack.fixed.get(slot) {
            return self.value_facts(value);
        }
        let Some(tail) = &pack.tail else {
            return LuaValueFacts::NIL;
        };
        let offset = slot - pack.fixed.len();
        if tail.exact_width().is_some_and(|width| offset >= width) {
            return LuaValueFacts::NIL;
        }
        match tail.as_expr() {
            HirExpr::Call(call) => {
                if self
                    .call_width(call)
                    .and_then(|(_, max)| max)
                    .is_some_and(|width| offset >= width)
                {
                    LuaValueFacts::NIL
                } else {
                    self.call_result(call, offset)
                }
            }
            _ => LuaValueFacts::UNKNOWN,
        }
    }
}

#[derive(Clone, Default)]
struct ValueState(BTreeMap<HirBinding, Value>);
impl ValueState {
    fn install(&mut self, binding: HirBinding, value: Value) {
        if value == Value::UNKNOWN {
            self.0.remove(&binding);
        } else {
            self.0.insert(binding, value);
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        self.0.retain(|binding, value| {
            let joined = value.join(other.0.get(binding).copied().unwrap_or(Value::UNKNOWN));
            changed |= *value != joined;
            *value = joined;
            joined != Value::UNKNOWN
        });
        changed
    }
}

struct Evaluation<'a> {
    state: &'a mut ValueState,
    captured: &'a BTreeSet<HirBinding>,
    facts: &'a ReturnValueFacts,
    caller: HirProtoRef,
    safety: HirExprSafety,
    values: BTreeMap<usize, Value>,
    calls: &'a mut BTreeMap<HirSourceSite, CallTarget>,
}

impl Evaluation<'_> {
    fn observe(&mut self) {
        self.state.0.retain(|binding, _| {
            !matches!(binding, HirBinding::Upvalue(_)) && !self.captured.contains(binding)
        });
    }

    fn call(&mut self, call: &HirCallExpr) -> CallTarget {
        if call.fastcall.is_some() {
            // 前层 FASTCALL 协议明确 fallback setup 晚于参数，不能重建成普通CALL顺序。
            for arg in &call.args {
                self.expr(arg);
            }
        }
        let value = self.expr(&call.callee);
        let callee = call
            .source_site
            .filter(|site| site.proto == self.caller)
            .and(value.callee);
        if call.fastcall.is_none() {
            for arg in &call.args {
                self.expr(arg);
            }
        }
        self.observe();
        let target = CallTarget {
            callee,
            caller: self.caller,
        };
        if let Some(site) = call.source_site {
            self.calls
                .entry(site)
                .and_modify(|old| {
                    if old.callee != callee {
                        old.callee = None;
                    }
                })
                .or_insert(target);
        }
        target
    }

    fn expr(&mut self, expr: &HirExpr) -> Value {
        let value = if let Some(binding) = HirBinding::from_expr(expr) {
            self.state
                .0
                .get(&binding)
                .copied()
                .unwrap_or(Value::UNKNOWN)
        } else if let HirExpr::Call(call) = expr {
            let target = self.call(call);
            self.facts.target_slot(target, 0)
        } else {
            let mut anchored = false;
            traverse_hir_expr_children!(expr, iter = iter, borrow = [&],
                expr(child) => { anchored |= self.expr(child).anchored; },
                call(_call) => { unreachable!("call handled above"); },
                decision(decision) => {
                    for node in &decision.nodes {
                        anchored |= self.expr(&node.test).anchored;
                        for target in [&node.truthy, &node.falsy] {
                            if let crate::hir::HirDecisionTarget::Expr(value) = target {
                                anchored |= self.expr(value).anchored;
                            }
                        }
                    }
                },
                table_constructor(table) => {
                    for field in &table.fields {
                        match field {
                            HirTableField::Array(value) => { self.expr(value); }
                            HirTableField::Record(record) => { self.expr(&record.key); self.expr(&record.value); }
                        }
                    }
                    if let Some(tail) = &table.trailing_multivalue { self.expr(tail.as_expr()); }
                },
                capture(_capture) => {}
            );
            let facts = value_facts_with(expr, &|child| {
                self.values
                    .get(&std::ptr::from_ref(child).addr())
                    .map(|value| value.facts)
            });
            let callee = if let HirExpr::Closure(closure) = expr {
                Some(closure.proto)
            } else if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr {
                let left = self.values[&std::ptr::from_ref(&logical.lhs).addr()];
                let right = self.values[&std::ptr::from_ref(&logical.rhs).addr()];
                left.callee.filter(|callee| Some(*callee) == right.callee)
            } else {
                None
            };
            if self.safety.node_may_observe_gc_roots(expr) {
                self.observe();
            }
            Value {
                facts,
                callee,
                anchored: anchored
                    || matches!(
                        expr,
                        HirExpr::String(_)
                            | HirExpr::Int64(_)
                            | HirExpr::UInt64(_)
                            | HirExpr::Complex { .. }
                            | HirExpr::Vector(_)
                    ),
            }
        };
        self.values.insert(std::ptr::from_ref(expr).addr(), value);
        value
    }

    fn pack(&mut self, pack: &HirValuePack) -> ReturnSummary {
        let mut result = ReturnSummary {
            minimum: pack.fixed.len(),
            maximum: Some(pack.fixed.len()),
            normal: true,
            ..ReturnSummary::default()
        };
        for (slot, value) in pack.fixed.iter().enumerate() {
            result.slots.insert(slot, self.expr(value));
        }
        if let Some(tail) = &pack.tail {
            let offset = pack.fixed.len();
            let target = if let HirExpr::Call(call) = tail.as_expr() {
                Some(self.call(call))
            } else {
                self.expr(tail.as_expr());
                None
            };
            if let Some(width) = tail.exact_width() {
                for index in 0..width {
                    result.slots.insert(
                        offset + index,
                        target.map_or(Value::UNKNOWN, |target| {
                            self.facts.target_slot(target, index)
                        }),
                    );
                }
                result.minimum += width;
                result.maximum = Some(result.minimum);
            } else if let Some(target) = target
                && let Some(callee) = target.callee
                && self.facts.summaries[callee.index()].normal
            {
                let tail_summary = &self.facts.summaries[callee.index()];
                for (&slot, &value) in &tail_summary.slots {
                    result
                        .slots
                        .insert(offset + slot, self.facts.project(target, value));
                }
                result.minimum += tail_summary.minimum;
                result.maximum = tail_summary.maximum.map(|width| offset + width);
                result.tail = tail_summary
                    .tail
                    .map(|(start, value)| (offset + start, self.facts.project(target, value)));
            } else {
                result.maximum = None;
                result.tail = Some((offset, Value::UNKNOWN));
            }
        }
        result
    }

    fn stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                let values = self.pack(&decl.values);
                for (index, &local) in decl.bindings.iter().enumerate() {
                    self.state
                        .install(HirBinding::Local(local), values.slot(index));
                }
            }
            HirStmt::Assign(assign) => {
                for target in &assign.targets {
                    if let HirLValue::TableAccess(access) = target {
                        self.expr(&access.base);
                        self.expr(&access.key);
                    }
                }
                let values = self.pack(&assign.values);
                for (index, target) in assign.targets.iter().enumerate() {
                    if let Some(binding) = HirBinding::from_lvalue(target) {
                        self.state.install(binding, values.slot(index));
                    } else {
                        self.observe();
                    }
                }
            }
            HirStmt::LocalRootRelease(local) => {
                self.state.install(HirBinding::Local(*local), Value::NIL)
            }
            _ => {
                traverse_hir_stmt_children!(stmt, iter = iter, opt = as_ref, borrow = [&],
                    expr(expr) => { self.expr(expr); },
                    lvalue(_lvalue) => {}, release(_local) => {}, block(_block) => {},
                    call(call) => { self.call(call); }, condition(cond) => { self.expr(cond); }
                );
                if matches!(stmt, HirStmt::Close(_) | HirStmt::GlobalDecl(_)) {
                    self.observe();
                }
            }
        }
    }
}
