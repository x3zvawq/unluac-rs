//! 分析正常返回包、callee 身份和显式 binding 写入的值域，供 HIR 消费者查询。
//!
//! 复用 HIR CFG、显式 capture 和 LuaValueFacts，保留返回值的槽与数量；
//! 缺失 binding 表示未知，不能当作空 holder 集。摘要随 HIR 改写失效，
//! 不授权删除调用、重排 lookup/COPY 或缩短物理根。
//! 例如 f(change_f()) 的 callee 在参数求值前快照，仍调用原先取得的 f。

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet};

use super::super::lexical_cfg::{HirFlowNodeKind, HirForBindings};
use super::{ObjectId, ProtoFlowFacts};
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
    table: Option<ObjectId>,
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
            table: None,
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
            table: self.table.filter(|table| Some(*table) == other.table),
            anchored: self.anchored || other.anchored,
        }
    }

    fn parameter_facts(self) -> LuaValueFacts {
        // caller 常量树的锚点不能冒充 callee 自身的常量树。
        if self.anchored {
            self.facts.join(LuaValueFacts::RESOURCE)
        } else {
            self.facts
        }
    }
}

/// 只记录完整构造器中最后一次静态写入为直接闭包的字段；动态 key 可能覆盖任意字段。
/// 地址身份沿用 ObjectId，只在当前不可变模块快照中使用，不作为跨轮 provenance。
fn table_callees(
    module: &HirModule,
) -> BTreeMap<ObjectId, BTreeMap<crate::LuaString, HirProtoRef>> {
    struct Tables(BTreeMap<ObjectId, BTreeMap<crate::LuaString, HirProtoRef>>);
    impl crate::hir::visit::HirVisitor<'_> for Tables {
        fn visit_expr(&mut self, expr: &HirExpr) {
            let HirExpr::TableConstructor(table) = expr else {
                return;
            };
            let mut fields = BTreeMap::new();
            for field in &table.fields {
                let HirTableField::Record(record) = field else {
                    continue;
                };
                let HirExpr::String(key) = &record.key else {
                    if matches!(
                        record.key,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                    ) {
                        continue;
                    }
                    return;
                };
                if let HirExpr::Closure(closure) = &record.value {
                    fields.insert(key.clone(), closure.proto);
                } else {
                    fields.remove(key);
                }
            }
            if !fields.is_empty() {
                self.0.insert(ObjectId::table(table), fields);
            }
        }
    }
    let mut tables = Tables(BTreeMap::new());
    for proto in &module.protos {
        crate::hir::visit::visit_stmts(&proto.body.stmts, &mut tables);
    }
    tables.0
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

#[derive(Default)]
struct CallInputs(BTreeMap<HirSourceSite, Vec<LuaValueFacts>>);

/// 同一模块快照的共享调用结果查询；未知目标、未知递归与捕获返回保持 UNKNOWN。
#[derive(Default)]
pub(in crate::hir::simplify) struct ReturnValueFacts {
    summaries: Vec<ReturnSummary>,
    subtree_start: Vec<usize>,
    subtree_end: Vec<usize>,
    calls: BTreeMap<HirSourceSite, CallTarget>,
    entries: Vec<ValueState>,
    table_callees: BTreeMap<ObjectId, BTreeMap<crate::LuaString, HirProtoRef>>,
    escaped_callees: Vec<Cell<bool>>,
    call_inputs: CallInputs,
}

/// 当前 proto 的所有可达显式写都产生非资源值的 binding；引用捕获者不签发此事实。
/// 复用返回域的求值与 CFG 合流，不借用改写前的模块摘要；调用结果一律未知。
/// 本查询只证明值域，不证明原槽覆盖可以删除，或声明能够提前退出作用域。
pub(in crate::hir::simplify) fn gc_inert_bindings(
    proto: &crate::hir::common::HirProto,
    safety: HirExprSafety,
) -> BTreeSet<HirBinding> {
    use super::super::mention::BindingWriteCollector;
    let flow = ProtoFlowFacts::new(proto, safety, super::closure_captures_in_block(&proto.body));
    let mut written = BTreeMap::<HirBinding, LuaValueFacts>::new();
    let mut calls = BTreeMap::new();
    let mut inputs = CallInputs::default();
    flow.graph.solve_forward(
        ValueState::default(),
        ValueState::join,
        |id, kind, state| {
            let mut evaluation = Evaluation {
                state,
                captured: &flow.reference_cells,
                facts: None,
                caller: proto.id,
                safety,
                values: BTreeMap::new(),
                calls: &mut calls,
                inputs: &mut inputs,
                observation: 0,
            };
            evaluation.node(kind);
            kind.visit_evaluation(&mut BindingWriteCollector(|binding| {
                let value = evaluation
                    .state
                    .0
                    .get(&binding)
                    .copied()
                    .unwrap_or(Value::UNKNOWN)
                    .facts;
                written
                    .entry(binding)
                    .and_modify(|old| *old = old.join(value))
                    .or_insert(value);
            }));
            evaluation
                .state
                .0
                .retain(|binding, _| flow.live_out[id.index()].contains(binding));
        },
    );
    written
        .into_iter()
        .filter_map(|(binding, value)| {
            (value.is_gc_inert() && !flow.reference_cells.contains(&binding)).then_some(binding)
        })
        .collect()
}

impl ReturnValueFacts {
    pub(super) fn new(module: &HirModule, captures: &[super::ClosureCaptures<'_>]) -> Self {
        let mut facts = Self {
            summaries: vec![ReturnSummary::default(); module.protos.len()],
            subtree_start: vec![usize::MAX; module.protos.len()],
            subtree_end: vec![0; module.protos.len()],
            entries: stable_capture_entries(module, captures),
            table_callees: table_callees(module),
            escaped_callees: (0..module.protos.len()).map(|_| Cell::new(false)).collect(),
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
        self.analyze(flow, true);
    }

    /// 返回摘要已冻结后重新签发调用点目标，避免 sibling arena 顺序隐藏 factory 字段。
    /// 复用同一 CFG；不迭代展开递归返回包，也不把调用点细化写回返回摘要。
    pub(super) fn finalize_calls(&mut self, flow: &ProtoFlowFacts<'_>) {
        self.analyze(flow, false);
    }

    fn analyze(&mut self, flow: &ProtoFlowFacts<'_>, update_summary: bool) {
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
        let mut inputs = CallInputs::default();
        graph.solve_forward(
            self.entries[proto.id.index()].clone(),
            |state, other| state.join_observing(other, |callee| self.escape(callee)),
            |id, kind, state| {
                let mut evaluation = Evaluation {
                    state,
                    captured: reference_cells,
                    facts: Some(self),
                    caller: proto.id,
                    safety: *safety,
                    values: BTreeMap::new(),
                    calls: &mut calls,
                    inputs: &mut inputs,
                    observation: 0,
                };
                if let Some(values) = evaluation.node(kind) {
                    summary.join(&values);
                }
                // 返回/callee副产物先记录；在共享CFG复制分支状态之前丢弃已无读取的
                // 值身份。只忘记本域事实，不删除原binding或缩短其物理root生命周期。
                evaluation
                    .state
                    .0
                    .retain(|binding, _| live_out[id.index()].contains(binding));
            },
        );
        if update_summary {
            self.summaries[proto.id.index()] = summary;
        }
        self.calls.extend(calls);
        self.call_inputs.0.extend(inputs.0);
    }

    fn escape(&self, callee: HirProtoRef) {
        self.escaped_callees[callee.index()].set(true);
    }

    /// 只汇总完整已知调用集的实参；逃逸、合流后丢失身份或作为 capture 的闭包不细化。
    /// 所有调用点先合流，细化次数不随调用点数量增长。
    pub(super) fn install_closed_parameter_entries(&mut self, module: &HirModule) -> bool {
        let mut entries = BTreeMap::<HirProtoRef, (Vec<LuaValueFacts>, usize)>::new();
        for (site, target) in &self.calls {
            let Some(callee) = target.callee else {
                continue;
            };
            if callee == module.entry || self.escaped_callees[callee.index()].get() {
                continue;
            }
            let Some(arguments) = self.call_inputs.0.get(site) else {
                continue;
            };
            let params = &module.protos[callee.index()].params;
            let (values, minimum_arguments) = entries
                .entry(callee)
                .or_insert_with(|| (vec![LuaValueFacts::EMPTY; params.len()], arguments.len()));
            *minimum_arguments = (*minimum_arguments).min(arguments.len());
            for (value, argument) in values.iter_mut().zip(arguments) {
                *value = value.join(*argument);
            }
        }
        let mut changed = false;
        for (callee, (values, minimum_arguments)) in entries {
            for (index, (&param, mut facts)) in module.protos[callee.index()]
                .params
                .iter()
                .zip(values)
                .enumerate()
            {
                // 省略参数的 nil 后缀按函数合流一次，避免每个短调用扫描全部形参。
                if index >= minimum_arguments {
                    facts = facts.join(LuaValueFacts::NIL);
                }
                if facts != LuaValueFacts::UNKNOWN {
                    self.entries[callee.index()]
                        .install(HirBinding::Param(param), Value::plain(facts));
                    changed = true;
                }
            }
        }
        changed
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

    /// 在分析快照有效时投影单结果定义证书；只允许保值的 temp 转发携带此证书。
    pub(in crate::hir::simplify) fn inert_scalar_call_results(
        &self,
        proto: &crate::hir::HirProto,
    ) -> BTreeSet<crate::hir::TempId> {
        let mut temps = BTreeSet::new();
        for stmt in &proto.body.stmts {
            crate::hir::visit::visit_stmt_structure(stmt, &mut |stmt| {
                if let Some((temp, HirExpr::Call(call))) = stmt.scalar_temp_assignment()
                    && self.call_result(call, 0).is_gc_inert()
                {
                    temps.insert(temp);
                }
            });
        }
        temps
    }

    pub(in crate::hir::simplify) fn call_target(&self, call: &HirCallExpr) -> Option<HirProtoRef> {
        self.calls.get(&call.source_site?)?.callee
    }

    /// 全模块摘要完成后查询正常返回槽的必然闭包；同层 sibling 的分析顺序不使
    /// 已记录的直接调用目标失效，但任一正常返回为未知/不同类型仍拒绝。
    pub(in crate::hir::simplify) fn call_result_callee(
        &self,
        call: &HirCallExpr,
        slot: usize,
    ) -> Option<HirProtoRef> {
        self.target_slot(*self.calls.get(&call.source_site?)?, slot)
            .callee
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

/// 只消费父级顶层已经执行的唯一直接闭包初始化；嵌套声明、分支赋值和可变 cell
/// 保持未知。每个 occurrence 都参与 must-value 合流，未知不能被后一个已知覆盖。
fn stable_capture_entries(
    module: &HirModule,
    captures: &[super::ClosureCaptures<'_>],
) -> Vec<ValueState> {
    use super::super::mention::BindingWriteCollector;
    use crate::hir::common::{HirCaptureMode, HirClosureExpr, UpvalueId};
    use crate::hir::visit::{HirVisitor, visit_stmts};

    struct Captures<'a> {
        available: &'a BTreeMap<HirBinding, Value>,
        entries: &'a mut [Option<ValueState>],
    }
    impl HirVisitor<'_> for Captures<'_> {
        fn visit_closure(&mut self, closure: &HirClosureExpr) {
            let mut entry = ValueState::default();
            for (index, capture) in closure.captures.iter().enumerate() {
                if let Some(&value) = self.available.get(&capture.binding) {
                    entry.install(HirBinding::Upvalue(UpvalueId(index)), value);
                }
            }
            match &mut self.entries[closure.proto.index()] {
                Some(previous) => {
                    previous.join(&entry);
                }
                previous @ None => *previous = Some(entry),
            }
        }
    }
    let mut entries = vec![None; module.protos.len()];
    for proto in &module.protos {
        if proto.children.is_empty() {
            continue;
        }
        let mut writes = BTreeMap::<HirBinding, usize>::new();
        visit_stmts(
            &proto.body.stmts,
            &mut BindingWriteCollector(|binding| {
                *writes.entry(binding).or_default() += 1;
            }),
        );
        let mut mutable = BTreeSet::new();
        for (child, captures) in &captures[proto.id.index()] {
            for (index, capture) in captures.iter().enumerate() {
                if capture.mode == HirCaptureMode::ByReference
                    && module.protos[child.index()]
                        .mutable_upvalues
                        .contains(&UpvalueId(index))
                {
                    mutable.insert(capture.binding);
                }
            }
        }
        let mut available = BTreeMap::new();
        for stmt in &proto.body.stmts {
            visit_stmts(
                std::slice::from_ref(stmt),
                &mut Captures {
                    available: &available,
                    entries: &mut entries,
                },
            );
            let HirStmt::LocalDecl(decl) = stmt else {
                continue;
            };
            let ([local], [HirExpr::Closure(closure)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                continue;
            };
            let binding = HirBinding::Local(*local);
            if writes.get(&binding) == Some(&1) && !mutable.contains(&binding) {
                available.insert(
                    binding,
                    Value {
                        facts: LuaValueFacts::RESOURCE,
                        callee: Some(closure.proto),
                        table: None,
                        anchored: false,
                    },
                );
            }
        }
    }
    entries.into_iter().map(Option::unwrap_or_default).collect()
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
        self.join_observing(other, |_| {})
    }

    fn join_observing(&mut self, other: &Self, mut escape: impl FnMut(HirProtoRef)) -> bool {
        let mut changed = false;
        for (binding, value) in &other.0 {
            if let Some(callee) = value.callee
                && self.0.get(binding).and_then(|value| value.callee) != Some(callee)
            {
                escape(callee);
            }
        }
        self.0.retain(|binding, value| {
            let joined = value.join(other.0.get(binding).copied().unwrap_or(Value::UNKNOWN));
            if let Some(callee) = value.callee
                && joined.callee != Some(callee)
            {
                escape(callee);
            }
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
    facts: Option<&'a ReturnValueFacts>,
    caller: HirProtoRef,
    safety: HirExprSafety,
    values: BTreeMap<usize, (Value, usize)>,
    calls: &'a mut BTreeMap<HirSourceSite, CallTarget>,
    inputs: &'a mut CallInputs,
    observation: usize,
}

impl Evaluation<'_> {
    fn node(&mut self, kind: HirFlowNodeKind<'_>) -> Option<ReturnSummary> {
        match kind {
            HirFlowNodeKind::Stmt(HirStmt::Return(ret)) => {
                let mut values = self.pack(&ret.values);
                for value in values
                    .slots
                    .values()
                    .chain(values.tail.iter().map(|(_, value)| value))
                {
                    self.escape(*value);
                }
                if ret.pending_cleanup_source.is_some() {
                    for value in values.slots.values_mut() {
                        value.table = None;
                    }
                    if let Some((_, value)) = &mut values.tail {
                        value.table = None;
                    }
                }
                return Some(values);
            }
            HirFlowNodeKind::Stmt(stmt) => self.stmt(stmt),
            HirFlowNodeKind::GenericForInit(flow) => self.stmt(flow.stmt()),
            HirFlowNodeKind::RepeatCondition(repeat) => {
                self.expr(&repeat.cond);
            }
            HirFlowNodeKind::ForBinding(HirForBindings::Numeric(local)) => {
                self.state.install(HirBinding::Local(local), Value::UNKNOWN);
            }
            HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)) => {
                for &local in &flow.for_stmt().bindings {
                    self.state.install(HirBinding::Local(local), Value::UNKNOWN);
                }
            }
            HirFlowNodeKind::GenericForDispatch(_) => self.observe(),
            HirFlowNodeKind::UnknownControl => return Some(ReturnSummary::unknown()),
            HirFlowNodeKind::Exit => {
                return Some(ReturnSummary {
                    normal: true,
                    maximum: Some(0),
                    ..ReturnSummary::default()
                });
            }
            HirFlowNodeKind::FunctionExit | HirFlowNodeKind::NumericForDispatch => {}
        }
        None
    }

    fn observe(&mut self) {
        self.observation += 1;
        self.state.0.retain(|binding, value| {
            value.table = None;
            !matches!(binding, HirBinding::Upvalue(_)) && !self.captured.contains(binding)
        });
    }

    fn escape(&self, value: Value) {
        if let Some(callee) = value.callee
            && let Some(facts) = self.facts
        {
            facts.escape(callee);
        }
    }

    fn install(&mut self, binding: HirBinding, value: Value) {
        if matches!(binding, HirBinding::Upvalue(_)) || self.captured.contains(&binding) {
            self.escape(value);
        }
        self.state.install(binding, value);
    }

    fn cached(&self, expr: &HirExpr) -> Value {
        let (mut value, observation) = self.values[&std::ptr::from_ref(expr).addr()];
        if observation != self.observation {
            value.table = None;
        }
        value
    }

    fn call(&mut self, call: &HirCallExpr) -> CallTarget {
        let mut arguments = Vec::with_capacity(call.args.fixed.len());
        if call.fastcall.is_some() {
            // 前层 FASTCALL 协议明确 fallback setup 晚于参数，不能重建成普通CALL顺序。
            for arg in &call.args {
                let value = self.expr(arg);
                self.escape(value);
                arguments.push(value.parameter_facts());
            }
        }
        let value = self.expr(&call.callee);
        let callee = call
            .source_site
            .filter(|site| site.proto == self.caller)
            .filter(|_| self.facts.is_some())
            .and(value.callee);
        if call.fastcall.is_none() {
            for arg in &call.args {
                let value = self.expr(arg);
                self.escape(value);
                arguments.push(value.parameter_facts());
            }
        }
        // 开放参数与隐式 receiver 需要宽度/位置投影；未覆盖的调用必须使整个目标开放，
        // 不能只从其余几个简单调用推断参数。
        if call.args.tail.is_some() || call.is_method() || callee.is_none() {
            self.escape(value);
        } else if let Some(site) = call.source_site {
            self.inputs
                .0
                .entry(site)
                .and_modify(|old| {
                    for (old, value) in old.iter_mut().zip(&arguments) {
                        *old = old.join(*value);
                    }
                })
                .or_insert(arguments);
        } else {
            self.escape(value);
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
                        if let Some(facts) = self.facts {
                            for target in old.callee.into_iter().chain(callee) {
                                facts.escape(target);
                            }
                        }
                        old.callee = None;
                    }
                })
                .or_insert(target);
        }
        target
    }

    fn expr(&mut self, expr: &HirExpr) -> Value {
        if matches!(expr, HirExpr::Binary(_)) {
            return self.binary_tree(expr);
        }
        let value = if let Some(binding) = HirBinding::from_expr(expr) {
            self.state
                .0
                .get(&binding)
                .copied()
                .unwrap_or(Value::UNKNOWN)
        } else if let HirExpr::Call(call) = expr {
            let target = self.call(call);
            self.facts
                .map_or(Value::UNKNOWN, |facts| facts.target_slot(target, 0))
        } else {
            let mut anchored = false;
            traverse_hir_expr_children!(expr, iter = iter, borrow = [&],
                expr(child) => {
                    let value = self.expr(child);
                    self.escape(value);
                    anchored |= value.anchored;
                },
                call(_call) => { unreachable!("call handled above"); },
                decision(decision) => {
                    for node in &decision.nodes {
                        anchored |= self.expr(&node.test).anchored;
                        for target in [&node.truthy, &node.falsy] {
                            if let crate::hir::HirDecisionTarget::Expr(value) = target {
                                let value = self.expr(value);
                                self.escape(value);
                                anchored |= value.anchored;
                            }
                        }
                    }
                },
                table_constructor(table) => {
                    for field in &table.fields {
                        match field {
                            HirTableField::Array(value) => { let value = self.expr(value); self.escape(value); }
                            HirTableField::Record(record) => {
                                let key = self.expr(&record.key); self.escape(key);
                                let value = self.expr(&record.value); self.escape(value);
                            }
                        }
                    }
                    if let Some(tail) = &table.trailing_multivalue {
                        let value = self.expr(tail.as_expr()); self.escape(value);
                    }
                },
                capture(capture) => {
                    if let Some(&value) = self.state.0.get(&capture.binding) { self.escape(value); }
                }
            );
            self.finish_expr(expr, anchored)
        };
        self.values
            .insert(std::ptr::from_ref(expr).addr(), (value, self.observation));
        value
    }

    // 左结合长链使用显式后序栈，保持每个操作与观察事件的原顺序，
    // 不让值域及逃逸分析的栈帧随算术链增长，也不重新结合表达式。
    fn binary_tree(&mut self, root: &HirExpr) -> Value {
        let mut pending = vec![(root, false)];
        while let Some((expr, ready)) = pending.pop() {
            if let HirExpr::Binary(binary) = expr {
                if !ready {
                    pending.push((expr, true));
                    pending.push((&binary.rhs, false));
                    pending.push((&binary.lhs, false));
                    continue;
                }
                let left = self.cached(&binary.lhs);
                let right = self.cached(&binary.rhs);
                self.escape(left);
                self.escape(right);
                let value = self.finish_expr(expr, left.anchored || right.anchored);
                self.values
                    .insert(std::ptr::from_ref(expr).addr(), (value, self.observation));
            } else {
                self.expr(expr);
            }
        }
        self.cached(root)
    }

    // 将节点结算与递归访问分开，避免字段查询的栈帧沿深算术链重复保留。
    fn finish_expr(&mut self, expr: &HirExpr, anchored: bool) -> Value {
        let facts = value_facts_with(expr, &|child| {
            self.values
                .get(&std::ptr::from_ref(child).addr())
                .map(|(value, _)| value.facts)
        });
        let callee = if let HirExpr::Closure(closure) = expr {
            Some(closure.proto)
        } else if let HirExpr::TableAccess(access) = expr {
            match (self.cached(&access.base).table, &access.key) {
                (Some(table), HirExpr::String(key)) => self
                    .facts
                    .and_then(|facts| facts.table_callees.get(&table))
                    .and_then(|fields| fields.get(key))
                    .copied(),
                _ => None,
            }
        } else if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr {
            let left = self.cached(&logical.lhs);
            let right = self.cached(&logical.rhs);
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
            table: if let HirExpr::TableConstructor(table) = expr {
                let id = ObjectId::table(table);
                self.facts
                    .is_some_and(|facts| facts.table_callees.contains_key(&id))
                    .then_some(id)
            } else {
                None
            },
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
    }

    fn pack(&mut self, pack: &HirValuePack) -> ReturnSummary {
        let mut result = ReturnSummary {
            minimum: pack.fixed.len(),
            maximum: Some(pack.fixed.len()),
            normal: true,
            ..ReturnSummary::default()
        };
        let mut table_slots = Vec::new();
        for (slot, value) in pack.fixed.iter().enumerate() {
            let value = self.expr(value);
            if value.table.is_some() {
                table_slots.push((slot, self.observation));
            }
            result.slots.insert(slot, value);
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
                            self.facts
                                .map_or(Value::UNKNOWN, |facts| facts.target_slot(target, index))
                        }),
                    );
                }
                result.minimum += width;
                result.maximum = Some(result.minimum);
            } else if let Some(target) = target
                && let Some(callee) = target.callee
                && let Some(facts) = self.facts
                && facts.summaries[callee.index()].normal
            {
                let tail_summary = &facts.summaries[callee.index()];
                for (&slot, &value) in &tail_summary.slots {
                    result
                        .slots
                        .insert(offset + slot, facts.project(target, value));
                }
                result.minimum += tail_summary.minimum;
                result.maximum = tail_summary.maximum.map(|width| offset + width);
                result.tail = tail_summary
                    .tail
                    .map(|(start, value)| (offset + start, facts.project(target, value)));
            } else {
                result.maximum = None;
                result.tail = Some((offset, Value::UNKNOWN));
            }
        }
        // 前面的返回/赋值槽只冻结对象身份，不冻结字段；后面的 RHS 调用仍可改写它。
        for (slot, observation) in table_slots {
            if observation != self.observation {
                result
                    .slots
                    .get_mut(&slot)
                    .expect("recorded fixed slot")
                    .table = None;
            }
        }
        result
    }

    fn stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl(decl) => {
                let values = self.pack(&decl.values);
                for (index, &local) in decl.bindings.iter().enumerate() {
                    self.install(HirBinding::Local(local), values.slot(index));
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
                // HIR 多目标提交不提供可借用的 Lua 编译器写入顺序；任一非 binding
                // 目标均可能在安装其它槽前后观察 RHS 表，整包不携带字段证明。
                let observes = assign
                    .targets
                    .iter()
                    .any(|target| HirBinding::from_lvalue(target).is_none());
                for (index, target) in assign.targets.iter().enumerate() {
                    if let Some(binding) = HirBinding::from_lvalue(target) {
                        let mut value = values.slot(index);
                        if observes {
                            value.table = None;
                        }
                        self.install(binding, value);
                    } else {
                        self.escape(values.slot(index));
                        self.observe();
                    }
                }
            }
            HirStmt::LocalRootRelease(local) => {
                self.state.install(HirBinding::Local(*local), Value::NIL)
            }
            _ => {
                traverse_hir_stmt_children!(stmt, iter = iter, opt = as_ref, borrow = [&],
                    expr(expr) => { let value = self.expr(expr); self.escape(value); },
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
