//! 收敛 locals 提升后暴露的函数入口参数别名。
//!
//! 消费共享 HIR 控制流图、可信 home 与 capture 事实，证明参数和 alias 从入口同值
//! 开始不会被分别观察；不重新推断 phi，也不处理任意 local 对。
//! 例如 local l=p; l=l+1; return l 在同 home 且旧 p 不再被观察时可改为
//! p=p+1; return p。仅显式读写等价不足以允许改变旧参数的根生命周期。

use crate::hir::common::{
    HirBlock, HirCaptureMode, HirExpr, HirLValue, HirLocalDecl, HirProto, HirStmt, LocalId, ParamId,
};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::ProtoPromotionFacts;

use super::super::lexical_cfg::{FlowRefinement, HirFlowGraph, HirFlowNodeKind};
use super::super::mention::{expr_mentions_local, stmts_reference_captured_bindings};
use super::super::walk::{self, HirRewritePass};
use crate::hir::visit::{self, HirVisitor};

pub(super) fn coalesce_param_aliases_in_proto(
    proto: &mut HirProto,
    promotion_facts: &mut ProtoPromotionFacts,
    safety: HirExprSafety,
) -> bool {
    let Some(alias) = match_param_alias_prefix(&proto.body) else {
        return false;
    };
    let shares_exact_home = promotion_facts
        .trusted_local_home_slot(alias.local)
        .zip(promotion_facts.trusted_param_home_slot(alias.param))
        .is_some_and(|(local, param)| local == param);
    let rest = &proto.body.stmts[alias.consumed..];
    if !shares_exact_home {
        // 候选拒绝[SemanticBarrier:Lifetime]：`local l=p; weak[p]=true; l={}; GC` 中跨槽合并会覆盖 p 并让原对象提前回收，原程序的参数槽仍应持有它。
        return false;
    }
    if proto
        .local_debug_hints
        .get(alias.local.index())
        .is_some_and(Option::is_some)
    {
        // 候选拒绝[PolicyBoundary]：带 source debug identity 的 alias local 保留独立声明，不把其名称与词法范围折入参数。
        return false;
    }
    if proto.inline_dispositions.local(alias.local).must_preserve() {
        // 候选拒绝[LayerBoundary]：temp-inline 已冻结该 alias 的 value epoch；把它折入
        // 参数会在 AST 之前删除承载结论的 binding 身份。
        return false;
    }
    if proto.physical_root_locals.contains(&alias.local)
        && (rest.iter().any(|stmt| stmt_writes_param(stmt, alias.param))
            || stmts_reference_captured_bindings(rest)
                .params
                .contains(&alias.param))
    {
        // 候选拒绝[SemanticBarrier:Lifetime]：普通 value-flow 允许在 alias 最后一次读取后
        // 覆盖参数，但 PhysicalRoot 仍须保留旧对象到原 local scope 结束。只有参数在完整
        // 后缀无写且未被 reference capture 暴露时，参数本身才是同一对象的稳定强根；
        // regress_406 覆盖 generic-for body 覆盖参数、弱表观察 alias 提前消失的反例。
        return false;
    }
    if let Err(error) = validate_alias_flow(rest, alias.local, alias.param, safety) {
        match error {
            AliasFlowError::ValueFlow => {
                // 候选拒绝[SemanticBarrier:ValueFlow]：同一路径写一侧后读取另一侧会区分两个 binding；如 `l=1; return p` 或 `p=2; return l`，合并后返回新值而非旧值。
            }
            AliasFlowError::Capture => {
                // 候选拒绝[SemanticBarrier:Capture]：reference capture 暴露一侧 cell 后再写另一侧时，逃逸 closure 可观察原 cell；合并会让它观察后续写入。
            }
            AliasFlowError::Resource => {
                // 候选拒绝[SemanticBarrier:Resource]：`local l=p; <TBC l>; l=q` 若改为参数，会更换 close owner，并可能关闭错误值或改变关闭时点。
            }
            AliasFlowError::UnstructuredControl => {
                // 候选拒绝[ProofIncomplete]：共享 CFG 无法唯一解析 label 或仍有可达的区域外 goto，缺少完整后继，不能证明两侧 binding 在所有路径等价。
            }
            AliasFlowError::BindingInvariant => {
                panic!("alias local must not be redeclared or reused as a for binding")
            }
        }
        return false;
    }

    let mut tail = proto.body.stmts.split_off(alias.consumed);
    let rewritten = walk::rewrite_stmts(
        &mut tail,
        &mut LocalToParamRewrite {
            local: alias.local,
            param: alias.param,
        },
    );
    if rewritten {
        promotion_facts.record_local_to_param_merge(alias.local, alias.param);
    }
    proto.body.stmts.append(&mut tail);
    proto.body.stmts.drain(..alias.consumed);
    true
}

#[derive(Clone, Copy)]
struct ParamAliasPrefix {
    local: LocalId,
    param: ParamId,
    consumed: usize,
}

fn match_param_alias_prefix(block: &HirBlock) -> Option<ParamAliasPrefix> {
    match_param_alias_local_decl(block).or_else(|| match_param_alias_decl_assign(block))
}

fn match_param_alias_local_decl(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let HirStmt::LocalDecl(local_decl) = block.stmts.first()? else {
        return None;
    };
    let local = single_local_binding(local_decl)?;
    let [value] = local_decl.values.fixed.as_slice() else {
        return None;
    };
    if local_decl.values.tail.is_some() {
        return None;
    }
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 1,
    })
}

fn match_param_alias_decl_assign(block: &HirBlock) -> Option<ParamAliasPrefix> {
    let [HirStmt::LocalDecl(local_decl), HirStmt::Assign(assign), ..] = block.stmts.as_slice()
    else {
        return None;
    };
    if !local_decl.values.is_empty() {
        return None;
    }
    let local = single_local_binding(local_decl)?;
    let [target] = assign.targets.as_slice() else {
        return None;
    };
    let [value] = assign.values.fixed.as_slice() else {
        return None;
    };
    if assign.values.tail.is_some() {
        return None;
    }
    if !matches!(target, HirLValue::Local(target) if *target == local) {
        return None;
    }
    let HirExpr::ParamRef(param) = value else {
        return None;
    };
    Some(ParamAliasPrefix {
        local,
        param: *param,
        consumed: 2,
    })
}

fn single_local_binding(local_decl: &HirLocalDecl) -> Option<LocalId> {
    let [local] = local_decl.bindings.as_slice() else {
        return None;
    };
    Some(*local)
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Divergence {
    Equal,
    LocalWritten,
    ParamWritten,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct AliasState {
    divergence: Divergence,
    local_reference_exposed: bool,
    param_reference_exposed: bool,
}

// 三种分叉状态与两个 capture 标志只形成 12 个状态；位序沿用 AliasState 的 Ord，
// 让分支合流和循环不动点无需分配集合，同时保持两阶段检查的遍历顺序。
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct AliasStates(u16);

impl AliasStates {
    fn entry() -> Self {
        Self(1)
    }

    fn is_empty(&self) -> bool {
        self.0 == 0
    }

    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    fn insert(&mut self, state: AliasState) {
        let rank = state.divergence as u32 * 4
            + u32::from(state.local_reference_exposed) * 2
            + u32::from(state.param_reference_exposed);
        self.0 |= 1 << rank;
    }

    fn iter(mut self) -> impl Iterator<Item = AliasState> {
        std::iter::from_fn(move || {
            if self.is_empty() {
                return None;
            }
            let rank = self.0.trailing_zeros();
            self.0 &= self.0 - 1;
            Some(AliasState {
                divergence: match rank / 4 {
                    0 => Divergence::Equal,
                    1 => Divergence::LocalWritten,
                    2 => Divergence::ParamWritten,
                    _ => unreachable!("alias state bit must belong to the twelve-state domain"),
                },
                local_reference_exposed: rank & 2 != 0,
                param_reference_exposed: rank & 1 != 0,
            })
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AliasFlowError {
    ValueFlow,
    Capture,
    Resource,
    UnstructuredControl,
    BindingInvariant,
}

fn validate_alias_flow(
    stmts: &[HirStmt],
    local: LocalId,
    param: ParamId,
    safety: HirExprSafety,
) -> Result<(), AliasFlowError> {
    let graph =
        HirFlowGraph::for_stmts(stmts, safety).map_err(|_| AliasFlowError::UnstructuredControl)?;
    if graph.has_reachable_unresolved_goto() {
        return Err(AliasFlowError::UnstructuredControl);
    }
    // 事实来自同一个不可变 HIR 快照，循环重入只转换有限状态，不再扫描表达式和子块。
    let transfers: Vec<_> = graph
        .nodes()
        .iter()
        .map(|node| AliasTransfer::collect(node.kind(), local, param))
        .collect();
    let mut error = None;
    graph.solve_forward(
        AliasStates::entry(),
        |current, incoming| {
            let joined = current.union(*incoming);
            let changed = joined != *current;
            *current = joined;
            changed
        },
        |id, _, states| {
            if states.is_empty() {
                return;
            }
            match transfers[id.index()].apply(*states) {
                Ok(next) => *states = next,
                Err(failure) => {
                    // 拒绝是单调观察结果；无出口循环中的失败同样阻止提交。
                    error.get_or_insert(failure);
                    *states = AliasStates::default();
                }
            }
        },
        |_, _, _| FlowRefinement::Unchanged,
    );
    error.map_or(Ok(()), Err)
}

enum AliasTransfer {
    Identity,
    Evaluate(AliasEvaluationFacts),
    Ordered(Box<[AliasEvaluationFacts]>),
    Reject(AliasFlowError),
}

impl AliasTransfer {
    fn collect(event: HirFlowNodeKind<'_>, local: LocalId, param: ParamId) -> Self {
        match event {
            HirFlowNodeKind::Stmt(HirStmt::If(stmt)) => Self::expr(&stmt.cond, local, param),
            HirFlowNodeKind::Stmt(HirStmt::While(stmt)) => Self::expr(&stmt.cond, local, param),
            HirFlowNodeKind::RepeatCondition(stmt) => Self::expr(&stmt.cond, local, param),
            HirFlowNodeKind::Stmt(HirStmt::NumericFor(stmt)) => {
                if stmt.binding == local {
                    return Self::Reject(AliasFlowError::BindingInvariant);
                }
                Self::exprs([&stmt.start, &stmt.limit, &stmt.step], local, param)
            }
            HirFlowNodeKind::GenericForInit(flow) => {
                let stmt = flow.for_stmt();
                if stmt.bindings.contains(&local) {
                    return Self::Reject(AliasFlowError::BindingInvariant);
                }
                Self::exprs(&stmt.iterator, local, param)
            }
            HirFlowNodeKind::GenericForDispatch(_) => {
                // 包括零轮和最后一次失败分派；iterator 可经已逃逸的引用观察或改写 cell。
                let mut facts = AliasEvaluationFacts::new(local, param);
                facts.has_opaque_callback = true;
                Self::Evaluate(facts)
            }
            HirFlowNodeKind::Stmt(HirStmt::ToBeClosed(stmt))
                if expr_mentions_local(&stmt.value, local) =>
            {
                Self::Reject(AliasFlowError::Resource)
            }
            HirFlowNodeKind::Stmt(HirStmt::LocalDecl(stmt)) if stmt.bindings.contains(&local) => {
                Self::Reject(AliasFlowError::BindingInvariant)
            }
            HirFlowNodeKind::Stmt(
                HirStmt::Break | HirStmt::Continue | HirStmt::Goto(_) | HirStmt::Label(_),
            )
            | HirFlowNodeKind::Exit
            | HirFlowNodeKind::FunctionExit
            | HirFlowNodeKind::NumericForDispatch
            | HirFlowNodeKind::ForBinding(_) => Self::Identity,
            HirFlowNodeKind::UnknownControl => Self::Reject(AliasFlowError::UnstructuredControl),
            HirFlowNodeKind::Stmt(
                HirStmt::Block(_) | HirStmt::Repeat(_) | HirStmt::GenericFor(_),
            ) => {
                unreachable!("shared flow graph must split structured owners into typed events")
            }
            HirFlowNodeKind::Stmt(stmt) => {
                let mut facts = AliasEvaluationFacts::new(local, param);
                visit::visit_stmts(std::slice::from_ref(stmt), &mut facts);
                facts.has_opaque_callback |= matches!(stmt, HirStmt::Close(_));
                Self::Evaluate(facts)
            }
        }
    }

    fn expr(expr: &HirExpr, local: LocalId, param: ParamId) -> Self {
        Self::Evaluate(AliasEvaluationFacts::for_expr(expr, local, param))
    }

    fn exprs<'a>(
        exprs: impl IntoIterator<Item = &'a HirExpr>,
        local: LocalId,
        param: ParamId,
    ) -> Self {
        // 每个 header 表达式按原顺序发布 capture/callback，不能先合并整组再转换状态。
        Self::Ordered(
            exprs
                .into_iter()
                .map(|expr| AliasEvaluationFacts::for_expr(expr, local, param))
                .collect(),
        )
    }

    fn apply(&self, states: AliasStates) -> Result<AliasStates, AliasFlowError> {
        match self {
            Self::Identity => Ok(states),
            Self::Evaluate(facts) => apply_evaluation_facts(facts, states),
            Self::Ordered(facts) => facts.iter().try_fold(states, |states, facts| {
                apply_evaluation_facts(facts, states)
            }),
            Self::Reject(error) => Err(*error),
        }
    }
}

fn apply_evaluation_facts(
    facts: &AliasEvaluationFacts,
    states: AliasStates,
) -> Result<AliasStates, AliasFlowError> {
    if facts.writes_local && facts.writes_param {
        return Err(AliasFlowError::ValueFlow);
    }
    let mut after_callbacks = AliasStates::default();
    for mut state in states.iter() {
        if (state.divergence == Divergence::LocalWritten && facts.reads_param)
            || (state.divergence == Divergence::ParamWritten && facts.reads_local)
        {
            return Err(AliasFlowError::ValueFlow);
        }
        state.local_reference_exposed |= facts.reference_captures_local;
        state.param_reference_exposed |= facts.reference_captures_param;
        if facts.has_opaque_callback
            && ((state.divergence == Divergence::LocalWritten && state.param_reference_exposed)
                || (state.divergence == Divergence::ParamWritten && state.local_reference_exposed))
        {
            return Err(AliasFlowError::ValueFlow);
        }
        after_callbacks.insert(state);
        if facts.has_opaque_callback {
            if state.local_reference_exposed {
                after_callbacks.insert(AliasState {
                    divergence: Divergence::LocalWritten,
                    ..state
                });
            }
            if state.param_reference_exposed {
                after_callbacks.insert(AliasState {
                    divergence: Divergence::ParamWritten,
                    ..state
                });
            }
        }
    }

    let mut next = AliasStates::default();
    for mut state in after_callbacks.iter() {
        if facts.writes_local {
            if state.param_reference_exposed {
                return Err(AliasFlowError::Capture);
            }
            state.divergence = Divergence::LocalWritten;
        } else if facts.writes_param {
            if state.local_reference_exposed {
                return Err(AliasFlowError::Capture);
            }
            state.divergence = Divergence::ParamWritten;
        }
        next.insert(state);
    }
    Ok(next)
}

struct AliasEvaluationFacts {
    local: LocalId,
    param: ParamId,
    writes_local: bool,
    writes_param: bool,
    reads_local: bool,
    reads_param: bool,
    reference_captures_local: bool,
    reference_captures_param: bool,
    has_opaque_callback: bool,
}

impl AliasEvaluationFacts {
    fn for_expr(expr: &HirExpr, local: LocalId, param: ParamId) -> Self {
        let mut facts = Self::new(local, param);
        visit::visit_expr(expr, &mut facts);
        facts
    }

    fn new(local: LocalId, param: ParamId) -> Self {
        Self {
            local,
            param,
            writes_local: false,
            writes_param: false,
            reads_local: false,
            reads_param: false,
            reference_captures_local: false,
            reference_captures_param: false,
            has_opaque_callback: false,
        }
    }
}

impl HirVisitor<'_> for AliasEvaluationFacts {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.has_opaque_callback |= matches!(stmt, HirStmt::GlobalDecl(_));
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        match expr {
            HirExpr::LocalRef(local) if *local == self.local => self.reads_local = true,
            HirExpr::ParamRef(param) if *param == self.param => self.reads_param = true,
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Call(_) => self.has_opaque_callback = true,
            _ => {}
        }
    }

    fn visit_capture(&mut self, capture: &crate::hir::HirCapture) {
        let local = capture.binding == crate::hir::HirBinding::Local(self.local);
        let param = capture.binding == crate::hir::HirBinding::Param(self.param);
        // 两种捕获模式都读取创建点的父绑定；只有引用捕获会暴露后续写入。
        self.reads_local |= local;
        self.reads_param |= param;
        if capture.mode == HirCaptureMode::ByReference {
            self.reference_captures_local |= local;
            self.reference_captures_param |= param;
        }
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.writes_local |= matches!(lvalue, HirLValue::Local(local) if *local == self.local);
        self.writes_param |= matches!(lvalue, HirLValue::Param(param) if *param == self.param);
        self.has_opaque_callback |=
            matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &crate::hir::common::HirCallExpr) {
        self.has_opaque_callback = true;
    }
}

fn stmt_writes_param(stmt: &HirStmt, param: ParamId) -> bool {
    let mut collector = ParamWriteCollector {
        param,
        written: false,
    };
    visit::visit_stmts(std::slice::from_ref(stmt), &mut collector);
    collector.written
}

struct ParamWriteCollector {
    param: ParamId,
    written: bool,
}

impl HirVisitor<'_> for ParamWriteCollector {
    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.written |= matches!(lvalue, HirLValue::Param(param) if *param == self.param);
    }
}

struct LocalToParamRewrite {
    local: LocalId,
    param: ParamId,
}

impl HirRewritePass for LocalToParamRewrite {
    fn rewrite_capture(&mut self, capture: &mut crate::hir::HirCapture) -> bool {
        if capture.binding == crate::hir::HirBinding::Local(self.local) {
            capture.binding = crate::hir::HirBinding::Param(self.param);
            return true;
        }
        false
    }

    fn rewrite_expr(&mut self, expr: &mut HirExpr) -> bool {
        if matches!(expr, HirExpr::LocalRef(local) if *local == self.local) {
            *expr = HirExpr::ParamRef(self.param);
            return true;
        }
        false
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut HirLValue) -> bool {
        if matches!(lvalue, HirLValue::Local(local) if *local == self.local) {
            *lvalue = HirLValue::Param(self.param);
            return true;
        }
        false
    }
}
