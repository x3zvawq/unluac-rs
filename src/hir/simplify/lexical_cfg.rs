//! 这个文件提供 HIR simplify 共用的词法控制流事实。
//!
//! `HirFlowGraph` 按当前区域的唯一 LabelId 连接 goto；源码标签布局的合法性由
//! Structure/AST 的 scope 合同负责。`break` / `continue` 由最近的 loop owner 消费，
//! 分支与循环出口使用目标方言 truthiness 事实判定。该图是当前 HIR 树
//! 的 owner-wide topology 单一来源；它区分 for 的一次性求值节点与循环 dispatch，并为
//! dataflow consumer 提供稳定 node id 和后继。block-local `LexicalCfg` 从同一图的可达
//! 出口投影线性 rewrite 所需的 successor、外部出口和支配查询，不另行解释控制结构。
//! 每个语义事件同时借用创建它的 HIR 语句；repeat 条件与 for 分派/写入即使拆成多个
//! 节点也保留同一 owner，消费者不从子 payload 指针反查原语句。合成出口没有语句 owner。
//! 例如 `do ... goto outer end; ...; ::outer::` 由子图的未解析出口连接直属 label，
//! 子图内自含的回环则只通过真实可达的正常出口影响后续语句。
//! 本模块不推断 temp reaching-def 或 root lifetime；这些仍由具体 pass 结合 promotion facts
//! 判断。
//! `validate_region_entry` 独立验证区域 label 唯一性和外部入口；只需要检查词法入口的
//! consumer 直接消费它，完整 CFG 也复用该结果，不为验证边界而构造后继与可达性。
//! 构图与重入查询的临时词法导航复用路径栈，仅已登记 label 和重入边界拥有路径副本。

use std::{
    cell::OnceCell,
    collections::{BTreeMap, BTreeSet, VecDeque},
};

use crate::hir::common::{
    HirBlock, HirExpr, HirGenericFor, HirLabelId, HirRepeat, HirStmt, LocalId,
};
use crate::hir::expr_safety::HirExprSafety;

use super::expr_facts::expr_truthiness;
use crate::hir::visit::visit_stmt_structure;

mod statement_tree;
pub(super) use statement_tree::{HirStmtId, HirStmtTree};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum LexicalCfgFailure {
    AmbiguousLabel,
    ExternalEntry,
}

/// 当前区域的词法入口事实，不裁剪不可达的 label/goto，也不证明出口或支配关系。
pub(super) fn validate_region_entry(
    stmts: &[HirStmt],
    owner_label_refs: &BTreeMap<HirLabelId, usize>,
) -> Result<(), LexicalCfgFailure> {
    let mut labels = BTreeSet::new();
    let mut internal_refs = BTreeMap::<HirLabelId, usize>::new();
    let mut has_duplicate = false;
    for stmt in stmts {
        visit_stmt_structure(stmt, &mut |stmt| match stmt {
            HirStmt::Label(label) => has_duplicate |= !labels.insert(label.id),
            HirStmt::Goto(goto) => *internal_refs.entry(goto.target).or_default() += 1,
            _ => {}
        });
    }
    if has_duplicate {
        return Err(LexicalCfgFailure::AmbiguousLabel);
    }
    if labels.iter().any(|label| {
        owner_label_refs.get(label).copied().unwrap_or_default()
            != internal_refs.get(label).copied().unwrap_or_default()
    }) {
        return Err(LexicalCfgFailure::ExternalEntry);
    }
    Ok(())
}

pub(super) struct LexicalCfg {
    successors: Vec<BTreeSet<usize>>,
    has_external_exit: bool,
    linear_forward_labels: Option<BTreeMap<HirLabelId, usize>>,
}

/// 仅在一次 HIR topology 快照中有效的节点身份。
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct HirFlowNodeId(usize);

impl HirFlowNodeId {
    pub(super) const fn index(self) -> usize {
        self.0
    }
}

/// 仅在一次 HIR topology 快照中关联 generic-for init/dispatch/binding 的身份。
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct HirFlowProtocolId(usize);

/// Structure 已折叠成源码 generic-for 后仍必须保留的运行时协议节点 owner。
#[derive(Clone, Copy)]
pub(super) struct HirGenericForFlow<'a> {
    protocol: HirFlowProtocolId,
    stmt: &'a HirStmt,
    for_stmt: &'a HirGenericFor,
}

impl<'a> HirGenericForFlow<'a> {
    pub(super) const fn protocol(self) -> HirFlowProtocolId {
        self.protocol
    }

    pub(super) const fn stmt(self) -> &'a HirStmt {
        self.stmt
    }

    pub(super) const fn for_stmt(self) -> &'a HirGenericFor {
        self.for_stmt
    }
}

/// 节点上需要由消费者执行的 HIR 语义事件。
///
/// generic-for 的 init/dispatch/binding 共享一个 snapshot-scoped protocol id：init 只
/// 求值一次 iterator pack，dispatch 每轮（包括最终退出前）调用被冻结的 iterator，binding
/// 只在分派选择新一轮后写入。因此退出边不会错误承载一次并未发生的源码 binding 写入。
/// `RepeatCondition` 独立表达 latch，使 lifetime consumer
/// 能在条件观测前检查 body 中仍存活的 binding。函数 owner 还把显式 `return` 与正常落底
/// 汇入 `FunctionExit`，而无法归属的控制转移进入 `UnknownControl`。
#[derive(Clone, Copy)]
pub(super) enum HirFlowNodeKind<'a> {
    Exit,
    FunctionExit,
    UnknownControl,
    Stmt(&'a HirStmt),
    GenericForInit(HirGenericForFlow<'a>),
    RepeatCondition(&'a HirRepeat),
    NumericForDispatch,
    GenericForDispatch(HirGenericForFlow<'a>),
    ForBinding(HirForBindings<'a>),
}

/// for 每轮成功分派后由 VM 写入的源码 binding。
#[derive(Clone, Copy)]
pub(super) enum HirForBindings<'a> {
    Numeric(LocalId),
    Generic(HirGenericForFlow<'a>),
}

pub(super) struct HirFlowNode<'a> {
    owner_stmt: Option<&'a HirStmt>,
    kind: HirFlowNodeKind<'a>,
    successors: BTreeMap<HirFlowNodeId, Option<bool>>,
}

impl<'a> HirFlowNode<'a> {
    /// 当前图快照中的原始语句身份；一个循环语句可拥有多个求值/控制事件。
    pub(super) const fn owner_stmt(&self) -> Option<&'a HirStmt> {
        self.owner_stmt
    }

    pub(super) const fn kind(&self) -> HirFlowNodeKind<'a> {
        self.kind
    }

    /// 条件求值事件的原始表达式；for dispatch 不属于表达式 truthiness 分支。
    pub(super) fn condition(&self) -> Option<&'a HirExpr> {
        match self.kind {
            HirFlowNodeKind::Stmt(HirStmt::If(stmt)) => Some(&stmt.cond),
            HirFlowNodeKind::Stmt(HirStmt::While(stmt)) => Some(&stmt.cond),
            HirFlowNodeKind::RepeatCondition(stmt) => Some(&stmt.cond),
            _ => None,
        }
    }

    /// None 是无约束边；同一条件的真假出口相同时也合并为无约束边。
    pub(super) fn successors(&self) -> &BTreeMap<HirFlowNodeId, Option<bool>> {
        &self.successors
    }
}

/// 条件边上的状态细化；矛盾路径不安装输入，也不参与合流。
pub(super) enum FlowRefinement<S> {
    Unchanged,
    Refined(S),
    Unreachable,
}

/// 当前 proto HIR 树的 owner-wide 控制流 topology。
///
/// 图只借用 HIR 节点，必须在对应树发生改写前丢弃。它不附带任何特定 pass 的
/// lattice，避免 root、liveness 和 reaching-def 因为共享 topology 而被耦合在一起。
pub(super) struct HirFlowGraph<'a> {
    nodes: Vec<HirFlowNode<'a>>,
    // 只在前向求解时冻结最终入边的 0/1/多条分类；可达性/SCC 查询不分配此表。
    incoming_multiplicity: OnceCell<Box<[u8]>>,
    entry: HirFlowNodeId,
    exit: HirFlowNodeId,
    goto_edges: Vec<(HirFlowNodeId, OwnerLabelLocation)>,
    unresolved_gotos: Vec<(HirFlowNodeId, HirLabelId)>,
}

impl<'a> HirFlowGraph<'a> {
    pub(super) fn for_block(
        block: &'a HirBlock,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        Self::for_stmts(&block.stmts, safety)
    }

    /// 为当前 HIR 快照中的连续语句 region 构造完整 topology。
    ///
    /// region 外的 `break` / `continue` 都是终止边；未能在 region 内解析的 goto
    /// 会单独保留来源，消费者可在可达性计算后决定是否拒绝该输入。
    pub(super) fn for_stmts(
        stmts: &'a [HirStmt],
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        HirFlowGraphBuilder::new(safety, HirFlowBoundary::Region).build(stmts)
    }

    /// 为完整函数 owner 构造 topology。
    ///
    /// 与 region 图不同，函数图把 `return` 和正常落底接到同一个函数出口；无法归属的
    /// goto/break/continue 则接到 conservative unknown sink。需要在函数结束观测 TBC、
    /// closure 或其它生命周期事实的 consumer 应使用此入口。
    pub(super) fn for_proto(
        block: &'a HirBlock,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        HirFlowGraphBuilder::new(safety, HirFlowBoundary::Function).build(&block.stmts)
    }

    pub(super) const fn exit(&self) -> HirFlowNodeId {
        self.exit
    }

    pub(super) fn nodes(&self) -> &[HirFlowNode<'a>] {
        &self.nodes
    }

    /// 在同一 topology 快照上求前向抽象状态不动点。
    ///
    /// `None` 仅表示不可达，首次到达直接安装状态；之后由 consumer 的 `join` 区分
    /// may-union 与 must-intersection。`transfer` 只解释当前 typed event，不重复建边。
    /// `refine` 只在有极性的条件边上调用；矛盾边不参与合流。它必须随输入状态的
    /// 单调变化而单调：弱化输入可以使原先矛盾的边可达，不能撤回已传播的状态。
    /// consumer 必须使用有限单调域和单调 transfer，并仅在 join 改变状态时返回 true；观察副产物也
    /// 必须单调合并，因为回边可能使同一节点再次执行。返回值只保存 consumer 从当前
    /// 事件投影出的结果，不强迫它保存整份输入状态再重放 transfer。
    /// 单前驱节点消费并移动状态，只有入口和合流点保存用于不动点比较的输入；每个
    /// 入口可达环必经这类 checkpoint，因此线性链无需按语句复制不断增长的状态。
    pub(super) fn solve_forward<S: Clone, R>(
        &self,
        initial: S,
        mut join: impl FnMut(&mut S, &S) -> bool,
        mut transfer: impl FnMut(HirFlowNodeId, HirFlowNodeKind<'a>, &mut S) -> R,
        mut refine: impl FnMut(&'a HirExpr, bool, &S) -> FlowRefinement<S>,
    ) -> Vec<Option<R>> {
        let incoming_edges = self.incoming_multiplicity.get_or_init(|| {
            let mut incoming = vec![0u8; self.nodes.len()];
            for node in &self.nodes {
                for successor in node.successors().keys() {
                    let count = &mut incoming[successor.index()];
                    *count = (*count + 1).min(2);
                }
            }
            incoming.into_boxed_slice()
        });
        let mut results = std::iter::repeat_with(|| None)
            .take(self.nodes.len())
            .collect::<Vec<_>>();
        let mut entries = vec![None; self.nodes.len()];
        entries[self.entry.index()] = Some(initial);
        let mut pending = VecDeque::from([self.entry]);
        let mut queued = vec![false; self.nodes.len()];
        queued[self.entry.index()] = true;
        while let Some(id) = pending.pop_front() {
            queued[id.index()] = false;
            let entry = &mut entries[id.index()];
            let mut output = if id == self.entry || incoming_edges[id.index()] > 1 {
                entry.clone()
            } else {
                entry.take()
            }
            .expect("queued HIR flow node must be reachable");
            let node = &self.nodes[id.index()];
            results[id.index()] = Some(transfer(id, node.kind(), &mut output));
            propagate_flow_state(
                output,
                node.successors()
                    .iter()
                    .map(|(&target, &truthy)| (target, truthy)),
                &mut entries,
                &mut pending,
                &mut queued,
                &mut join,
                |truthy, state| match truthy {
                    Some(truthy) => refine(
                        node.condition()
                            .expect("condition edge has a condition owner"),
                        truthy,
                        state,
                    ),
                    None => FlowRefinement::Unchanged,
                },
            );
        }
        results
    }

    /// 在入口可达子图上求后向抽象状态不动点，由 consumer 投影所需结果。
    ///
    /// 所有可达节点从 lattice 的 bottom 开始执行，包含无法到达函数出口的循环；
    /// 否则无限循环中的读取会被错误视为不可观察。
    /// 此查询使用静态 topology，不消费前向路径条件的细化结果。
    /// `transfer` 从输出状态计算输入状态，`join` 将它传播到前驱。
    /// 图负责方向与调度；consumer 只提供有限单调域及当前 typed event 的 gen/kill。
    /// 入口、分支和合流点保留状态用于收敛比较，线性链直接转交状态。每个入口可达环
    /// 必含入口或多前驱节点，因此无出口环也有 checkpoint。观察副产物必须单调合并，
    /// 需要输出快照时在 transfer 改写状态前投影，不能在中间迭代批准删除。
    pub(super) fn solve_backward<S: Clone>(
        &self,
        bottom: S,
        mut join: impl FnMut(&mut S, &S) -> bool,
        mut transfer: impl FnMut(HirFlowNodeId, HirFlowNodeKind<'a>, &mut S),
    ) {
        let reachable = self.reachable();
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for (source, node) in self.nodes.iter().enumerate() {
            if reachable[source] {
                for successor in node.successors().keys() {
                    predecessors[successor.index()].push(HirFlowNodeId(source));
                }
            }
        }
        let mut outputs = vec![None; self.nodes.len()];
        let mut pending = reachable
            .iter()
            .enumerate()
            .filter_map(|(index, &is_reachable)| is_reachable.then_some(HirFlowNodeId(index)))
            .collect::<VecDeque<_>>();
        let mut queued = reachable;
        while let Some(id) = pending.pop_front() {
            queued[id.index()] = false;
            let output = &mut outputs[id.index()];
            let mut input = if id == self.entry
                || self.nodes[id.index()].successors().len() > 1
                || predecessors[id.index()].len() > 1
            {
                output.get_or_insert_with(|| bottom.clone()).clone()
            } else {
                output.take().unwrap_or_else(|| bottom.clone())
            };
            transfer(id, self.nodes[id.index()].kind(), &mut input);
            propagate_flow_state(
                input,
                predecessors[id.index()]
                    .iter()
                    .map(|&target| (target, None)),
                &mut outputs,
                &mut pending,
                &mut queued,
                &mut join,
                |_, _| FlowRefinement::Unchanged,
            );
        }
    }

    pub(super) fn reachable(&self) -> Vec<bool> {
        let mut reachable = vec![false; self.nodes.len()];
        reachable[self.entry.index()] = true;
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            for &successor in self.nodes[node.index()].successors().keys() {
                if !reachable[successor.index()] {
                    reachable[successor.index()] = true;
                    pending.push(successor);
                }
            }
        }
        reachable
    }

    pub(super) fn has_reachable_unresolved_goto(&self) -> bool {
        if self.unresolved_gotos.is_empty() {
            return false;
        }
        let reachable = self.reachable();
        self.unresolved_gotos
            .iter()
            .any(|(source, _)| reachable[source.index()])
    }

    fn reachable_components(&self) -> Vec<Option<usize>> {
        let traversal = crate::graph::depth_first(
            self.nodes.len(),
            self.entry,
            HirFlowNodeId::index,
            |_| true,
            |node| self.nodes[node.index()].successors().keys().copied(),
        );
        let mut predecessors = vec![Vec::new(); self.nodes.len()];
        for &source in &traversal.postorder {
            for successor in self.nodes[source.index()].successors().keys() {
                predecessors[successor.index()].push(source);
            }
        }
        let components = crate::graph::strongly_connected_components(
            self.nodes.len(),
            &traversal.postorder,
            HirFlowNodeId::index,
            |node| predecessors[node.index()].iter().copied(),
        );
        let mut membership = vec![None; self.nodes.len()];
        for (component, members) in components.iter().enumerate() {
            for node in members {
                membership[node.index()] = Some(component);
            }
        }
        membership
    }
}

/// 两个方向共用状态交接：已有输入只借用状态合流，空输入才需要所有权。
/// 最后一条边可直接移动状态，避免在线性链或已建立的循环 checkpoint 上复制集合。
fn propagate_flow_state<S: Clone>(
    state: S,
    edges: impl Iterator<Item = (HirFlowNodeId, Option<bool>)>,
    entries: &mut [Option<S>],
    pending: &mut VecDeque<HirFlowNodeId>,
    queued: &mut [bool],
    join: &mut impl FnMut(&mut S, &S) -> bool,
    mut refine: impl FnMut(Option<bool>, &S) -> FlowRefinement<S>,
) {
    let mut state = Some(state);
    let mut edges = edges.peekable();
    while let Some((target, truthy)) = edges.next() {
        let mut refined = match refine(truthy, state.as_ref().expect("remaining edges share state"))
        {
            FlowRefinement::Unchanged => None,
            FlowRefinement::Refined(state) => Some(state),
            FlowRefinement::Unreachable => continue,
        };
        let changed = match &mut entries[target.index()] {
            Some(current) => join(
                current,
                refined
                    .as_ref()
                    .or(state.as_ref())
                    .expect("edge has a state"),
            ),
            entry @ None => {
                *entry = if refined.is_some() {
                    refined.take()
                } else if edges.peek().is_none() {
                    state.take()
                } else {
                    state.clone()
                };
                true
            }
        };
        if changed && !queued[target.index()] {
            queued[target.index()] = true;
            pending.push_back(target);
        }
    }
}

/// proto owner 内一个词法 block 的稳定路径。
///
/// 路径只在 owner-wide CFG 收集与同一次原地改写之间存活；每一步记录父 block 的语句
/// 索引以及进入的子 block 种类。调用方应先处理子 block、最后再压缩父 block，保证路径
/// 在查询期间不因删除语句而漂移。
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct LexicalBlockPath(Vec<LexicalBlockStep>);

impl LexicalBlockPath {
    pub(super) fn root() -> Self {
        Self::default()
    }

    /// 临时导航共享路径栈，先恢复父路径再返回，包括未形成子图的 None/Err。
    pub(super) fn with_child<R>(
        &mut self,
        stmt_index: usize,
        kind: LexicalBlockKind,
        visit: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.0.push(LexicalBlockStep { stmt_index, kind });
        let result = visit(self);
        self.0.pop();
        result
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum LexicalBlockKind {
    Then,
    Else,
    Body,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct LexicalBlockStep {
    stmt_index: usize,
    kind: LexicalBlockKind,
}

/// proto owner 内由真实可达 goto 环形成的词法重入边界。
///
/// block-local `LexicalCfg` 只能看出某个 label 有外部引用，无法区分一次性的前向入口与
/// 从目标可返回源点的回边。这里先建立完整 owner CFG，再只为处于同一可达环的
/// goto/label 对记录目标边界；嵌套 label 同时把包含它的祖先语句记为边界，使只理解
/// block 前缀的 consumer 不会越过一次真实的跨层重入。
#[derive(Clone, Debug, Default)]
pub(super) struct OwnerReentryFacts {
    first_target_by_block: BTreeMap<LexicalBlockPath, usize>,
}

impl OwnerReentryFacts {
    pub(super) fn collect(
        block: &HirBlock,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        let graph = HirFlowGraph::for_block(block, safety)?;
        let mut facts = Self::default();
        if graph.goto_edges.is_empty() {
            return Ok(facts);
        }
        let components = graph.reachable_components();
        for (source, target) in &graph.goto_edges {
            // source -> target 已是实际 goto 边；同一可达 SCC 恰好证明 target 能回到 source。
            if components[source.index()].is_some()
                && components[source.index()] == components[target.node.index()]
            {
                facts.note_target(target);
            }
        }
        Ok(facts)
    }

    pub(super) fn first_reentry_target(&self, block: &LexicalBlockPath) -> Option<usize> {
        self.first_target_by_block.get(block).copied()
    }

    fn note_target(&mut self, target: &OwnerLabelLocation) {
        let mut ancestor = LexicalBlockPath::root();
        for step in &target.block.0 {
            self.note_block_target(&ancestor, step.stmt_index);
            ancestor.0.push(*step);
        }
        self.note_block_target(&target.block, target.stmt_index);
    }

    fn note_block_target(&mut self, block: &LexicalBlockPath, target: usize) {
        self.first_target_by_block
            .entry(block.clone())
            .and_modify(|first| *first = (*first).min(target))
            .or_insert(target);
    }
}

#[derive(Clone)]
struct OwnerLabelLocation {
    node: HirFlowNodeId,
    block: LexicalBlockPath,
    stmt_index: usize,
}

#[derive(Clone, Copy)]
struct HirLoopTargets {
    break_target: Option<HirFlowNodeId>,
    continue_target: Option<HirFlowNodeId>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum HirFlowBoundary {
    Region,
    Function,
}

struct HirFlowGraphBuilder<'a> {
    nodes: Vec<HirFlowNode<'a>>,
    labels: BTreeMap<HirLabelId, OwnerLabelLocation>,
    pending_gotos: Vec<(HirFlowNodeId, HirLabelId)>,
    safety: HirExprSafety,
    boundary: HirFlowBoundary,
    function_exit: Option<HirFlowNodeId>,
    unknown_control: Option<HirFlowNodeId>,
    next_protocol: usize,
}

impl<'a> HirFlowGraphBuilder<'a> {
    fn new(safety: HirExprSafety, boundary: HirFlowBoundary) -> Self {
        Self {
            nodes: Vec::new(),
            labels: BTreeMap::new(),
            pending_gotos: Vec::new(),
            safety,
            boundary,
            function_exit: None,
            unknown_control: None,
            next_protocol: 0,
        }
    }

    fn build(mut self, stmts: &'a [HirStmt]) -> Result<HirFlowGraph<'a>, LexicalCfgFailure> {
        let exit = match self.boundary {
            HirFlowBoundary::Region => self.new_node(None, HirFlowNodeKind::Exit, []),
            HirFlowBoundary::Function => {
                let exit = self.new_node(None, HirFlowNodeKind::FunctionExit, []);
                let unknown = self.new_node(None, HirFlowNodeKind::UnknownControl, [exit]);
                self.function_exit = Some(exit);
                self.unknown_control = Some(unknown);
                exit
            }
        };
        let entry = self
            .build_block(
                stmts,
                &mut LexicalBlockPath::root(),
                exit,
                HirLoopTargets {
                    break_target: None,
                    continue_target: None,
                },
            )
            .ok_or(LexicalCfgFailure::AmbiguousLabel)?;

        let mut goto_edges = Vec::with_capacity(self.pending_gotos.len());
        let mut unresolved_gotos = Vec::new();
        for (source, label) in std::mem::take(&mut self.pending_gotos) {
            let Some(location) = self.labels.get(&label).cloned() else {
                unresolved_gotos.push((source, label));
                if let Some(unknown) = self.unknown_control {
                    self.nodes[source.index()].successors.insert(unknown, None);
                }
                continue;
            };
            self.nodes[source.index()]
                .successors
                .insert(location.node, None);
            goto_edges.push((source, location));
        }

        Ok(HirFlowGraph {
            nodes: self.nodes,
            incoming_multiplicity: OnceCell::new(),
            entry,
            exit,
            goto_edges,
            unresolved_gotos,
        })
    }

    fn new_node(
        &mut self,
        owner_stmt: Option<&'a HirStmt>,
        kind: HirFlowNodeKind<'a>,
        successors: impl IntoIterator<Item = HirFlowNodeId>,
    ) -> HirFlowNodeId {
        let id = HirFlowNodeId(self.nodes.len());
        self.nodes.push(HirFlowNode {
            owner_stmt,
            kind,
            successors: successors
                .into_iter()
                .map(|target| (target, None))
                .collect(),
        });
        id
    }

    fn set_condition_successors(
        &mut self,
        condition: HirFlowNodeId,
        truthy: HirFlowNodeId,
        falsy: HirFlowNodeId,
    ) {
        let node = &mut self.nodes[condition.index()];
        let known = expr_truthiness(
            node.condition().expect("condition node has an expression"),
            self.safety,
        );
        match known {
            Some(value) => {
                node.successors
                    .insert(if value { truthy } else { falsy }, Some(value));
            }
            None if truthy == falsy => {
                node.successors.insert(truthy, None);
            }
            None => {
                node.successors
                    .extend([(truthy, Some(true)), (falsy, Some(false))]);
            }
        }
    }

    fn build_block(
        &mut self,
        stmts: &'a [HirStmt],
        path: &mut LexicalBlockPath,
        next: HirFlowNodeId,
        loop_targets: HirLoopTargets,
    ) -> Option<HirFlowNodeId> {
        let mut entry = next;
        for (index, stmt) in stmts.iter().enumerate().rev() {
            entry = self.build_stmt(stmt, path, index, entry, loop_targets)?;
        }
        Some(entry)
    }

    fn build_stmt(
        &mut self,
        stmt: &'a HirStmt,
        path: &mut LexicalBlockPath,
        stmt_index: usize,
        next: HirFlowNodeId,
        loop_targets: HirLoopTargets,
    ) -> Option<HirFlowNodeId> {
        match stmt {
            HirStmt::LocalRootRelease(_) => {
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), [next]))
            }
            HirStmt::Label(label) => {
                let node = self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), [next]);
                let location = OwnerLabelLocation {
                    node,
                    block: path.clone(),
                    stmt_index,
                };
                if self.labels.insert(label.id, location).is_some() {
                    return None;
                }
                Some(node)
            }
            HirStmt::Goto(goto) => {
                let node = self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), []);
                self.pending_gotos.push((node, goto.target));
                Some(node)
            }
            HirStmt::Break => {
                let target = loop_targets.break_target.or(self.unknown_control);
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), target))
            }
            HirStmt::Continue => {
                let target = loop_targets.continue_target.or(self.unknown_control);
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), target))
            }
            HirStmt::Return(_) => {
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), self.function_exit))
            }
            HirStmt::Block(block) => path.with_child(stmt_index, LexicalBlockKind::Body, |path| {
                self.build_block(&block.stmts, path, next, loop_targets)
            }),
            HirStmt::If(if_stmt) => {
                let then_entry = path.with_child(stmt_index, LexicalBlockKind::Then, |path| {
                    self.build_block(&if_stmt.then_block.stmts, path, next, loop_targets)
                })?;
                let else_entry = if let Some(block) = &if_stmt.else_block {
                    path.with_child(stmt_index, LexicalBlockKind::Else, |path| {
                        self.build_block(&block.stmts, path, next, loop_targets)
                    })?
                } else {
                    next
                };
                let condition = self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), []);
                self.set_condition_successors(condition, then_entry, else_entry);
                Some(condition)
            }
            HirStmt::While(while_stmt) => {
                let condition = self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), []);
                let body = path.with_child(stmt_index, LexicalBlockKind::Body, |path| {
                    self.build_block(
                        &while_stmt.body.stmts,
                        path,
                        condition,
                        HirLoopTargets {
                            break_target: Some(next),
                            continue_target: Some(condition),
                        },
                    )
                })?;
                self.set_condition_successors(condition, body, next);
                Some(condition)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let condition = self.new_node(
                    Some(stmt),
                    HirFlowNodeKind::RepeatCondition(repeat_stmt),
                    [],
                );
                let body = path.with_child(stmt_index, LexicalBlockKind::Body, |path| {
                    self.build_block(
                        &repeat_stmt.body.stmts,
                        path,
                        condition,
                        HirLoopTargets {
                            break_target: Some(next),
                            continue_target: Some(condition),
                        },
                    )
                })?;
                self.set_condition_successors(condition, next, body);
                Some(body)
            }
            HirStmt::NumericFor(for_stmt) => {
                let dispatch = self.new_node(Some(stmt), HirFlowNodeKind::NumericForDispatch, []);
                let binding = self.new_node(
                    Some(stmt),
                    HirFlowNodeKind::ForBinding(HirForBindings::Numeric(for_stmt.binding)),
                    [],
                );
                let body = path.with_child(stmt_index, LexicalBlockKind::Body, |path| {
                    self.build_block(
                        &for_stmt.body.stmts,
                        path,
                        dispatch,
                        HirLoopTargets {
                            break_target: Some(next),
                            continue_target: Some(dispatch),
                        },
                    )
                })?;
                self.nodes[binding.index()].successors.insert(body, None);
                self.nodes[dispatch.index()]
                    .successors
                    .extend([(binding, None), (next, None)]);
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), [dispatch]))
            }
            HirStmt::GenericFor(for_stmt) => {
                let flow = HirGenericForFlow {
                    protocol: HirFlowProtocolId(self.next_protocol),
                    stmt,
                    for_stmt,
                };
                self.next_protocol += 1;
                let dispatch =
                    self.new_node(Some(stmt), HirFlowNodeKind::GenericForDispatch(flow), []);
                let binding = self.new_node(
                    Some(stmt),
                    HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)),
                    [],
                );
                let body = path.with_child(stmt_index, LexicalBlockKind::Body, |path| {
                    self.build_block(
                        &for_stmt.body.stmts,
                        path,
                        dispatch,
                        HirLoopTargets {
                            break_target: Some(next),
                            continue_target: Some(dispatch),
                        },
                    )
                })?;
                self.nodes[binding.index()].successors.insert(body, None);
                self.nodes[dispatch.index()]
                    .successors
                    .extend([(binding, None), (next, None)]);
                Some(self.new_node(
                    Some(stmt),
                    HirFlowNodeKind::GenericForInit(flow),
                    [dispatch],
                ))
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_) => {
                Some(self.new_node(Some(stmt), HirFlowNodeKind::Stmt(stmt), [next]))
            }
        }
    }
}

impl LexicalCfg {
    pub(super) fn analyze(
        stmts: &[HirStmt],
        owner_label_refs: &BTreeMap<HirLabelId, usize>,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        validate_region_entry(stmts, owner_label_refs)?;

        let direct_labels = stmts
            .iter()
            .enumerate()
            .filter_map(|(index, stmt)| match stmt {
                HirStmt::Label(label) => Some((label.id, index)),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut successors = vec![BTreeSet::<usize>::new(); stmts.len()];
        let mut has_external_exit = false;
        for (index, stmt) in stmts.iter().enumerate() {
            let graph = HirFlowGraph::for_stmts(std::slice::from_ref(stmt), safety)?;
            let reachable = graph.reachable();
            if index + 1 < stmts.len() && reachable[graph.exit().index()] {
                successors[index].insert(index + 1);
            }
            for (source, target) in &graph.unresolved_gotos {
                if !reachable[source.index()] {
                    continue;
                }
                if let Some(&target_index) = direct_labels.get(target) {
                    successors[index].insert(target_index);
                } else {
                    has_external_exit = true;
                }
            }
        }
        // 线性 consumer 只会显式跳过当前 block 的 direct forward goto；嵌套 block
        // 内部自含的回环已经投影成当前语句的正常出口，仍可
        // 安全交给递归 analyzer。若嵌套 goto 指向本层 label，当前非 Goto 语句会出现
        // 非顺序 successor，因而不能伪装成普通 fallthrough。
        let linear_forward_labels = (!has_external_exit
            && stmts.iter().enumerate().all(|(index, stmt)| {
                let stmt_successors = &successors[index];
                match stmt {
                    HirStmt::Goto(_) => {
                        stmt_successors.len() == 1
                            && stmt_successors
                                .first()
                                .is_some_and(|target| *target > index)
                    }
                    _ => {
                        stmt_successors.is_empty()
                            || (stmt_successors.len() == 1
                                && stmt_successors.contains(&(index + 1)))
                    }
                }
            }))
        .then_some(direct_labels);

        Ok(Self {
            successors,
            has_external_exit,
            linear_forward_labels,
        })
    }

    pub(super) fn successors(&self) -> &[BTreeSet<usize>] {
        &self.successors
    }

    pub(super) fn has_external_exit(&self) -> bool {
        self.has_external_exit
    }

    /// 返回可由单调词法 walker 精确消费的 direct label 索引。
    ///
    /// 成功意味着当前 block 没有外部 goto 出口，direct goto 只严格向前，且所有非
    /// Goto 语句在本层只会正常落到下一句。嵌套结构内部可以包含自洽回环；它们由嵌套
    /// analyzer 自己处理，不会再让整个外层 block 丢失入口事实。
    pub(super) fn linear_forward_labels(&self) -> Option<&BTreeMap<HirLabelId, usize>> {
        self.linear_forward_labels.as_ref()
    }

    /// 按直接语句位置发布“该声明支配所有可达后缀语句”；不可达声明为 false。
    ///
    /// 新 local 的词法作用域延伸到 block 末尾，入口绕过声明会造成非法跳入 scope。
    /// 支配树的子树区间必须包含后缀全部可达节点的 preorder；反向维护其最小/最大值，
    /// 即可一次得到所有声明的结论，无需逐个删除节点重新搜索。结果仅属于当前 CFG 快照。
    pub(super) fn suffix_dominance(&self) -> Vec<bool> {
        let count = self.successors.len();
        let mut predecessors = vec![Vec::new(); count];
        for (source, targets) in self.successors.iter().enumerate() {
            for &target in targets {
                predecessors[target].push(source);
            }
        }
        let traversal = crate::graph::depth_first(
            count,
            0,
            |node| node,
            |_| count != 0,
            |node| self.successors[node].iter().copied(),
        );
        let dominance = crate::graph::dominator_tree(
            &traversal,
            |node| node,
            |node| node,
            |node| predecessors[node].iter().copied(),
        )
        .expect("lexical CFG traversal must define a valid dominance tree");
        let mut result = vec![false; count];
        let mut later: Option<(usize, usize)> = None;
        for index in (0..count).rev() {
            if let Some(start) = dominance.preorder_index[index] {
                let end = dominance.subtree_end[index]
                    .expect("reachable dominator must have a subtree interval");
                result[index] = later.is_none_or(|(min, max)| start <= min && max < end);
                later = Some(later.map_or((start, start), |(min, max)| {
                    (min.min(start), max.max(start))
                }));
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirGenericFor, HirGlobalRef, HirIf, HirValuePack, HirWhile};

    #[test]
    fn coincident_condition_exits_merge_without_refinement() {
        let block = HirBlock {
            stmts: vec![HirStmt::If(Box::new(HirIf {
                cond: HirExpr::LocalRef(LocalId(0)),
                then_block: HirBlock::default(),
                else_block: None,
            }))],
        };
        let graph =
            HirFlowGraph::for_block(&block, HirExprSafety::for_dialect(DecompileDialect::Lua54))
                .unwrap();
        let condition = &graph.nodes()[graph.entry.index()];
        let HirStmt::If(stmt) = &block.stmts[0] else {
            unreachable!()
        };
        assert!(std::ptr::eq(condition.condition().unwrap(), &stmt.cond));
        assert_eq!(
            condition.successors(),
            &BTreeMap::from([(graph.exit(), None)])
        );
        for initial in [7, 19] {
            let outputs = graph.solve_forward(
                initial,
                |_, _| panic!("a linear path has no joins"),
                |_, _, state| *state,
                |_, _, _| panic!("coincident exits impose no condition"),
            );
            assert_eq!(outputs[graph.exit().index()], Some(initial));
        }
    }

    #[test]
    fn contradictory_exit_becomes_reachable_after_loop_join() {
        let block = HirBlock {
            stmts: vec![HirStmt::While(Box::new(HirWhile {
                cond: HirExpr::LocalRef(LocalId(0)),
                body: HirBlock {
                    stmts: vec![HirStmt::Continue],
                },
            }))],
        };
        let graph =
            HirFlowGraph::for_block(&block, HirExprSafety::for_dialect(DecompileDialect::Lua54))
                .unwrap();
        // 两位分别表示可能的真/假值；正文将条件改为假，回边使入口从仅真弱化为真假皆可。
        let mut exit_attempts = Vec::new();
        let mut condition_visits = 0;
        let mut exit_visits = 0;
        let outputs = graph.solve_forward(
            1u8,
            |current, incoming| {
                let merged = *current | *incoming;
                let changed = *current != merged;
                *current = merged;
                changed
            },
            |_, kind, state| {
                match kind {
                    HirFlowNodeKind::Stmt(HirStmt::While(_)) => condition_visits += 1,
                    HirFlowNodeKind::Stmt(HirStmt::Continue) => *state = 2,
                    HirFlowNodeKind::Exit => exit_visits += 1,
                    _ => {}
                }
                *state
            },
            |_, truthy, state| {
                let refined = *state & if truthy { 1 } else { 2 };
                if !truthy {
                    exit_attempts.push(refined);
                }
                if refined == 0 {
                    FlowRefinement::Unreachable
                } else if refined == *state {
                    FlowRefinement::Unchanged
                } else {
                    FlowRefinement::Refined(refined)
                }
            },
        );
        assert_eq!(exit_attempts, [0, 2]);
        assert_eq!(outputs[graph.exit().index()], Some(2));
        assert_eq!(condition_visits, 2);
        assert_eq!(exit_visits, 1);
    }

    #[test]
    fn generic_for_protocol_orders_init_dispatch_and_success_binding() {
        let block = HirBlock {
            stmts: vec![HirStmt::GenericFor(Box::new(HirGenericFor {
                bindings: vec![LocalId(0)],
                iterator: HirValuePack::fixed(vec![HirExpr::GlobalRef(HirGlobalRef {
                    key: "next".into(),
                })]),
                body: HirBlock::default(),
                initializer_transaction: None,
                initializer_roots: Vec::new(),
                dispatch_results: Vec::new(),
            }))],
        };
        let graph =
            HirFlowGraph::for_block(&block, HirExprSafety::for_dialect(DecompileDialect::Lua54))
                .expect("generic-for topology must be valid");

        let mut init = None;
        let mut dispatch = None;
        let mut binding = None;
        for (index, node) in graph.nodes().iter().enumerate() {
            match node.kind() {
                HirFlowNodeKind::GenericForInit(_) => {
                    init = Some(HirFlowNodeId(index));
                }
                HirFlowNodeKind::GenericForDispatch(_) => {
                    dispatch = Some(HirFlowNodeId(index));
                }
                HirFlowNodeKind::ForBinding(HirForBindings::Generic(_)) => {
                    binding = Some(HirFlowNodeId(index));
                }
                _ => {}
            }
        }

        let init = init.expect("generic-for init node");
        let dispatch = dispatch.expect("generic-for dispatch node");
        let binding = binding.expect("generic-for binding node");
        let protocol = match graph.nodes()[init.index()].kind() {
            HirFlowNodeKind::GenericForInit(flow) => flow.protocol(),
            _ => unreachable!(),
        };
        assert!(matches!(
            graph.nodes()[dispatch.index()].kind(),
            HirFlowNodeKind::GenericForDispatch(flow) if flow.protocol() == protocol
        ));
        assert!(matches!(
            graph.nodes()[binding.index()].kind(),
            HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow))
                if flow.protocol() == protocol
        ));
        assert_eq!(
            graph.nodes()[init.index()].successors(),
            &BTreeMap::from([(dispatch, None)])
        );
        assert_eq!(
            graph.nodes()[dispatch.index()].successors(),
            &BTreeMap::from([(binding, None), (graph.exit(), None)])
        );
        assert_eq!(
            graph.nodes()[binding.index()].successors(),
            &BTreeMap::from([(dispatch, None)])
        );
    }
}
