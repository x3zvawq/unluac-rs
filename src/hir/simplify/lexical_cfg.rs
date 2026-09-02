//! 这个文件提供 HIR simplify 共用的词法控制流事实。
//!
//! label 只在其直接 block 建边；嵌套 block 内能够自行解析的 goto 被内部消费，指向父层
//! label 的 goto 则逐层上浮。`break` / `continue` 由最近的 loop owner 消费，恒真/恒假
//! loop 的正常出口使用目标方言 truthiness 事实判定。`HirFlowGraph` 是当前 HIR 树
//! 的 owner-wide topology 单一来源；它区分 for 的一次性求值节点与循环 dispatch，并为
//! dataflow consumer 提供稳定 node id 和后继。block-local `LexicalCfg` 则保留线性
//! rewrite 所需的 successor、外部出口和支配查询。
//! 本模块不推断 temp reaching-def 或 root lifetime；这些仍由具体 pass 结合 promotion facts
//! 判断。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirBlock, HirGenericFor, HirLabelId, HirRepeat, HirStmt, LocalId};
use crate::hir::expr_safety::HirExprSafety;

use super::expr_facts::expr_truthiness;
use super::label_refs::count_label_references;
use super::visit::{HirVisitor, visit_stmts};

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(super) enum LexicalCfgFailure {
    AmbiguousLabel,
    ExternalEntry,
}

pub(super) struct LexicalCfg {
    successors: Vec<BTreeSet<usize>>,
    reachable: Vec<bool>,
    has_external_exit: bool,
    has_label_flow: bool,
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
    kind: HirFlowNodeKind<'a>,
    successors: BTreeSet<HirFlowNodeId>,
}

impl<'a> HirFlowNode<'a> {
    pub(super) const fn kind(&self) -> HirFlowNodeKind<'a> {
        self.kind
    }

    pub(super) fn successors(&self) -> &BTreeSet<HirFlowNodeId> {
        &self.successors
    }
}

/// 当前 proto HIR 树的 owner-wide 控制流 topology。
///
/// 图只借用 HIR 节点，必须在对应树发生改写前丢弃。它不附带任何特定 pass 的
/// lattice，避免 root、liveness 和 reaching-def 因为共享 topology 而被耦合在一起。
pub(super) struct HirFlowGraph<'a> {
    nodes: Vec<HirFlowNode<'a>>,
    entry: HirFlowNodeId,
    exit: HirFlowNodeId,
    goto_edges: Vec<(HirFlowNodeId, OwnerLabelLocation)>,
    unresolved_goto_sources: Vec<HirFlowNodeId>,
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

    pub(super) const fn entry(&self) -> HirFlowNodeId {
        self.entry
    }

    pub(super) const fn exit(&self) -> HirFlowNodeId {
        self.exit
    }

    pub(super) fn nodes(&self) -> &[HirFlowNode<'a>] {
        &self.nodes
    }

    pub(super) fn reachable(&self) -> Vec<bool> {
        let mut reachable = vec![false; self.nodes.len()];
        reachable[self.entry.index()] = true;
        let mut pending = vec![self.entry];
        while let Some(node) = pending.pop() {
            for &successor in self.nodes[node.index()].successors() {
                if !reachable[successor.index()] {
                    reachable[successor.index()] = true;
                    pending.push(successor);
                }
            }
        }
        reachable
    }

    pub(super) fn has_reachable_unresolved_goto(&self) -> bool {
        let reachable = self.reachable();
        self.unresolved_goto_sources
            .iter()
            .any(|source| reachable[source.index()])
    }

    fn node_reaches(&self, start: HirFlowNodeId, target: HirFlowNodeId) -> bool {
        if start == target {
            return true;
        }
        let mut visited = vec![false; self.nodes.len()];
        visited[start.index()] = true;
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            for &successor in self.nodes[node.index()].successors() {
                if successor == target {
                    return true;
                }
                if !visited[successor.index()] {
                    visited[successor.index()] = true;
                    pending.push(successor);
                }
            }
        }
        false
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

    pub(super) fn child(&self, stmt_index: usize, kind: LexicalBlockKind) -> Self {
        let mut path = self.clone();
        path.0.push(LexicalBlockStep { stmt_index, kind });
        path
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
        let reachable = graph.reachable();
        let mut facts = Self::default();
        for (source, target) in &graph.goto_edges {
            if reachable[source.index()] && graph.node_reaches(target.node, *source) {
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
            HirFlowBoundary::Region => self.new_node(HirFlowNodeKind::Exit, []),
            HirFlowBoundary::Function => {
                let exit = self.new_node(HirFlowNodeKind::FunctionExit, []);
                let unknown = self.new_node(HirFlowNodeKind::UnknownControl, [exit]);
                self.function_exit = Some(exit);
                self.unknown_control = Some(unknown);
                exit
            }
        };
        let entry = self
            .build_block(
                stmts,
                &LexicalBlockPath::root(),
                exit,
                HirLoopTargets {
                    break_target: None,
                    continue_target: None,
                },
            )
            .ok_or(LexicalCfgFailure::AmbiguousLabel)?;

        let mut goto_edges = Vec::with_capacity(self.pending_gotos.len());
        let mut unresolved_goto_sources = Vec::new();
        for (source, label) in std::mem::take(&mut self.pending_gotos) {
            let Some(location) = self.labels.get(&label).cloned() else {
                unresolved_goto_sources.push(source);
                if let Some(unknown) = self.unknown_control {
                    self.nodes[source.index()].successors.insert(unknown);
                }
                continue;
            };
            self.nodes[source.index()].successors.insert(location.node);
            goto_edges.push((source, location));
        }

        Ok(HirFlowGraph {
            nodes: self.nodes,
            entry,
            exit,
            goto_edges,
            unresolved_goto_sources,
        })
    }

    fn new_node(
        &mut self,
        kind: HirFlowNodeKind<'a>,
        successors: impl IntoIterator<Item = HirFlowNodeId>,
    ) -> HirFlowNodeId {
        let id = HirFlowNodeId(self.nodes.len());
        self.nodes.push(HirFlowNode {
            kind,
            successors: successors.into_iter().collect(),
        });
        id
    }

    fn build_block(
        &mut self,
        stmts: &'a [HirStmt],
        path: &LexicalBlockPath,
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
        path: &LexicalBlockPath,
        stmt_index: usize,
        next: HirFlowNodeId,
        loop_targets: HirLoopTargets,
    ) -> Option<HirFlowNodeId> {
        match stmt {
            HirStmt::Label(label) => {
                let node = self.new_node(HirFlowNodeKind::Stmt(stmt), [next]);
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
                let node = self.new_node(HirFlowNodeKind::Stmt(stmt), []);
                self.pending_gotos.push((node, goto.target));
                Some(node)
            }
            HirStmt::Break => {
                let target = loop_targets.break_target.or(self.unknown_control);
                Some(self.new_node(HirFlowNodeKind::Stmt(stmt), target))
            }
            HirStmt::Continue => {
                let target = loop_targets.continue_target.or(self.unknown_control);
                Some(self.new_node(HirFlowNodeKind::Stmt(stmt), target))
            }
            HirStmt::Return(_) => {
                Some(self.new_node(HirFlowNodeKind::Stmt(stmt), self.function_exit))
            }
            HirStmt::Block(block) => self.build_block(
                &block.stmts,
                &path.child(stmt_index, LexicalBlockKind::Body),
                next,
                loop_targets,
            ),
            HirStmt::If(if_stmt) => {
                let then_entry = self.build_block(
                    &if_stmt.then_block.stmts,
                    &path.child(stmt_index, LexicalBlockKind::Then),
                    next,
                    loop_targets,
                )?;
                let else_entry = if let Some(block) = &if_stmt.else_block {
                    self.build_block(
                        &block.stmts,
                        &path.child(stmt_index, LexicalBlockKind::Else),
                        next,
                        loop_targets,
                    )?
                } else {
                    next
                };
                let successors = match expr_truthiness(&if_stmt.cond, self.safety) {
                    Some(true) => vec![then_entry],
                    Some(false) => vec![else_entry],
                    None => vec![then_entry, else_entry],
                };
                Some(self.new_node(HirFlowNodeKind::Stmt(stmt), successors))
            }
            HirStmt::While(while_stmt) => {
                let condition = self.new_node(HirFlowNodeKind::Stmt(stmt), []);
                let body = self.build_block(
                    &while_stmt.body.stmts,
                    &path.child(stmt_index, LexicalBlockKind::Body),
                    condition,
                    HirLoopTargets {
                        break_target: Some(next),
                        continue_target: Some(condition),
                    },
                )?;
                match expr_truthiness(&while_stmt.cond, self.safety) {
                    Some(true) => self.nodes[condition.index()].successors.insert(body),
                    Some(false) => self.nodes[condition.index()].successors.insert(next),
                    None => {
                        self.nodes[condition.index()]
                            .successors
                            .extend([body, next]);
                        true
                    }
                };
                Some(condition)
            }
            HirStmt::Repeat(repeat_stmt) => {
                let condition = self.new_node(HirFlowNodeKind::RepeatCondition(repeat_stmt), []);
                let body = self.build_block(
                    &repeat_stmt.body.stmts,
                    &path.child(stmt_index, LexicalBlockKind::Body),
                    condition,
                    HirLoopTargets {
                        break_target: Some(next),
                        continue_target: Some(condition),
                    },
                )?;
                match expr_truthiness(&repeat_stmt.cond, self.safety) {
                    Some(true) => self.nodes[condition.index()].successors.insert(next),
                    Some(false) => self.nodes[condition.index()].successors.insert(body),
                    None => {
                        self.nodes[condition.index()]
                            .successors
                            .extend([body, next]);
                        true
                    }
                };
                Some(body)
            }
            HirStmt::NumericFor(for_stmt) => {
                let dispatch = self.new_node(HirFlowNodeKind::NumericForDispatch, []);
                let binding = self.new_node(
                    HirFlowNodeKind::ForBinding(HirForBindings::Numeric(for_stmt.binding)),
                    [],
                );
                let body = self.build_block(
                    &for_stmt.body.stmts,
                    &path.child(stmt_index, LexicalBlockKind::Body),
                    dispatch,
                    HirLoopTargets {
                        break_target: Some(next),
                        continue_target: Some(dispatch),
                    },
                )?;
                self.nodes[binding.index()].successors.insert(body);
                self.nodes[dispatch.index()]
                    .successors
                    .extend([binding, next]);
                Some(self.new_node(HirFlowNodeKind::Stmt(stmt), [dispatch]))
            }
            HirStmt::GenericFor(for_stmt) => {
                let flow = HirGenericForFlow {
                    protocol: HirFlowProtocolId(self.next_protocol),
                    stmt,
                    for_stmt,
                };
                self.next_protocol += 1;
                let dispatch = self.new_node(HirFlowNodeKind::GenericForDispatch(flow), []);
                let binding = self.new_node(
                    HirFlowNodeKind::ForBinding(HirForBindings::Generic(flow)),
                    [],
                );
                let body = self.build_block(
                    &for_stmt.body.stmts,
                    &path.child(stmt_index, LexicalBlockKind::Body),
                    dispatch,
                    HirLoopTargets {
                        break_target: Some(next),
                        continue_target: Some(dispatch),
                    },
                )?;
                self.nodes[binding.index()].successors.insert(body);
                self.nodes[dispatch.index()]
                    .successors
                    .extend([binding, next]);
                Some(self.new_node(HirFlowNodeKind::GenericForInit(flow), [dispatch]))
            }
            HirStmt::LocalDecl(_)
            | HirStmt::GlobalDecl(_)
            | HirStmt::Assign(_)
            | HirStmt::TableSetList(_)
            | HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::CallStmt(_) => Some(self.new_node(HirFlowNodeKind::Stmt(stmt), [next])),
        }
    }
}

impl LexicalCfg {
    pub(super) fn analyze(
        stmts: &[HirStmt],
        owner_label_refs: &BTreeMap<HirLabelId, usize>,
        safety: HirExprSafety,
    ) -> Result<Self, LexicalCfgFailure> {
        let mut owned_labels = OwnedLabelCollector::default();
        visit_stmts(stmts, &mut owned_labels);
        if owned_labels.has_duplicate {
            return Err(LexicalCfgFailure::AmbiguousLabel);
        }
        let internal_refs = count_label_references(stmts);
        for &label in &owned_labels.labels {
            if owner_label_refs.get(&label).copied().unwrap_or_default()
                != internal_refs.get(&label).copied().unwrap_or_default()
            {
                return Err(LexicalCfgFailure::ExternalEntry);
            }
        }

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
            let summary = summarize_stmt_flow(stmt, safety);
            if index + 1 < stmts.len() && summary.falls_through {
                successors[index].insert(index + 1);
            }
            for target in summary.outgoing_gotos {
                if let Some(&target_index) = direct_labels.get(&target) {
                    successors[index].insert(target_index);
                } else {
                    has_external_exit = true;
                }
            }
        }
        let reachable = reachable_indices(&successors, None);
        // 线性 consumer 只会显式跳过当前 block 的 direct forward goto；嵌套 block
        // 内部自含的回环已经被 summarize_stmt_flow 消费成当前语句的 fallthrough，仍可
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
            reachable,
            has_external_exit,
            has_label_flow: !owned_labels.labels.is_empty()
                || !internal_refs.is_empty()
                || has_external_exit,
            linear_forward_labels,
        })
    }

    pub(super) fn successors(&self) -> &[BTreeSet<usize>] {
        &self.successors
    }

    pub(super) fn has_external_exit(&self) -> bool {
        self.has_external_exit
    }

    pub(super) fn has_label_flow(&self) -> bool {
        self.has_label_flow
    }

    /// 返回可由单调词法 walker 精确消费的 direct label 索引。
    ///
    /// 成功意味着当前 block 没有外部 goto 出口，direct goto 只严格向前，且所有非
    /// Goto 语句在本层只会正常落到下一句。嵌套结构内部可以包含自洽回环；它们由嵌套
    /// analyzer 自己处理，不会再让整个外层 block 丢失入口事实。
    pub(super) fn linear_forward_labels(&self) -> Option<&BTreeMap<HirLabelId, usize>> {
        self.linear_forward_labels.as_ref()
    }

    /// 新 local 的词法作用域从 declaration 延伸到 block 末尾；因此任何入口路径若能
    /// 绕过 declaration 到达后缀 label，改写都会生成未初始化读取或非法跳入 local scope。
    pub(super) fn statement_dominates_suffix(&self, declaration: usize) -> bool {
        if declaration >= self.successors.len() || !self.reachable[declaration] {
            return false;
        }
        let reachable_without_declaration = reachable_indices(&self.successors, Some(declaration));
        !reachable_without_declaration[declaration + 1..]
            .iter()
            .any(|reachable| *reachable)
    }
}

fn reachable_indices(successors: &[BTreeSet<usize>], excluded: Option<usize>) -> Vec<bool> {
    let mut reachable = vec![false; successors.len()];
    if successors.is_empty() || excluded == Some(0) {
        return reachable;
    }
    reachable[0] = true;
    let mut pending = vec![0usize];
    while let Some(index) = pending.pop() {
        for &successor in &successors[index] {
            if excluded != Some(successor) && !reachable[successor] {
                reachable[successor] = true;
                pending.push(successor);
            }
        }
    }
    reachable
}

#[derive(Default)]
struct OwnedLabelCollector {
    labels: BTreeSet<HirLabelId>,
    has_duplicate: bool,
}

impl HirVisitor for OwnedLabelCollector {
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::Label(label) = stmt {
            self.has_duplicate |= !self.labels.insert(label.id);
        }
    }
}

#[derive(Default)]
struct ControlFlowSummary {
    falls_through: bool,
    breaks_loop: bool,
    continues_loop: bool,
    outgoing_gotos: BTreeSet<HirLabelId>,
}

impl ControlFlowSummary {
    fn fallthrough() -> Self {
        Self {
            falls_through: true,
            breaks_loop: false,
            continues_loop: false,
            outgoing_gotos: BTreeSet::new(),
        }
    }

    fn merge(&mut self, other: Self) {
        self.falls_through |= other.falls_through;
        self.breaks_loop |= other.breaks_loop;
        self.continues_loop |= other.continues_loop;
        self.outgoing_gotos.extend(other.outgoing_gotos);
    }
}

fn summarize_stmt_flow(stmt: &HirStmt, safety: HirExprSafety) -> ControlFlowSummary {
    match stmt {
        HirStmt::Goto(goto_stmt) => ControlFlowSummary {
            falls_through: false,
            breaks_loop: false,
            continues_loop: false,
            outgoing_gotos: BTreeSet::from([goto_stmt.target]),
        },
        HirStmt::Break => ControlFlowSummary {
            breaks_loop: true,
            ..ControlFlowSummary::default()
        },
        HirStmt::Continue => ControlFlowSummary {
            continues_loop: true,
            ..ControlFlowSummary::default()
        },
        HirStmt::Return(_) => ControlFlowSummary::default(),
        HirStmt::If(if_stmt) => match expr_truthiness(&if_stmt.cond, safety) {
            Some(true) => summarize_block_flow(&if_stmt.then_block, safety),
            Some(false) => if_stmt
                .else_block
                .as_ref()
                .map_or_else(ControlFlowSummary::fallthrough, |block| {
                    summarize_block_flow(block, safety)
                }),
            None => {
                let mut summary = summarize_block_flow(&if_stmt.then_block, safety);
                if let Some(else_block) = &if_stmt.else_block {
                    summary.merge(summarize_block_flow(else_block, safety));
                } else {
                    summary.falls_through = true;
                }
                summary
            }
        },
        HirStmt::Block(block) => summarize_block_flow(block, safety),
        HirStmt::While(while_stmt) => {
            let truthiness = expr_truthiness(&while_stmt.cond, safety);
            if truthiness == Some(false) {
                return ControlFlowSummary::fallthrough();
            }
            let body = summarize_block_flow(&while_stmt.body, safety);
            ControlFlowSummary {
                falls_through: truthiness != Some(true) || body.breaks_loop,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::Repeat(repeat_stmt) => {
            let body = summarize_block_flow(&repeat_stmt.body, safety);
            let reaches_condition = body.falls_through || body.continues_loop;
            ControlFlowSummary {
                falls_through: body.breaks_loop
                    || (expr_truthiness(&repeat_stmt.cond, safety) != Some(false)
                        && reaches_condition),
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::NumericFor(numeric_for) => {
            let body = summarize_block_flow(&numeric_for.body, safety);
            ControlFlowSummary {
                falls_through: true,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::GenericFor(generic_for) => {
            let body = summarize_block_flow(&generic_for.body, safety);
            ControlFlowSummary {
                falls_through: true,
                breaks_loop: false,
                continues_loop: false,
                outgoing_gotos: body.outgoing_gotos,
            }
        }
        HirStmt::Label(_)
        | HirStmt::LocalDecl(_)
        | HirStmt::GlobalDecl(_)
        | HirStmt::Assign(_)
        | HirStmt::TableSetList(_)
        | HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::CallStmt(_) => ControlFlowSummary::fallthrough(),
    }
}

fn summarize_block_flow(block: &HirBlock, safety: HirExprSafety) -> ControlFlowSummary {
    let direct_labels = block
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| match stmt {
            HirStmt::Label(label) => Some((label.id, index)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let stmt_summaries = block
        .stmts
        .iter()
        .map(|stmt| summarize_stmt_flow(stmt, safety))
        .collect::<Vec<_>>();
    let mut reachable = vec![false; block.stmts.len() + 1];
    reachable[0] = true;
    let mut pending = vec![0usize];
    let mut outgoing_gotos = BTreeSet::new();
    let mut breaks_loop = false;
    let mut continues_loop = false;

    while let Some(index) = pending.pop() {
        if index == block.stmts.len() {
            continue;
        }
        let summary = &stmt_summaries[index];
        breaks_loop |= summary.breaks_loop;
        continues_loop |= summary.continues_loop;
        if summary.falls_through && !reachable[index + 1] {
            reachable[index + 1] = true;
            pending.push(index + 1);
        }
        for &target in &summary.outgoing_gotos {
            if let Some(&target_index) = direct_labels.get(&target) {
                if !reachable[target_index] {
                    reachable[target_index] = true;
                    pending.push(target_index);
                }
            } else {
                outgoing_gotos.insert(target);
            }
        }
    }

    ControlFlowSummary {
        falls_through: reachable[block.stmts.len()],
        breaks_loop,
        continues_loop,
        outgoing_gotos,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::decompile::DecompileDialect;
    use crate::hir::common::{HirExpr, HirGenericFor, HirGlobalRef, HirValuePack};

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
            &BTreeSet::from([dispatch])
        );
        assert_eq!(
            graph.nodes()[dispatch.index()].successors(),
            &BTreeSet::from([binding, graph.exit()])
        );
        assert_eq!(
            graph.nodes()[binding.index()].successors(),
            &BTreeSet::from([dispatch])
        );
    }
}
