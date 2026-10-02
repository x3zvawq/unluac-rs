//! 保存结构化分支与标量决策共同产生的值与状态合流。
//!
//! 消费冻结分支 owner 和 canonical SSA；后层须同时消费整组写入，不能把带副作用的分支当作纯值决策。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct Incoming {
    pub value: TempId,
    pub source: Option<InstrRef>,
    pub literal: Option<value_programs::Literal>,
    pub copy: Option<(HirBinding, HomeSlotKey)>,
    /// 此叶块只有当前写和可选的合流 jump，没有夹带其它事件。
    pub terminal_write: bool,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct ResultValue {
    pub value: TempId,
    pub home: HomeSlotKey,
    pub incoming: Vec<Incoming>,
}

impl ResultValue {
    fn valid(&self, facts: &ProtoPromotionFacts) -> bool {
        facts.trusted_temp_home_slot(self.value) == Some(self.home)
            && self.incoming.iter().all(|incoming| {
                facts.trusted_temp_home_slot(incoming.value) == Some(self.home)
                    && incoming.copy.is_none_or(|(binding, home)| match binding {
                        HirBinding::Temp(temp) => facts.trusted_temp_home_slot(temp) == Some(home),
                        HirBinding::Param(param) => {
                            facts.trusted_param_home_slot(param) == Some(home)
                        }
                        _ => false,
                    })
            })
    }
}

/// 原两臂均写同一 home，但没有运行时读取，因而不存在可供消费的合流 SSA 值。
#[derive(Debug, Clone)]
pub(in crate::hir) struct UnreadValue {
    pub home: HomeSlotKey,
    pub writes: [TempId; 2],
    pub sources: [InstrRef; 2],
    pub literals: [Option<value_programs::Literal>; 2],
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Frame {
    /// 基本块起点可能包含前置语句；它只给出搜索下界，不授权退休此前的所有准备。
    pub begin: InstrRef,
    pub end: InstrRef,
    /// 原合流后的首个操作 PC，用于确认在该边界生效的 debug 初始化身份。
    pub end_pc: Option<u32>,
    pub predicates: Vec<InstrRef>,
    pub results: Vec<ResultValue>,
    /// 原 disposition 仍为 EdgeCopy；只证明其所有入口来自当前分支，不改写 Structure 所有权。
    edge_results: Vec<ResultValue>,
    pub unread: Option<UnreadValue>,
    inputs: Vec<(TempId, HomeSlotKey)>,
}

impl Frame {
    pub(in crate::hir) fn edge_results<'a>(
        &'a self,
        facts: &'a ProtoPromotionFacts,
    ) -> impl Iterator<Item = &'a ResultValue> {
        self.edge_results
            .iter()
            .filter(|result| result.valid(facts))
    }

    pub(super) fn valid(&self, facts: &ProtoPromotionFacts) -> bool {
        self.inputs
            .iter()
            .all(|(value, home)| facts.trusted_temp_home_slot(*value) == Some(*home))
            && self.results.iter().all(|result| result.valid(facts))
            && self.unread.as_ref().is_none_or(|value| {
                value
                    .writes
                    .iter()
                    .all(|&write| facts.trusted_temp_home_slot(write) == Some(value.home))
            })
    }
}

#[derive(Debug, Clone, Default)]
pub(in crate::hir) struct Facts {
    pub frames: Vec<Frame>,
    pub by_result: BTreeMap<TempId, usize>,
    pub by_predicate: BTreeMap<InstrRef, Option<usize>>,
    pub routes: BTreeMap<InstrRef, (InstrRef, InstrRef)>,
    pub truthy_inputs: BTreeMap<InstrRef, (TempId, HomeSlotKey)>,
}

#[allow(
    clippy::too_many_arguments,
    reason = "原指令、SSA、冻结 owner、epoch 与 canonical 投影共同确定分支结果身份"
)]
pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    epochs: &SlotEpochFacts,
    fixed: &[TempId],
    phis: &[TempId],
) -> Facts {
    let mut groups = BTreeMap::<RegionId, Vec<&crate::structure::PhiPlan>>::new();
    let mut incomplete = BTreeSet::new();
    let mut edge_copies = BTreeMap::new();
    for phi in plan.phis() {
        if !phi.incomings.is_empty()
            && phi
                .incomings
                .iter()
                .all(|input| input.disposition == PhiIncomingDisposition::EdgeCopy)
        {
            edge_copies
                .entry(phi.block)
                .or_insert_with(Vec::new)
                .push(phi);
        }
        let owners = phi
            .incomings
            .iter()
            .filter_map(|incoming| match incoming.disposition {
                PhiIncomingDisposition::RegionResult(owner) => Some(owner),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        if let Some(&owner) = owners.first()
            && owners.len() == 1
            && phi
                .incomings
                .iter()
                .all(|incoming| incoming.disposition == PhiIncomingDisposition::RegionResult(owner))
        {
            if matches!(
                plan.region(owner),
                Some(RegionPlan::Branch { .. } | RegionPlan::ValueDecision { .. })
            ) {
                groups.entry(owner).or_default().push(phi);
            }
        } else {
            // 候选拒绝[ProofIncomplete:Ownership]：有一项结果跨 owner 时不能只发布其它看似完整的结果。
            incomplete.extend(owners);
        }
    }
    let mut facts = Facts::default();
    let mut unread = BTreeMap::new();
    for (owner, _) in plan.regions() {
        if groups.contains_key(&owner) || incomplete.contains(&owner) {
            continue;
        }
        let Some(initializer) = plan.branch_initializer(owner, cfg, dataflow) else {
            continue;
        };
        if dataflow.reg_is_captured(initializer.reg)
            || initializer.defs.iter().any(|def| {
                !dataflow.def_uses[def.index()].is_empty()
                    || !dataflow.def_phi_uses[def.index()].is_empty()
                    || fixed[def.index()] != TempId(def.index())
            })
        {
            // 候选拒绝[ProofIncomplete:UnreadBranch]：有读取、捕获或已合并的定义
            // 不能作为独立无读写入发布；已有合流继续由 RegionResult 协议持有。
            continue;
        }
        groups.insert(owner, Vec::new());
        unread.insert(owner, initializer);
    }
    let predicates = plan
        .conditions()
        .flat_map(|(_, condition)| condition.nodes.iter().map(|node| node.predicate))
        .chain(
            plan.value_decisions()
                .flat_map(|(_, decision)| decision.nodes.iter().map(|node| node.predicate)),
        );
    for predicate in predicates {
        if let LowInstr::Branch(branch) = &proto.instrs[predicate.index()] {
            let routes = if branch.cond.negated {
                (branch.else_target, branch.then_target)
            } else {
                (branch.then_target, branch.else_target)
            };
            facts.routes.insert(predicate, routes);
            if let crate::transformer::BranchSubject::Truthy(crate::transformer::CondOperand::Reg(
                reg,
            )) = branch.cond.subject
                && let Some(value) = canonical_value_temp(
                    dataflow.use_value(predicate, reg),
                    fixed.len(),
                    fixed,
                    phis,
                )
            {
                facts.truthy_inputs.insert(
                    predicate,
                    (
                        value,
                        HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, predicate)),
                    ),
                );
            }
        }
    }
    let result_value = |phi: &crate::structure::PhiPlan,
                        continuation,
                        end|
     -> Option<ResultValue> {
        if phi.block != continuation || phi.incomings.len() > 128 {
            return None;
        }
        let home = HomeSlotKey::new(phi.reg.index(), epochs.epoch_at(phi.reg, end));
        let value = canonical_value_temp(SsaValue::Phi(phi.phi), fixed.len(), fixed, phis)?;
        let mut incoming = Vec::new();
        for input in &phi.incomings {
            let source = match input.value {
                SsaValue::Def(def) => Some(dataflow.def_instr(def)),
                SsaValue::Phi(_) => None,
                _ => return None,
            };
            if source.is_some_and(|source| {
                source >= end || epochs.epoch_at(phi.reg, source) != home.epoch
            }) {
                return None;
            }
            let literal = source
                .and_then(|source| {
                    copy_assignments::scalar_literal(proto, &proto.instrs[source.index()])
                })
                .filter(|(reg, _)| *reg == phi.reg)
                .and_then(|(_, value)| value_programs::Literal::from_expr(&value));
            let copy = source.and_then(|source| {
                let LowInstr::Move(copy) = proto.instrs[source.index()] else {
                    return None;
                };
                if copy.dst != phi.reg {
                    return None;
                }
                let input = dataflow.use_value(source, copy.src);
                let binding = match input {
                    SsaValue::Entry(reg)
                        if reg.index() < usize::from(proto.signature.num_params) =>
                    {
                        HirBinding::Param(ParamId(reg.index()))
                    }
                    value => {
                        HirBinding::Temp(canonical_value_temp(value, fixed.len(), fixed, phis)?)
                    }
                };
                Some((
                    binding,
                    HomeSlotKey::new(copy.src.index(), epochs.epoch_at(copy.src, source)),
                ))
            });
            let terminal_write = match input.value {
                SsaValue::Def(def) => {
                    let range = cfg.blocks[dataflow.def_block(def).index()].instrs;
                    source == Some(range.start)
                        && match range.len {
                            1 => range.end() == end.index(),
                            2 => {
                                matches!(proto.instrs[range.start.index() + 1], LowInstr::Jump(jump) if jump.target == end)
                            }
                            _ => false,
                        }
                }
                _ => false,
            };
            incoming.push(Incoming {
                value: canonical_value_temp(input.value, fixed.len(), fixed, phis)?,
                source,
                literal,
                copy,
                terminal_write,
            });
        }
        Some(ResultValue {
            value,
            home,
            incoming,
        })
    };
    for (owner, values) in groups {
        if incomplete.contains(&owner) {
            continue;
        }
        let candidate = (|| {
            let (header, continuation, predicates) = match plan.region(owner)? {
                RegionPlan::Branch { plan: branch, .. } => {
                    let branch = plan.branch(*branch)?;
                    let condition = plan.condition(branch.condition)?;
                    if condition.nodes.len() > 8 {
                        return None;
                    }
                    (
                        branch.header,
                        branch.continuation?,
                        condition
                            .nodes
                            .iter()
                            .map(|node| node.predicate)
                            .collect::<Vec<_>>(),
                    )
                }
                RegionPlan::ValueDecision { plan: decision, .. } => {
                    let decision = plan.value_decision(*decision)?;
                    // 内部吸收的 phi 有自己的消费协议；这里只发布单结果决策的原叶写。
                    if decision.nodes.len() > 8
                        || !decision.absorbed_phis.is_empty()
                        || !decision.operands.is_empty()
                        || values.len() != 1
                        || values[0].phi != decision.result_phi
                    {
                        return None;
                    }
                    (
                        decision.header()?,
                        decision.merge,
                        decision
                            .nodes
                            .iter()
                            .map(|node| node.predicate)
                            .collect::<Vec<_>>(),
                    )
                }
                _ => return None,
            };
            let begin = cfg.blocks[header.index()].instrs.start;
            let end = cfg.blocks[continuation.index()].instrs.start;
            // 候选拒绝[ResourceLimit]：完整组的查询成本有界；不为每个结果重复扫描任意宽分支。
            if values.len() > 8 || end.index().checked_sub(begin.index())? > 128 || end <= begin {
                return None;
            }
            let mut inputs = Vec::new();
            for &predicate in &predicates {
                if predicate < begin || predicate >= end {
                    return None;
                }
                for (reg, value) in dataflow.use_values_at(predicate).iter() {
                    inputs.push((
                        canonical_value_temp(value, fixed.len(), fixed, phis)?,
                        HomeSlotKey::new(reg.index(), epochs.epoch_at(reg, predicate)),
                    ));
                }
            }
            let mut results = Vec::new();
            for phi in values {
                results.push(result_value(phi, continuation, end)?);
            }
            let edge_results = if matches!(plan.region(owner), Some(RegionPlan::Branch { .. })) {
                edge_copies
                    .get(&continuation)
                    .filter(|phis| phis.len() <= 8)
                    .into_iter()
                    .flatten()
                    .filter(|phi| {
                        phi.incomings.len() <= 128
                            && phi.incomings.iter().all(|input| {
                                input
                                    .edge
                                    .and_then(|edge| plan.edge_region_relation(edge))
                                    .is_some_and(|relation| {
                                        relation.source_owner.is_some_and(|source| {
                                            plan.region_contains(owner, source)
                                        })
                                    })
                            })
                    })
                    .filter_map(|phi| result_value(phi, continuation, end))
                    .collect()
            } else {
                Vec::new()
            };
            let unread = if let Some(initializer) = unread.get(&owner) {
                let home = HomeSlotKey::new(
                    initializer.reg.index(),
                    epochs.epoch_at(initializer.reg, end),
                );
                let sources = initializer.defs.map(|def| dataflow.def_instr(def));
                if sources.iter().any(|&source| {
                    source < begin
                        || source >= end
                        || epochs.epoch_at(initializer.reg, source) != home.epoch
                }) {
                    // 候选拒绝[ProofIncomplete:RootLifetime]：原两臂写与合流位置须共享
                    // 同一个物理 home；Close 后的同槽不能接续原写入身份。
                    return None;
                }
                Some(UnreadValue {
                    home,
                    writes: initializer.defs.map(|def| TempId(def.index())),
                    sources,
                    literals: sources.map(|source| {
                        copy_assignments::scalar_literal(proto, &proto.instrs[source.index()])
                            .filter(|(reg, _)| *reg == initializer.reg)
                            .and_then(|(_, value)| value_programs::Literal::from_expr(&value))
                    }),
                })
            } else {
                None
            };
            Some(Frame {
                begin,
                end,
                end_pc: proto
                    .lowering_map
                    .pc_map()
                    .get(end.index())
                    .and_then(|pcs| pcs.first().copied()),
                predicates,
                results,
                edge_results,
                unread,
                inputs,
            })
        })();
        if let Some(frame) = candidate {
            for predicate in &frame.predicates {
                facts
                    .by_predicate
                    .entry(*predicate)
                    .and_modify(|index| *index = None)
                    .or_insert(Some(facts.frames.len()));
            }
            for result in &frame.results {
                facts.by_result.insert(result.value, facts.frames.len());
            }
            facts.frames.push(frame);
        }
    }
    facts
}
