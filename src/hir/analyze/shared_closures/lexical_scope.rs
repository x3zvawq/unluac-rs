//! 计算 shared-closure 组的词法 scope envelope；依赖 StructurePlan containment，不负责 dominance；例如要求 owner scope 同时包含最左和最右 capture site。

use super::*;

#[derive(Clone, Copy)]
pub(super) struct GroupLexicalScopeEnvelope {
    pub(super) first: RegionId,
    pub(super) last: RegionId,
}

/// containment tree 的每棵子树在 DFS postorder 中都是连续区间；因此 owner 同时包含
/// 一组 scope 的最左、最右端点，当且仅当它包含整组 scope。
pub(super) fn group_lexical_scope_envelope(
    group: &ReusableGroup,
    cfg: &Cfg,
    scopes: &mut LexicalScopeIndex<'_>,
) -> Option<GroupLexicalScopeEnvelope> {
    let mut sites = group.instrs.iter();
    let first = scopes.instr_scope(*sites.next()?, cfg)?;
    let mut min = (scopes.rank(first)?, first);
    let mut max = min;
    for site in sites {
        let site_scope = scopes.instr_scope(*site, cfg)?;
        let ranked = (scopes.rank(site_scope)?, site_scope);
        if ranked.0 < min.0 {
            min = ranked;
        }
        if ranked.0 > max.0 {
            max = ranked;
        }
    }
    Some(GroupLexicalScopeEnvelope {
        first: min.1,
        last: max.1,
    })
}

#[derive(Clone, Copy)]
pub(super) enum LexicalScopeState {
    Unknown,
    Resolved(Option<RegionId>),
}

pub(super) enum LexicalScopeStep {
    Parent(RegionId),
    Resolved(Option<RegionId>),
}

pub(super) struct LexicalScopeIndex<'a> {
    structure: &'a StructurePlan,
    states: Vec<LexicalScopeState>,
    ranks: Vec<usize>,
}

impl<'a> LexicalScopeIndex<'a> {
    pub(super) fn new(structure: &'a StructurePlan) -> Self {
        let mut ranks = vec![usize::MAX; structure.regions().len()];
        for (rank, region) in structure.region_postorder().iter().copied().enumerate() {
            ranks[region.index()] = rank;
        }
        Self {
            structure,
            states: vec![LexicalScopeState::Unknown; ranks.len()],
            ranks,
        }
    }

    pub(super) fn rank(&self, region: RegionId) -> Option<usize> {
        self.ranks
            .get(region.index())
            .copied()
            .filter(|rank| *rank != usize::MAX)
    }

    pub(super) fn instr_scope(&mut self, instr: InstrRef, cfg: &Cfg) -> Option<RegionId> {
        let block = *cfg.instr_to_block.get(instr.index())?;
        self.region_scope(self.structure.region_for_block(block)?)
    }

    pub(super) fn region_scope(&mut self, start: RegionId) -> Option<RegionId> {
        let mut pending = Vec::new();
        let mut region = start;
        let resolved = loop {
            match *self.states.get(region.index())? {
                LexicalScopeState::Resolved(scope) => break scope,
                LexicalScopeState::Unknown => pending.push(region),
            }
            match lexical_scope_step(self.structure, region) {
                LexicalScopeStep::Parent(parent) => region = parent,
                LexicalScopeStep::Resolved(scope) => break scope,
            }
        };
        for region in pending {
            self.states[region.index()] = LexicalScopeState::Resolved(resolved);
        }
        resolved
    }
}

/// 返回 region 最终发射到的 Lua block；无法证明 VM-for control/preheader 落点时拒绝。
///
/// CFG dominance 不等于词法可见性：例如 repeat body 可以支配循环后的 block，但 body
/// 内声明的 local 在循环外不可见。Sequence 与 island 会被展平；branch arm、loop body、
/// normal tail 和 single-pass wrapper 则各自产生新的 Lua block；while/repeat control
/// prefix 最终发射在 loop body 内，因此共享 body 的 scope identity。
pub(super) fn lexical_scope_step(structure: &StructurePlan, region: RegionId) -> LexicalScopeStep {
    if region == structure.root() || structure.single_pass_for_region(region).is_some() {
        return LexicalScopeStep::Resolved(Some(region));
    }
    let Some(parent) = structure.region(region).and_then(RegionPlan::parent) else {
        return LexicalScopeStep::Resolved(None);
    };
    match structure.region(parent) {
        Some(RegionPlan::Branch {
            then_arm, else_arm, ..
        }) if *then_arm == region || *else_arm == Some(region) => {
            LexicalScopeStep::Resolved(Some(region))
        }
        Some(RegionPlan::Loop {
            plan,
            preheader,
            control,
            body,
            normal_tail,
            ..
        }) => {
            if *body == region || *normal_tail == Some(region) {
                LexicalScopeStep::Resolved(Some(region))
            } else if *control == region {
                LexicalScopeStep::Resolved(
                    matches!(
                        structure.loop_protocol(*plan),
                        Some(
                            crate::structure::LoopVmProtocol::While(_)
                                | crate::structure::LoopVmProtocol::Repeat(_)
                                | crate::structure::LoopVmProtocol::WhileTrue
                        )
                    )
                    .then_some(*body),
                )
            } else if *preheader == Some(region) {
                LexicalScopeStep::Resolved(None)
            } else {
                LexicalScopeStep::Parent(parent)
            }
        }
        Some(_) => LexicalScopeStep::Parent(parent),
        None => LexicalScopeStep::Resolved(None),
    }
}

pub(super) fn instr_is_reachable(cfg: &Cfg, instr: InstrRef) -> bool {
    cfg.instr_to_block
        .get(instr.index())
        .is_some_and(|block| cfg.reachable_blocks.contains(block))
}

pub(super) fn closure_at(
    proto: &LoweredProto,
    instr: InstrRef,
) -> Option<&crate::transformer::ClosureInstr> {
    match proto.instrs.get(instr.index())? {
        LowInstr::Closure(closure) => Some(closure),
        _ => None,
    }
}
