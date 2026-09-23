//! 恢复共享工厂内部的全局发布，使嵌套 owner 与被发布的闭包保持同一词法归属。
//! 仅完整匹配原工厂和全部展开实例后，才同时消费独立恢复器的 owner 与 replacement。

use super::*;
use crate::transformer::{AccessBase, AccessKey, SetTableKind, ValueOperand};

impl SharedClosurePlan {
    pub(in crate::hir::analyze) fn restore_publications(
        &mut self,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) {
        let mut occurrences = vec![Vec::new(); self.composites.len()];
        for (&site, &factory) in &self.replacements {
            occurrences[factory.0].push(site);
        }
        for (index, sites) in occurrences.iter().enumerate() {
            let Some(field) = publication_body(proto, &self.composites[index]) else {
                continue;
            };
            let Some(first) = sites
                .first()
                .and_then(|site| site.index().checked_sub(3))
                .map(InstrRef)
            else {
                continue;
            };
            let Some(inner) = self.owner_at(first) else {
                continue;
            };
            let inner_plan = &self.composites[inner.0];
            let outer = &self.composites[index];
            if inner.0 == index
                || inner_plan.nodes.len() != 1
                || inner_plan.root.index() != 0
                || inner_plan.lexical_owner_proto != outer.nodes[0].proto
                || inner_plan.outer_captures != outer.outer_captures
                || occurrences[inner.0].len() != sites.len()
                || !sites.iter().all(|site| {
                    publication_occurrence(proto, cfg, dataflow, self, outer, inner, *site, &field)
                })
            {
                continue;
            }
            // 内层 owner 的值仍由 outer 的依赖节点创建；只删除重复的独立工厂恢复。
            self.owners.remove(&first);
            for &site in sites {
                let leaf = InstrRef(site.index() - 2);
                self.replacements.remove(&leaf);
                self.consumed.insert(leaf);
                self.effect_prefixes.insert(InstrRef(site.index() - 1));
            }
            self.composites[index].effect = Some(SharedFactoryEffect {
                kind: SharedFactoryEffectKind::Publish,
                field,
                calls: sites.iter().map(|&site| (site, Vec::new())).collect(),
            });
        }
    }
}

fn global_field(
    proto: &LoweredProto,
    set: &crate::transformer::SetTableInstr,
) -> Option<crate::LuaString> {
    let AccessKey::Const(key) = set.key else {
        return None;
    };
    let crate::parser::RawLiteralConst::String(name) = proto.constants.get(key.index())? else {
        return None;
    };
    (set.base == AccessBase::Env && set.kind == SetTableKind::Normal)
        .then(|| super::super::helpers::raw_lua_string(name))
}

fn publication_body(proto: &LoweredProto, plan: &CompositeFactoryPlan) -> Option<crate::LuaString> {
    if plan.preserve_owner_value
        || plan.effect.is_some()
        || plan.nodes.len() != 2
        || plan.root.index() != 1
        || plan.outer_captures.len() != 1
        || plan.nodes[0].captures != [CompositeCapture::Outer(0)]
        || plan.nodes[1].captures != [CompositeCapture::Dependency(CompositeNodeRef(0))]
    {
        return None;
    }
    let owner = proto.children.get(plan.lexical_owner_proto.index())?;
    let [
        LowInstr::Closure(inner),
        LowInstr::Closure(leaf),
        LowInstr::SetTable(set),
        LowInstr::Closure(result),
        LowInstr::Return(ret),
    ] = owner.instrs.as_slice()
    else {
        return None;
    };
    if owner.signature.num_params != 0
        || owner.signature.is_vararg
        || owner.upvalue_count != 1
        || inner.dst != Reg(0)
        || leaf.dst != Reg(1)
        || result.dst != Reg(1)
        || inner.captures.as_slice()
            != [crate::transformer::Capture {
                source: CaptureSource::Upvalue(UpvalueRef(0)),
            }]
        || leaf.captures != inner.captures
        || result.captures.as_slice()
            != [crate::transformer::Capture {
                source: CaptureSource::ByValue(Reg(0)),
            }]
        || set.value != ValueOperand::Reg(Reg(1))
        || !matches!(ret.values, ValuePack::Fixed(range) if range.start == Reg(1) && range.len == 1)
        || owner.children.get(inner.proto.index())?.origin
            != proto.children.get(plan.nodes[0].proto.index())?.origin
        || owner.children.get(result.proto.index())?.origin
            != proto.children.get(plan.nodes[1].proto.index())?.origin
    {
        return None;
    }
    let inner_body = owner.children.get(inner.proto.index())?;
    let [LowInstr::Closure(created), LowInstr::Return(returned)] = inner_body.instrs.as_slice()
    else {
        return None;
    };
    let published = owner.children.get(leaf.proto.index())?;
    if inner_body.signature.num_params != 0
        || inner_body.signature.is_vararg
        || inner_body.upvalue_count != 1
        || inner_body.children.len() != 1
        || created.captures != inner.captures
        || !matches!(created.creation, ClosureCreation::Reusable(_))
        || !matches!(returned.values, ValuePack::Fixed(range) if range.start == created.dst && range.len == 1)
        || inner_body.children.get(created.proto.index())?.origin != published.origin
        || !value_leaf(published)
        || !value_leaf(owner.children.get(result.proto.index())?)
    {
        return None;
    }
    global_field(owner, set)
}

pub(super) fn value_leaf(proto: &LoweredProto) -> bool {
    proto.signature.num_params == 0
        && !proto.signature.is_vararg
        && proto.upvalue_count == 1
        && proto.children.is_empty()
        && matches!(proto.instrs.as_slice(), [LowInstr::GetUpvalue(get), LowInstr::Return(ret)]
            if matches!(ret.values, ValuePack::Fixed(range) if range.start == get.dst && range.len == 1))
}

#[expect(
    clippy::too_many_arguments,
    reason = "同时核对两份已有 factory plan 与原展开实例"
)]
fn publication_occurrence(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &SharedClosurePlan,
    outer: &CompositeFactoryPlan,
    inner_factory: CompositeFactoryRef,
    site: InstrRef,
    field: &crate::LuaString,
) -> bool {
    let Some(start) = site.index().checked_sub(3) else {
        return false;
    };
    let [
        LowInstr::Closure(inner),
        LowInstr::Closure(leaf),
        LowInstr::SetTable(set),
        LowInstr::Closure(result),
    ] = &proto.instrs[start..=site.index()]
    else {
        return false;
    };
    if cfg.instr_to_block[start] != cfg.instr_to_block[site.index()]
        || !plan.is_consumed(InstrRef(start))
        || plan.replacement_at(InstrRef(start + 1)) != Some(inner_factory)
        || inner.dst.index() != result.dst.index() + 1
        || leaf.dst.index() != result.dst.index() + 2
        || inner.proto != outer.nodes[0].proto
        || leaf.proto != plan.composites[inner_factory.0].nodes[0].proto
        || result.proto != outer.nodes[1].proto
        || leaf.captures != inner.captures
        || set.value != ValueOperand::Reg(leaf.dst)
        || global_field(proto, set).as_ref() != Some(field)
        || plan.effect_prefix_at(InstrRef(start + 2))
    {
        return false;
    }
    [
        (InstrRef(start), inner.dst, site),
        (InstrRef(start + 1), leaf.dst, InstrRef(start + 2)),
    ]
    .into_iter()
    .all(|(producer, reg, consumer)| {
        dataflow
            .instr_def_for_reg(producer, reg)
            .is_some_and(|def| {
                dataflow.def_phi_uses[def.index()].is_empty()
                    && dataflow.def_uses[def.index()].len() == 1
                    && dataflow.def_uses[def.index()][0].instr == consumer
            })
    })
}
