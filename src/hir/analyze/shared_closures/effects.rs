//! 匹配已恢复共享工厂的完整事件前缀，将原调用帧与闭包依赖链一起保留。
//! 这里只产生需要 O2 内联的候选；最终函数体与全部调用仍由 Generate 核对。

use super::*;
use crate::transformer::{
    AccessBase, AccessKey, CallKind, ConstRef, GetTableKind, RegRange, ResultPack,
};

impl SharedClosurePlan {
    pub(in crate::hir::analyze) fn restore_effect_prefixes(
        &mut self,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) {
        let mut occurrences = vec![Vec::new(); self.composites.len()];
        for (&site, &factory) in &self.replacements {
            occurrences[factory.0].push(site);
        }
        for (index, sites) in occurrences.into_iter().enumerate() {
            let composite = &self.composites[index];
            let Some(label) = event_body(proto, composite) else {
                continue;
            };
            let Some(calls) = sites
                .into_iter()
                .map(|site| {
                    event_occurrence(proto, cfg, dataflow, self, composite, site, &label)
                        .map(|arg| (site, vec![arg]))
                })
                .collect::<Option<BTreeMap<_, _>>>()
            else {
                continue;
            };
            // 原事件体和每个展开实例同时成立才消费前缀，不能只恢复部分调用。
            for &site in calls.keys() {
                self.effect_prefixes
                    .extend((site.index() - 5..site.index() - 1).map(InstrRef));
            }
            self.composites[index].effect = Some(SharedFactoryEffect {
                kind: SharedFactoryEffectKind::Print,
                field: label,
                calls,
            });
        }
    }

    pub(in crate::hir::analyze) fn effect_prefix_at(&self, site: InstrRef) -> bool {
        self.effect_prefixes.contains(&site)
    }
}

fn string(proto: &LoweredProto, key: ConstRef) -> Option<crate::LuaString> {
    let crate::parser::RawLiteralConst::String(value) = proto.constants.get(key.index())? else {
        return None;
    };
    Some(super::super::helpers::raw_lua_string(value))
}

fn event_body(proto: &LoweredProto, plan: &CompositeFactoryPlan) -> Option<crate::LuaString> {
    if plan.preserve_owner_value
        || plan.nodes.len() != 2
        || plan.root.index() != 1
        || plan
            .nodes
            .iter()
            .flat_map(|node| &node.captures)
            .any(|capture| matches!(capture, CompositeCapture::Integer(_)))
    {
        return None;
    }
    let owner = proto.children.get(plan.lexical_owner_proto.index())?;
    let [
        LowInstr::GetTable(get),
        LowInstr::LoadConst(label),
        LowInstr::Move(arg),
        LowInstr::Call(call),
        LowInstr::Closure(first),
        LowInstr::Closure(result),
        LowInstr::Return(ret),
    ] = owner.instrs.as_slice()
    else {
        return None;
    };
    let AccessKey::Const(key) = get.key else {
        return None;
    };
    if owner.signature.num_params != 1
        || owner.signature.is_vararg
        || get.base != AccessBase::Env
        || get.kind != GetTableKind::Import
        || string(owner, key)?.as_utf8() != Some("print")
        || get.dst != Reg(1)
        || label.dst != Reg(2)
        || arg.dst != Reg(3)
        || arg.src != Reg(0)
        || call.kind != CallKind::Normal
        || call.method_name.is_some()
        || call.callee != Reg(1)
        || call.args != ValuePack::Fixed(RegRange::new(Reg(2), 2))
        || call.results != ResultPack::Ignore
        || first.dst != Reg(1)
        || result.dst != Reg(2)
        || ret.values != ValuePack::Fixed(RegRange::new(Reg(2), 1))
    {
        return None;
    }
    for (closure, node) in [(first, &plan.nodes[0]), (result, &plan.nodes[1])] {
        if owner.children.get(closure.proto.index())?.origin
            != proto.children.get(node.proto.index())?.origin
        {
            return None;
        }
    }
    string(owner, label.value)
}

fn event_occurrence(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &SharedClosurePlan,
    composite: &CompositeFactoryPlan,
    site: InstrRef,
    expected_label: &crate::LuaString,
) -> Option<crate::LuaString> {
    let start = site.index().checked_sub(5)?;
    let [
        LowInstr::GetTable(get),
        LowInstr::LoadConst(label),
        LowInstr::LoadConst(arg),
        LowInstr::Call(call),
        LowInstr::Closure(first),
        LowInstr::Closure(result),
    ] = proto.instrs.get(start..=site.index())?
    else {
        return None;
    };
    let AccessKey::Const(key) = get.key else {
        return None;
    };
    let base = result.dst.index();
    if get.base != AccessBase::Env
        || get.kind != GetTableKind::Import
        || string(proto, key)?.as_utf8() != Some("print")
        || string(proto, label.value)? != *expected_label
        || get.dst.index() != base + 1
        || label.dst.index() != base + 2
        || arg.dst.index() != base + 3
        || call.kind != CallKind::Normal
        || call.method_name.is_some()
        || call.callee != get.dst
        || call.args != ValuePack::Fixed(RegRange::new(label.dst, 2))
        || call.results != ResultPack::Ignore
        || first.dst != get.dst
        || first.proto != composite.nodes[0].proto
        || result.proto != composite.nodes[1].proto
        || !plan.is_consumed(InstrRef(site.index() - 1))
        || cfg.instr_to_block[start] != cfg.instr_to_block[site.index()]
    {
        return None;
    }
    for offset in 0..4 {
        let instr = InstrRef(start + offset);
        if plan.owner_at(instr).is_some()
            || plan.replacement_at(instr).is_some()
            || plan.is_consumed(instr)
            || plan.effect_prefix_at(instr)
        {
            return None;
        }
        // 前缀值必须只流入这次调用；保留后续观察或 phi 的值不能移入工厂。
        for def in &dataflow.instr_defs[instr.index()] {
            if !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|use_| use_.instr != InstrRef(start + 3))
            {
                return None;
            }
        }
    }
    string(proto, arg.value)
}
