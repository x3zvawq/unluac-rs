//! 为原 nil 声明及后续标量写恢复同一绑定。
//!
//! 保留原写入位置，避免跨 goto 的独立 SSA 定义在 AST 变成额外声明；
//! 入口声明可承接同槽 Def/Phi 的后续读取；内层复用槽只接回未读写组。
//! debug、capture 及不同槽生命周期已有各自身份，不在这里合并。

use super::*;
use crate::hir::promotion::ProtoPromotionFacts;

pub(in crate::hir::analyze) fn bind_scalar_slots(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
    bind_reused_boolean_slots(proto, graph, dataflow, emission, bindings, facts);
    if graph.block_is_cyclic(cfg.entry_block) || emission.prefix_is_hoisted(cfg.entry_block) {
        return;
    }
    let Some(prefix) = emission.regular_prefix(cfg.entry_block) else {
        return;
    };
    let scope_start = bindings
        .lexical_scopes
        .iter()
        .filter(|scope| scope.end > prefix.start && scope.start < prefix.end)
        .map(|scope| scope.start)
        .min()
        .unwrap_or(prefix.end);
    let mut seeds = BTreeMap::new();
    let mut writes = BTreeMap::<Reg, BTreeSet<TempId>>::new();
    let mut blocked = BTreeSet::new();
    // 按原寄存器索引全部定义，不能漏掉无可信 home 或跨 CLOSE epoch 的后继写。
    for def in &dataflow.defs {
        let temp = TempId(def.id.index());
        if def.reg.index() < usize::from(proto.signature.num_params)
            || (proto.signature.has_vararg_param_reg
                && def.reg.index() == usize::from(proto.signature.num_params))
        {
            continue;
        }
        writes
            .entry(def.reg)
            .or_default()
            .extend([temp, bindings.fixed_temps[temp.index()]]);
        // 候选拒绝[SemanticBarrier:Binding]：已有身份或非标量覆盖时，
        // 同槽不代表同一变量；hoisted 发射也不能借原入口的词法支配关系。
        let scalar_write = matches!(
            proto.instrs[def.instr.index()],
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
        ) || matches!(proto.instrs[def.instr.index()], LowInstr::LoadConst(load)
            if matches!(proto.constants[load.value.index()],
                crate::parser::RawLiteralConst::Nil | crate::parser::RawLiteralConst::Boolean(_)
                    | crate::parser::RawLiteralConst::Integer(_) | crate::parser::RawLiteralConst::Number(_)))
            || matches!(proto.instrs[def.instr.index()], LowInstr::UnaryOp(unary)
            if unary.op == crate::transformer::UnaryOpKind::Not);
        let numeric_write = matches!(
            proto.instrs[def.instr.index()],
            LowInstr::LoadInteger(_) | LowInstr::LoadNumber(_)
        ) || matches!(proto.instrs[def.instr.index()], LowInstr::LoadConst(load)
            if matches!(proto.constants[load.value.index()],
                crate::parser::RawLiteralConst::Integer(_) | crate::parser::RawLiteralConst::Number(_)));
        // 数字仅补回没有消费者的原覆盖；参与值流的数字分支已有声明/表达式 owner，
        // 提前绑定会割裂它与其他目标的并行合流和返回帧。
        let consumed_number = numeric_write
            && (!dataflow.def_uses[temp.index()].is_empty()
                || !dataflow.def_phi_uses[temp.index()].is_empty());
        if !scalar_write
            || consumed_number
            || dataflow.reg_is_reference_captured(def.reg)
            || emission.prefix_is_hoisted(def.block)
        {
            blocked.insert(def.reg);
        }
        if def.block == cfg.entry_block
            && prefix.contains(&def.instr.index())
            && def.instr.index() < scope_start
            && matches!(proto.instrs[def.instr.index()], LowInstr::LoadNil(_))
            && dataflow.def_overwritten_value(def.id) == Some(SsaValue::Entry(def.reg))
        {
            seeds.insert(def.reg, temp);
        }
    }
    // Phi 仍是原寄存器的值身份；循环自反馈并不创建另一份声明。
    // 不从普通 Def 的使用情况猜合流绑定，直接消费 canonical Phi→Temp 映射。
    for phi in &dataflow.phi_candidates {
        if let Some(temps) = writes.get_mut(&phi.reg) {
            temps.insert(bindings.phi_temps[phi.id.index()]);
        }
    }
    for (reg, seed) in seeds {
        let temps = &writes[&reg];
        if blocked.contains(&reg) || temps.len() < 2 {
            continue;
        }
        // ProofIncomplete：被消费的入口 nil 也可能是 CALL/iterator/构造器的准备值，
        // 不能据此把整个 scratch 槽提升为声明。这里仅恢复在首次读取前已覆盖的入口声明；
        // 后继 Boolean Def/Phi 可以被读取，声明身份仍来自未读的原 nil。
        if !dataflow.def_uses[seed.index()].is_empty()
            || !dataflow.def_phi_uses[seed.index()].is_empty()
        {
            continue;
        }
        let Some(home) = facts.trusted_temp_home_slot(seed) else {
            continue;
        };
        let existing = bindings.temp_decl_locals.get(&seed).copied();
        if existing.is_some_and(|local| {
            facts.trusted_local_home_slot(local) != Some(home)
                || bindings.local_debug_hints[local.index()].is_some()
                || bindings.local_debug_scopes[local.index()].is_some()
        }) {
            continue;
        }
        // 候选拒绝[ProofIncomplete]：只合并全部写都由同一可信 home/epoch 解释的槽。
        if temps.iter().any(|&temp| {
            facts.trusted_temp_home_slot(temp) != Some(home)
                || bindings.bound_temp_targets.get(&temp).is_some_and(|target|
                    !matches!(target, BoundSlotTarget::Local(local) if Some(*local) == existing))
                || bindings.captured_temp_targets.contains_key(&temp)
                || (temp != seed && bindings.temp_decl_locals.contains_key(&temp))
                || bindings.temp_debug_scopes[temp.index()].is_some()
        }) {
            continue;
        }
        // 入口声明支配全部后续路径，且只存放不可持有对象根的值；合并的是写入身份，
        // 不是删除原检查或推导常量。原 LOADNIL 仍在原点清除未知入口 scratch。
        // nil 的 COPY-root owner 可能已发布原声明；只补同槽后续写，不再分配另一身份。
        let local = existing.unwrap_or_else(|| {
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
            local
        });
        facts.record_local_home_slot(local, home);
        for &temp in temps {
            bindings
                .bound_temp_targets
                .insert(temp, BoundSlotTarget::Local(local));
            facts.record_temp_to_local_merge(temp, local);
        }
        bindings.temp_decl_locals.insert(seed, local);
    }
}

/// 同槽此前或此后用于表达式 scratch 时，只接回 nil 开始的连续未读 Boolean 写组。
/// 各原写保持原位置；后继帧的声明末端仍由 source-frames 的完整前缀预览处理。
fn bind_reused_boolean_slots(
    proto: &LoweredProto,
    graph: &GraphFacts,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
    let scope_boundaries = bindings
        .lexical_scopes
        .iter()
        .flat_map(|scope| [scope.start, scope.end])
        .collect::<BTreeSet<_>>();
    let mut writes = BTreeMap::<Reg, Vec<_>>::new();
    for def in &dataflow.defs {
        writes.entry(def.reg).or_default().push(def);
    }
    for (reg, defs) in writes {
        if reg.index() < usize::from(proto.signature.num_params)
            || (proto.signature.has_vararg_param_reg
                && reg.index() == usize::from(proto.signature.num_params))
            || dataflow.reg_is_reference_captured(reg)
        {
            continue;
        }
        let eligible = |temp: TempId| {
            let def = &dataflow.defs[temp.index()];
            (matches!(
                proto.instrs[def.instr.index()],
                LowInstr::LoadNil(_) | LowInstr::LoadBool(_)
            ) || matches!(proto.instrs[def.instr.index()], LowInstr::UnaryOp(unary)
                    if unary.op == crate::transformer::UnaryOpKind::Not))
                && bindings.fixed_temps[temp.index()] == temp
                && !bindings.bound_temp_targets.contains_key(&temp)
                && !bindings.captured_temp_targets.contains_key(&temp)
                && !bindings.temp_decl_locals.contains_key(&temp)
                && bindings.temp_debug_scopes[temp.index()].is_none()
                && dataflow.def_uses[temp.index()].is_empty()
                && dataflow.def_phi_uses[temp.index()].is_empty()
                && !graph.block_is_cyclic(def.block)
                && !emission.prefix_is_hoisted(def.block)
        };
        let mut groups = Vec::new();
        let mut start = None;
        for (index, def) in defs.iter().enumerate() {
            if eligible(TempId(def.id.index())) {
                if start.is_none()
                    && matches!(proto.instrs[def.instr.index()], LowInstr::LoadNil(_))
                {
                    start = Some(index);
                }
            } else if let Some(first) = start.take()
                && index > first + 1
            {
                groups.push(first..index);
            }
        }
        for group in groups {
            let seed = defs[group.start];
            let temp = TempId(seed.id.index());
            let Some(home) = facts.trusted_temp_home_slot(temp) else {
                continue;
            };
            let last = defs[group.end - 1].instr.index();
            if emission
                .regular_prefix(seed.block)
                .is_none_or(|prefix| !prefix.contains(&seed.instr.index()))
                || scope_boundaries
                    .range(seed.instr.index() + 1..=last)
                    .next()
                    .is_some()
            {
                continue;
            }
            if defs[group.clone()].iter().any(|def| {
                !graph.dominates(seed.block, def.block)
                    || facts.trusted_temp_home_slot(TempId(def.id.index())) != Some(home)
                    || !emission.ordinary_block(def.block)
                    || !emission.scope_contains(seed.block, def.block)
            }) {
                // ProofIncomplete：跨入口或跨发射域的写组没有统一声明 owner。
                continue;
            }
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
            facts.record_local_home_slot(local, home);
            for def in &defs[group] {
                let temp = TempId(def.id.index());
                bindings
                    .bound_temp_targets
                    .insert(temp, BoundSlotTarget::Local(local));
                facts.record_temp_to_local_merge(temp, local);
            }
            bindings.temp_decl_locals.insert(temp, local);
        }
    }
}
