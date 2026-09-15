//! 在原 source scope 结束处交接独立副本根，分开源码身份与额外保活身份。
//!
//! scope 与定义来自 Structure/Bindings，窗口控制闭合来自 GraphFacts，精确退休来自
//! Promotion。不能把命名 copy 的 nil 声明提到函数入口；也不能在声明处复制隐藏根，
//! 否则 scope 内 debug.setlocal(copy,nil) 后仍会多保活旧值。这里在已证明的 scope 末端
//! 才读取当前 copy：`do local copy=owner; inspect(); holder=copy end`，后层无需重建边界。
//! 原 debug 末端可能含 goto 或不可达尾部；可发射末端消费共享 emission 投影，
//! 再在实际窗口上校验闭合、覆盖与 cleanup，不让原始 PC 代替运行生命周期。
//! 无 debug 的原 nil 初始化也可拥有独立副本：只认同块的直接覆盖 Def、唯一原 nil
//! 退休点与块内读取，不把回边进入后尚未初始化的额外 holder 提前到函数入口。
//! COPY 只向已有低槽交接后，NEWTABLE 在原槽覆盖它时，独立结束 COPY 声明；
//! `do local snapshot=alias; target=snapshot end; source={}` 允许分配继续使用原 freereg，
//! 不能把 snapshot 与新表接成活动 local 后让分配额外使用更高 scratch。

use super::*;
use crate::hir::HirLowerError;
use crate::hir::emission::HirEmissionFacts;
use crate::hir::promotion::ProtoPromotionFacts;

/// 原 COPY 窗口只含低槽纯写；退出词法窗口不清根，原 NEWTABLE 仍负责实际覆盖。
pub(in crate::hir::analyze) fn bind_allocation_copy_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) {
    let roots = facts.entry_parameter_copy_roots().collect::<BTreeSet<_>>();
    let mut candidates = Vec::new();
    for (block_index, block) in cfg.blocks.iter().enumerate() {
        let block_id = BlockRef(block_index);
        let Some(prefix) = emission.regular_prefix(block_id) else {
            continue;
        };
        if emission.prefix_is_hoisted(block_id) {
            continue;
        }
        let mut segment_start = block.instrs.start.index();
        for index in block.instrs.start.index()..block.instrs.end() {
            if !matches!(proto.instrs[index], LowInstr::NewTable(_)) {
                continue;
            }
            let prior_start = segment_start;
            segment_start = index + 1;
            let [next] = dataflow.instr_defs[index].as_slice() else {
                continue;
            };
            let Some(SsaValue::Def(old)) = dataflow.def_overwritten_value(*next) else {
                continue;
            };
            let def = &dataflow.defs[old.index()];
            let temp = TempId(old.index());
            let start = def.instr.index();
            let Some(home) = facts.trusted_temp_home_slot(temp) else {
                continue;
            };
            let LowInstr::Move(copy) = proto.instrs[start] else {
                continue;
            };
            let anchored_source = match dataflow.use_value(def.instr, copy.src) {
                SsaValue::Def(input) => roots.contains(&TempId(input.index())),
                SsaValue::Entry(parameter) => {
                    parameter.index() < usize::from(proto.signature.num_params)
                }
                _ => false,
            };
            if !anchored_source
                || def.block != block_id
                || start < prior_start
                || start >= index
                || !prefix.contains(&start)
                || !prefix.contains(&index)
                || home.slot() != def.reg.index()
                || bindings.fixed_temps[old.index()] != temp
                || bindings.bound_temp_targets.contains_key(&temp)
                || bindings.captured_temp_targets.contains_key(&temp)
                || bindings.temp_decl_locals.contains_key(&temp)
                || bindings.temp_debug_scopes[temp.index()].is_some()
                || dataflow.reg_is_reference_captured(def.reg)
                || !dataflow.def_phi_uses[old.index()].is_empty()
                || dataflow.def_uses[old.index()]
                    .iter()
                    .any(|use_| use_.instr.index() <= start || use_.instr.index() >= index)
                || copy.src >= copy.dst
                || !(start + 1..index).all(|at| {
                    // 低槽已有 binding 可接收 COPY；死常量也留在原窗口。这里不把
                    // 外部使用的匿名 Def 变成子块 local，不吞下新的高槽声明或观察事件。
                    matches!(
                        proto.instrs[at],
                        LowInstr::Move(_)
                            | LowInstr::LoadNil(_)
                            | LowInstr::LoadBool(_)
                            | LowInstr::LoadConst(_)
                            | LowInstr::LoadInteger(_)
                            | LowInstr::LoadNumber(_)
                    ) && dataflow.instr_defs[at].iter().all(|&written| {
                        let written_temp = bindings.fixed_temps[written.index()];
                        dataflow.def_reg(written) < def.reg
                            && (bindings.bound_temp_targets.contains_key(&written_temp)
                                || (!matches!(proto.instrs[at], LowInstr::Move(_))
                                    && dataflow.def_uses[written.index()].is_empty()
                                    && dataflow.def_phi_uses[written.index()].is_empty()
                                    && !dataflow
                                        .reg_is_reference_captured(dataflow.def_reg(written))))
                            && !bindings.temp_decl_locals.contains_key(&written_temp)
                            && bindings.temp_debug_scopes[written_temp.index()].is_none()
                    })
                })
            {
                continue;
            }
            candidates.push((start..index, temp, home));
        }
    }
    if candidates.is_empty() {
        return;
    }
    let retained = lexical_windows::retain_non_crossing(
        bindings
            .lexical_scopes
            .iter()
            .cloned()
            .chain(candidates.iter().map(|(window, _, _)| window.clone()))
            .collect(),
    )
    .into_iter()
    .map(|window| (window.start, window.end))
    .collect::<BTreeSet<_>>();
    let mut scoped = BTreeSet::new();
    for (window, temp, home) in candidates {
        if !retained.contains(&(window.start, window.end)) {
            continue;
        }
        if let Some(old) =
            bind_allocation_copy_target(proto, cfg, dataflow, bindings, facts, &roots, window.end)
        {
            scoped.insert(old);
        }
        let local = LocalId(bindings.local_count);
        bindings.local_count += 1;
        bindings.local_debug_hints.push(None);
        bindings.local_debug_scopes.push(None);
        bindings
            .bound_temp_targets
            .insert(temp, BoundSlotTarget::Local(local));
        bindings.temp_decl_locals.insert(temp, local);
        bindings.lexical_scopes.push(window);
        facts.record_local_home_slot(local, home);
        facts.record_temp_to_local_merge(temp, local);
        scoped.insert(temp);
    }
    facts.record_allocation_copy_scopes(scoped);
}

/// 分配后的原低槽 MOVE 与原参数快照属于同一 binding；在表达式内联前保留这个身份，
/// 避免未读的 SSA 目标在 AST 再变成一个占据 freereg 的新 local。
fn bind_allocation_copy_target(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
    roots: &BTreeSet<TempId>,
    allocation: usize,
) -> Option<TempId> {
    let [allocated] = dataflow.instr_defs[allocation].as_slice() else {
        return None;
    };
    let [use_] = dataflow.def_uses[allocated.index()].as_slice() else {
        return None;
    };
    let LowInstr::Move(copy) = *proto.instrs.get(allocation + 1)? else {
        return None;
    };
    let [target] = dataflow.instr_defs[allocation + 1].as_slice() else {
        return None;
    };
    let Some(SsaValue::Def(old)) = dataflow.def_overwritten_value(*target) else {
        return None;
    };
    let old_temp = TempId(old.index());
    let target_temp = TempId(target.index());
    let block = cfg.instr_to_block[allocation];
    let home = facts.trusted_temp_home_slot(old_temp)?;
    if use_.instr.index() != allocation + 1
        || copy.src != dataflow.def_reg(*allocated)
        || copy.dst >= copy.src
        || !roots.contains(&old_temp)
        || dataflow.defs[old.index()].block != block
        || cfg.instr_to_block[allocation + 1] != block
        || facts.trusted_temp_home_slot(target_temp) != Some(home)
        || [old, *target].iter().any(|&def| {
            let temp = TempId(def.index());
            bindings.fixed_temps[def.index()] != temp
                || bindings.bound_temp_targets.contains_key(&temp)
                || bindings.captured_temp_targets.contains_key(&temp)
                || bindings.temp_decl_locals.contains_key(&temp)
                || bindings.temp_debug_scopes[temp.index()].is_some()
                || dataflow.reg_is_reference_captured(dataflow.def_reg(def))
                || !dataflow.def_phi_uses[def.index()].is_empty()
                || dataflow.def_uses[def.index()]
                    .iter()
                    .any(|use_| cfg.instr_to_block[use_.instr.index()] != block)
        })
    {
        return None;
    }
    let local = LocalId(bindings.local_count);
    bindings.local_count += 1;
    bindings.local_debug_hints.push(None);
    bindings.local_debug_scopes.push(None);
    // 合并 temp 前先登记原 home，否则新 Local 尚无身份会被 merge 永久标为失效。
    facts.record_local_home_slot(local, home);
    for temp in [old_temp, target_temp] {
        bindings
            .bound_temp_targets
            .insert(temp, BoundSlotTarget::Local(local));
        facts.record_temp_to_local_merge(temp, local);
    }
    bindings.temp_decl_locals.insert(old_temp, local);
    Some(old_temp)
}

/// 原 nil 初始化与其后 COPY 共享同一实际槽，且全部读取留在该普通块时，直接复用
/// 原声明：`repeat local target; target=source until target` 不另造入口 holder。
pub(in crate::hir::analyze) fn bind_copy_root_initializers(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) -> Vec<LocalId> {
    let mut locals = Vec::new();
    let mut nil_sites = BTreeSet::new();
    for (root, site) in facts.single_copy_root_before_releases() {
        let def = &dataflow.defs[root.index()];
        let Some(SsaValue::Def(initial)) = dataflow.def_overwritten_value(def.id) else {
            continue;
        };
        let initial_def = &dataflow.defs[initial.index()];
        let initial_temp = bindings.fixed_temps[initial.index()];
        let Some(home) = facts.trusted_temp_home_slot(root) else {
            continue;
        };
        let Some(prefix) = emission.regular_prefix(def.block) else {
            continue;
        };
        if initial_def.instr != site
            || !matches!(proto.instrs[site.index()], LowInstr::LoadNil(_))
            || initial_temp != TempId(initial.index())
            || initial_def.block != def.block
            || site.index() >= def.instr.index()
            || !prefix.contains(&site.index())
            || !prefix.contains(&def.instr.index())
            || emission.prefix_is_hoisted(def.block)
            || facts.trusted_temp_home_slot(initial_temp) != Some(home)
            || !dataflow.def_phi_uses[initial.index()].is_empty()
            || dataflow.def_uses[initial.index()].iter().any(|use_| {
                use_.instr.index() < site.index() || use_.instr.index() >= def.instr.index()
            })
            || dataflow.def_uses[root.index()].iter().any(|use_| {
                // terminator 的读取仍属于本块（repeat 的 until 在声明作用域内）。
                cfg.instr_to_block[use_.instr.index()] != def.block
                    || use_.instr.index() < def.instr.index()
                    || use_.instr.index() > prefix.end
            })
            || [root, initial_temp].iter().any(|temp| {
                bindings.bound_temp_targets.contains_key(temp)
                    || bindings.captured_temp_targets.contains_key(temp)
                    || bindings.temp_decl_locals.contains_key(temp)
                    || bindings.temp_debug_scopes[temp.index()].is_some()
            })
        {
            continue;
        }
        let local = LocalId(bindings.local_count);
        bindings.local_count += 1;
        bindings.local_debug_hints.push(None);
        bindings.local_debug_scopes.push(None);
        bindings
            .bound_temp_targets
            .insert(root, BoundSlotTarget::Local(local));
        bindings
            .bound_temp_targets
            .insert(initial_temp, BoundSlotTarget::Local(local));
        bindings.temp_decl_locals.insert(initial_temp, local);
        facts.record_local_home_slot(local, home);
        facts.record_temp_to_local_merge(root, local);
        locals.push(local);
        nil_sites.insert(site);
    }
    // 同一 LOADNIL 的未读成员仍是原声明前缀；在原点共同发射，避免先拆成
    // LocalDecl 与 Temp 写、再由 Final 恢复成第二条声明。活出值与已有身份不参与。
    for site in nil_sites {
        for &def in &dataflow.instr_defs[site.index()] {
            let temp = TempId(def.index());
            let Some(home) = facts.trusted_temp_home_slot(temp) else {
                continue;
            };
            if bindings.fixed_temps[def.index()] != temp
                || bindings.bound_temp_targets.contains_key(&temp)
                || bindings.captured_temp_targets.contains_key(&temp)
                || bindings.temp_decl_locals.contains_key(&temp)
                || bindings.temp_debug_scopes[temp.index()].is_some()
                || dataflow.reg_is_reference_captured(dataflow.def_reg(def))
                || !dataflow.def_uses[def.index()].is_empty()
                || !dataflow.def_phi_uses[def.index()].is_empty()
            {
                continue;
            }
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
            bindings
                .bound_temp_targets
                .insert(temp, BoundSlotTarget::Local(local));
            bindings.temp_decl_locals.insert(temp, local);
            facts.record_local_home_slot(local, home);
        }
    }
    locals
}

/// 参数快照的各 epoch 已在首次同槽写回截断；共用同一 home 的 holder 不会重叠。
/// 例如展开 224 次 `owner,n=owner,0; lookup()`，只需一个额外 local，而不是 224 个。
/// holder 是独立保活身份，不参与后续 ordinary home compaction 的写入复用。
pub(in crate::hir::analyze) fn bind_copy_root_holders(
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) -> Vec<LocalId> {
    let mut holders = BTreeMap::new();
    for temp in facts.observing_copy_root_temps() {
        let home = facts
            .trusted_temp_home_slot(temp)
            .expect("canonical parameter snapshot retains its physical home");
        let local = *holders.entry(home).or_insert_with(|| {
            let local = LocalId(bindings.local_count);
            bindings.local_count += 1;
            bindings.local_debug_hints.push(None);
            bindings.local_debug_scopes.push(None);
            facts.record_home_free_local(local);
            local
        });
        bindings
            .bound_temp_targets
            .insert(temp, BoundSlotTarget::Local(local));
    }
    holders.into_values().collect()
}

#[expect(
    clippy::too_many_arguments,
    reason = "身份交接借用同一 lowering 的发射与生命周期事实"
)]
pub(in crate::hir::analyze) fn bind_copy_root_scopes(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    graph: &GraphFacts,
    structure: &ReadyStructureFacts,
    emission: &HirEmissionFacts<'_>,
    bindings: &mut ProtoBindings,
    facts: &mut ProtoPromotionFacts,
) -> Result<(), HirLowerError> {
    if facts.copy_root_temps().is_empty() {
        return Ok(());
    }
    let debug = structure.debug_bindings();
    let mut scopes = bindings.lexical_scopes.clone();
    let mut handoffs = Vec::new();
    let mut local_homes = Vec::new();
    for &temp in facts.copy_root_temps() {
        let Some(scope) = bindings
            .temp_debug_scopes
            .get(temp.index())
            .copied()
            .flatten()
        else {
            continue;
        };
        let def = &dataflow.defs[temp.index()];
        if !matches!(proto.instrs[def.instr.index()], LowInstr::Move(_)) {
            continue;
        }
        let fact = debug
            .for_scope(scope)
            .ok_or_else(|| HirLowerError::invalid("copy root source scope is not accepted"))?;
        // 已存在 binding 的后续写入没有新的源码声明边界；其身份由原入口绑定持有。
        if fact.value != SsaValue::Def(def.id) {
            continue;
        }
        let raw_end = fact
            .end_instr
            .ok_or_else(|| HirLowerError::invalid("copy root source scope has no low endpoint"))?
            .index();
        let end = emission
            .source_scope_prefix_end(cfg, raw_end)
            .ok_or_else(|| {
                HirLowerError::invalid("copy root source scope has no emitted prefix endpoint")
            })?;
        let start = def.instr.index();
        if start >= end {
            return Err(HirLowerError::invalid(
                "copy root has an empty source window",
            ));
        }
        let end_block = cfg.instr_to_block[end - 1];
        // 候选拒绝[ProofIncomplete]：跨窗口覆盖或未单独发射的端点还没有可提交的源码身份交接。
        // 内层 CLOSE 只关闭更高槽位时，外层源码身份仍活过其回调；在指令
        // 完成后读取当前 local 才能保留回调中的 debug.setlocal 写入。
        if matches!(proto.instrs[end - 1], LowInstr::Close(close) if def.reg >= close.from)
            || matches!(proto.instrs[end - 1], LowInstr::Tbc(_))
            || dataflow
                .first_must_write_in_range(def.reg, start + 1..end)
                .is_some()
            || !graph.closed_instruction_window(cfg, start..end)
            || !emission
                .regular_prefix(def.block)
                .is_some_and(|range| range.contains(&start))
            || !emission
                .regular_prefix(end_block)
                .is_some_and(|range| range.contains(&(end - 1)))
            || emission.scope_owner(def.block) != emission.scope_owner(end_block)
        {
            return Err(HirLowerError::invalid(
                "copy root cannot retain its source scope at an emitted endpoint",
            ));
        }
        let holder = TempId(bindings.temp_count);
        bindings.temp_count += 1;
        bindings.temp_debug_locals.push(None);
        bindings.temp_debug_scopes.push(None);
        let local = LocalId(bindings.local_count);
        bindings.local_count += 1;
        bindings
            .local_debug_hints
            .push(bindings.temp_debug_locals[temp.index()].clone());
        bindings.local_debug_scopes.push(Some(scope));
        bindings
            .bound_temp_targets
            .insert(temp, BoundSlotTarget::Local(local));
        bindings.temp_decl_locals.insert(temp, local);
        local_homes.push((
            local,
            facts
                .trusted_temp_home_slot(temp)
                .expect("canonical copy root retains its physical home"),
        ));
        scopes.push(start..end);
        handoffs.push((temp, holder, InstrRef(end - 1)));
    }
    let expected = scopes
        .iter()
        .map(|range| (range.start, range.end))
        .collect::<BTreeSet<_>>();
    let scopes = lexical_windows::retain_non_crossing(scopes);
    if scopes.len() != expected.len() {
        return Err(HirLowerError::invalid(
            "copy root source scope crosses another lexical owner",
        ));
    }
    bindings.lexical_scopes = scopes;
    for (local, home) in local_homes {
        facts.record_local_home_slot(local, home);
    }
    facts.install_copy_root_scopes(handoffs);
    Ok(())
}
