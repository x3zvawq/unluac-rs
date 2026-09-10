//! 在原 source scope 结束处交接独立副本根，分开源码身份与额外保活身份。
//!
//! scope 与定义来自 Structure/Bindings，窗口控制闭合来自 GraphFacts，精确退休来自
//! Promotion。不能把命名 copy 的 nil 声明提到函数入口；也不能在声明处复制隐藏根，
//! 否则 scope 内 debug.setlocal(copy,nil) 后仍会多保活旧值。这里在已证明的 scope 末端
//! 才读取当前 copy：`do local copy=owner; inspect(); holder=copy end`，后层无需重建边界。
//! 原 debug 末端可能含 goto 或不可达尾部；可发射末端消费共享 emission 投影，
//! 再在实际窗口上校验闭合、覆盖与 cleanup，不让原始 PC 代替运行生命周期。

use super::*;
use crate::hir::HirLowerError;
use crate::hir::emission::HirEmissionFacts;
use crate::hir::promotion::ProtoPromotionFacts;

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
