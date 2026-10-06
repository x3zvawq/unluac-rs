//! 证明原基本块内尚未暴露的新表访问性质。
//!
//! 消费 NewTable、原使用及 debug 身份，发布具体读取的无元方法证书和私有初始化归属。

use super::*;

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    effects: &[InstrEffect],
    summaries: &[SideEffectSummary],
    captures: &[RegCaptures],
) -> Vec<bool> {
    let mut reads = vec![false; proto.instrs.len()];
    for block in &cfg.block_order {
        let mut plain = BTreeSet::new();
        let range = cfg.blocks[block.index()].instrs;
        for index in range.start.index()..range.end() {
            let instr = &proto.instrs[index];
            let read_base = match instr {
                LowInstr::GetTable(access) if primitive_key(proto, access.key) => {
                    match access.base {
                        AccessBase::Reg(reg) if plain.contains(&reg) => Some(reg),
                        _ => None,
                    }
                }
                _ => None,
            };
            reads[index] = read_base.is_some();
            // 查询只描述读取节点；SETLIST 可能分配，不能借 raw store 消除它的观察。
            if read_base.is_none() && summaries[index].may_observe_gc_roots() {
                plain.retain(|reg| !source_visible(proto, *reg, index));
            }
            for reg in effects[index].fixed_uses() {
                let stays_private = read_base == Some(*reg)
                    || matches!(instr, LowInstr::SetList(set) if set.base == *reg);
                if !stays_private {
                    plain.remove(reg);
                }
            }
            if let Some(start) = effects[index].open_use {
                plain.retain(|reg| *reg < start);
            }
            plain.retain(|reg| !effects[index].must_define(*reg));
            if let LowInstr::NewTable(table) = instr
                && !captures[table.dst.index()].by_reference
                && !source_visible(proto, table.dst, index)
            {
                plain.insert(table.dst);
            }
        }
    }
    reads
}

fn primitive_key(proto: &LoweredProto, key: AccessKey) -> bool {
    use crate::parser::RawLiteralConst;
    match key {
        AccessKey::Integer(_) => true,
        AccessKey::Const(key) => matches!(
            proto.constants.get(key.index()),
            Some(
                RawLiteralConst::Nil
                    | RawLiteralConst::Boolean(_)
                    | RawLiteralConst::Integer(_)
                    | RawLiteralConst::Number(_)
                    | RawLiteralConst::String(_)
            )
        ),
        AccessKey::Reg(_) => false,
    }
}

fn source_visible(proto: &LoweredProto, reg: Reg, index: usize) -> bool {
    proto
        .debug_locals
        .source_visible_at(reg, &proto.lowering_map.pc_map()[index])
}

/// 每个分配只遍历自己的 SSA uses；字段准备不按候选回扫指令区间。
/// 唯一指令消费者前只能引用目标 base，不能已有别名或捕获。
/// phi 是边上的值转交，不是另一次求值；其闭合性由条件/值决策 owner 验证。
pub(super) fn initializations(
    proto: &LoweredProto,
    cfg: &Cfg,
    facts: &DataflowFacts,
) -> BTreeMap<DefId, Vec<InstrRef>> {
    let mut initializations = BTreeMap::new();
    for def in &facts.defs {
        let LowInstr::NewTable(table) = &proto.instrs[def.instr.index()] else {
            continue;
        };
        let indexed = matches!(
            table.allocation,
            crate::transformer::TableAllocation::Indexed { .. }
        );
        let template = matches!(
            table.allocation,
            crate::transformer::TableAllocation::Template(_)
        );
        if !indexed
            && !template
            && !matches!(
                table.allocation,
                crate::transformer::TableAllocation::PucBatched(_)
                    | crate::transformer::TableAllocation::Luau(_)
            )
        {
            // Luau 模板占位仍由 HIR 完整构造事务恢复，不能省略其字段身份证明。
            continue;
        }
        if facts.reference_capture_may_be_open(def.reg, def.instr) {
            continue;
        }
        // 不按 def_phi_uses 拒绝初始化：`flag and { f() } or fallback` 的表
        // 同时被 TEST 和结果 phi 使用，但只分配一次。决策的 CurrentValue/出口
        // 协议负责这次转交，shared_fixed_evaluation_defs 仍计算真实指令读取。
        // use index 已按原指令排序。最后一次读取由外部表达式消费，其前各次读取
        // 必须都是这个原 Def 的初始化 base；初始化后再写回的普通表不领取该事实。
        let uses = &facts.def_uses[def.id.index()];
        let Some((consumer, writes)) = uses.split_last() else {
            continue;
        };
        if writes.is_empty()
            || cfg.instr_to_block[consumer.instr.index()] != def.block
            || facts.instr_effects[consumer.instr.index()].repeats_fixed_use(consumer.reg)
            || source_visible(proto, def.reg, def.instr.index())
            || uses.iter().any(|site| {
                site.reg != def.reg
                    || cfg.instr_to_block[site.instr.index()] != def.block
                    || facts.reference_capture_may_be_open(site.reg, site.instr)
                    || source_visible(proto, site.reg, site.instr.index())
            })
        {
            continue;
        }
        let target = |site: &crate::structure::UseSite| match &proto.instrs[site.instr.index()] {
            LowInstr::SetTable(write) => write.base == AccessBase::Reg(site.reg),
            LowInstr::SetList(write) => write.base == site.reg,
            _ => false,
        };
        if target(consumer)
            || writes.iter().any(|site| {
                !target(site) || facts.instr_effects[site.instr.index()].repeats_fixed_use(site.reg)
            })
        {
            // 自引用 key/value、提前发布或中途读取都不是构造器内部的 base 转交。
            continue;
        }
        let mut arrays = 0usize;
        let mut records = 0usize;
        let mut open = false;
        let mut open_call = false;
        let mut valid = true;
        for site in writes {
            match &proto.instrs[site.instr.index()] {
                LowInstr::SetTable(write) if indexed => {
                    if records != 0 || open || write.key != AccessKey::Integer((arrays + 1) as i64)
                    {
                        valid = false;
                        break;
                    }
                    arrays += 1;
                }
                LowInstr::SetTable(write) => {
                    if arrays != 0 || open || write.kind != crate::transformer::SetTableKind::Normal
                    {
                        valid = false;
                        break;
                    }
                    if template && !runtime_call_key(proto, facts, site.instr, write.key) {
                        // 候选拒绝[ProofIncomplete]：这里只证明 CALL key 不会进入 TDUP
                        // 的静态键集合；静态键覆盖和数组填槽仍由完整构造区域核对。
                        valid = false;
                        break;
                    }
                    records += 1;
                }
                LowInstr::SetList(write) => {
                    // 混合 record/list 的准备与批次写入可能交错；尚无统一事件投影时
                    // 保留原普通区域，不能按最终 SETLIST 的位置倒置字段求值。
                    if template || records != 0 || open || write.start_index as usize != arrays + 1
                    {
                        valid = false;
                        break;
                    }
                    match write.values {
                        ValuePack::Fixed(pack) => arrays += pack.len,
                        ValuePack::Open(start) => {
                            let sources = facts.open_use_sources_at(site.instr);
                            let Some(tail) = sources
                                .defs()
                                .first()
                                .filter(|_| !sources.has_entry() && sources.defs().len() == 1)
                            else {
                                valid = false;
                                break;
                            };
                            let tail = &facts.open_defs[tail.index()];
                            let Some(prefix) = tail.start_reg.index().checked_sub(start.index())
                            else {
                                valid = false;
                                break;
                            };
                            arrays += prefix;
                            open = true;
                            open_call =
                                matches!(proto.instrs[tail.instr.index()], LowInstr::Call(_));
                        }
                    }
                }
                _ => unreachable!("private initialization target was checked"),
            }
        }
        let capacity_matches = match table.allocation {
            crate::transformer::TableAllocation::PucBatched(capacity) => {
                capacity.matches(arrays, records)
            }
            // Luau 的开放 CALL 尾占一个语法数组项，VARARG 尾不计预分配；
            // 与共享 TablePreallocation::matches_luau 的字段投影保持一致。
            crate::transformer::TableAllocation::Luau(capacity) => {
                capacity.matches(arrays + usize::from(open_call), records)
            }
            crate::transformer::TableAllocation::Indexed {
                array_capacity,
                hash_bits,
            } => crate::value_semantics::table::allocation::matches_indexed_capacity(
                array_capacity,
                hash_bits,
                arrays + usize::from(open),
                records,
                false,
            ),
            // 原模板内容原样降低，新增字段的 key 均为运行时 CALL；不会被编译器
            // 提前静态化进模板，也不改变其原数组容量及预置键集合。
            crate::transformer::TableAllocation::Template(_) => true,
            _ => false,
        };
        if valid && capacity_matches {
            initializations.insert(def.id, writes.iter().map(|site| site.instr).collect());
        }
    }
    initializations
}

fn runtime_call_key(
    proto: &LoweredProto,
    facts: &DataflowFacts,
    instr: InstrRef,
    key: AccessKey,
) -> bool {
    let AccessKey::Reg(reg) = key else {
        return false;
    };
    let SsaValue::Def(def) = facts.use_value(instr, reg) else {
        return false;
    };
    matches!(&proto.instrs[facts.def_instr(def).index()], LowInstr::Call(call)
        if call.results == ResultPack::Fixed(RegRange { start: reg, len: 1 }))
}
