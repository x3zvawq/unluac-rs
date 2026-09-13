//! 在原始基本块内证明尚未暴露的新表读取不会进入元方法。
//!
//! NewTable 是唯一事实源；寄存器覆盖、外部使用和可见 debug binding 的用户代码观察
//! 会结束证明。跨块合流暂不传播，后层只消费具体读取的证书，不从 constructor 源码形状
//! 重建逃逸。例如 `local ids={DS.AP,DS.SH}; return ids[1],ids[2]` 中，初始化期间 ids
//! 尚不属于活动 source scope，后续自身的普通读取不会凭空成为 GC 回调。
//! DebugScope 按维护地图只保护保留的 source identity；未命名临时数字槽不充当逃逸来源。

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
