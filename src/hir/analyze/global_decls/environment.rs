//! 从入口快照与 global 协议证明局部词法环境身份。
//!
//! 消费 Low-IR/SSA 的唯一来源，发布 binding 的环境角色，不根据 debug 名字推断环境。

use super::*;
use crate::transformer::UpvalueOperand;

pub(super) fn entry_snapshot(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
) -> Option<DefId> {
    // 候选拒绝[ProofIncomplete:Scope]：尚无混合根环境/局部环境或跨块绑定范围证书。
    if !proto.environment_upvalues.is_empty()
        || !proto.children.is_empty()
        || cfg.block_order.len() != 1
        || cfg.edges.iter().any(|edge| edge.to != cfg.exit_block)
        || proto.signature.has_vararg_param_reg
        || proto.signature.legacy_arg_slot
    {
        return None;
    }
    let (destination, source) = match proto.instrs.first()? {
        LowInstr::GetUpvalue(first) => {
            let UpvalueOperand::Upvalue(source) = first.src else {
                return None;
            };
            (first.dst, Some(source))
        }
        LowInstr::Move(first)
            if first.src.index() < usize::from(proto.signature.num_params)
                && dataflow.use_value(InstrRef(0), first.src) == SsaValue::Entry(first.src) =>
        {
            // 参数只是快照的值来源；环境角色属于新的 Def，不能合并两个物理槽。
            (first.dst, None)
        }
        _ => return None,
    };
    if destination.index() != usize::from(proto.signature.num_params) {
        return None;
    }
    let def = dataflow.instr_def_for_reg(InstrRef(0), destination)?;
    // 调试表若存在，环境槽只能有一个贯穿后续指令的 source scope。
    // 缺失调试表由单 Def/无关闭证明；不能用名字补造 scope 身份。
    let mut scopes = proto
        .debug_locals
        .iter()
        .filter(|local| local.reg == destination && local.is_source());
    if let Some(scope) = scopes.next()
        && (scopes.next().is_some()
            || proto
                .lowering_map
                .pc_map()
                .iter()
                .skip(1)
                .flatten()
                .any(|&pc| pc < scope.start_pc || pc >= scope.end_pc))
    {
        return None;
    }
    if dataflow
        .defs
        .iter()
        .any(|other| other.reg == destination && other.id != def)
        || !dataflow.def_phi_uses[def.index()].is_empty()
        || dataflow
            .open_defs
            .iter()
            .any(|open| open.start_reg <= destination)
    {
        // 候选拒绝[ProofIncomplete:Identity]：不以入口值代替后继写入、Phi 或开放结果。
        return None;
    }
    if proto.instrs.iter().skip(1).any(|instr| match instr {
        LowInstr::Close(_) | LowInstr::Tbc(_) => true,
        LowInstr::GetUpvalue(get) => {
            source.is_some_and(|source| get.src == UpvalueOperand::Upvalue(source))
                || matches!(get.src, UpvalueOperand::Env(_))
        }
        LowInstr::SetUpvalue(set) => {
            source.is_some_and(|source| set.dst == UpvalueOperand::Upvalue(source))
                || matches!(set.dst, UpvalueOperand::Env(_))
        }
        LowInstr::GetTable(get) => {
            source.is_some_and(|source| get.base == AccessBase::Upvalue(source))
                || matches!(
                    get.base,
                    AccessBase::Env | AccessBase::EnvironmentUpvalue(_)
                )
        }
        LowInstr::SetTable(set) => {
            source.is_some_and(|source| set.base == AccessBase::Upvalue(source))
                || matches!(
                    set.base,
                    AccessBase::Env | AccessBase::EnvironmentUpvalue(_)
                )
        }
        _ => false,
    }) {
        // 候选拒绝[ProofIncomplete:Scope]：源 upvalue 若也名为 _ENV，局部声明之后仍须
        // 访问其原 cell；不能让固定语义名称遮蔽这种独立使用。
        return None;
    }
    Some(def)
}
