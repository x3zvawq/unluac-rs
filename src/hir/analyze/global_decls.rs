//! 从 Low-IR 与 SSA 恢复 Lua 5.5 global 初始化协议。
//!
//! 发布覆盖完整协议的 typed HIR 声明及唯一 owner；标识符合法性和展示形式由 AST 处理。

use crate::parser::RawLiteralConst;
use crate::structure::{Cfg, DataflowFacts, DefId, InstrRange, SsaValue};
use crate::transformer::{
    AccessBase, AccessKey, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg, RegRange,
    ResultPack, SetTableKind, ValueOperand,
};

mod environment;

#[derive(Debug)]
pub(super) struct GlobalDeclProtocols {
    protocols: Vec<GlobalDeclProtocol>,
    protocol_by_instr: Vec<Option<usize>>,
    /// 完整协议已认领的入口局部环境；与根环境 upvalue 身份分开。
    pub(super) local_environment: Option<DefId>,
}

#[derive(Debug)]
pub(super) struct GlobalDeclProtocol {
    owner: InstrRef,
    pub(super) probe: InstrRef,
    pub(super) end: usize,
    pub(super) names: Vec<crate::LuaString>,
    pub(super) values: GlobalDeclValues,
}

#[derive(Debug)]
pub(super) enum GlobalDeclValues {
    FixedCall {
        prefix: Vec<GlobalDeclValueUse>,
        results: RegRange,
        /// 目标 base/key 在 RHS 之前准备；逆序 probe 的准备则属于协议本体。
        wide_targets: Vec<(crate::LuaString, InstrRef)>,
    },
    ValueUses(Vec<GlobalDeclValueUse>),
}

#[derive(Debug)]
pub(super) struct GlobalDeclValueUse {
    pub(super) instr: InstrRef,
    pub(super) reg: Reg,
}

struct GlobalDeclItem {
    name: crate::LuaString,
    set_ref: InstrRef,
    value_reg: Reg,
}

impl GlobalDeclProtocols {
    pub(super) fn record_preparations(
        &self,
        dataflow: &DataflowFacts,
        fixed_temps: &[crate::hir::TempId],
        facts: &mut crate::hir::promotion::ProtoPromotionFacts,
    ) {
        for protocol in &self.protocols {
            if let GlobalDeclValues::ValueUses(values) = &protocol.values
                && let [value] = values.as_slice()
                && protocol.names.len() == 1
            {
                facts.record_global_initializer_write(protocol.probe, value.instr);
            }
            let GlobalDeclValues::FixedCall {
                prefix,
                wide_targets,
                ..
            } = &protocol.values
            else {
                continue;
            };
            if prefix.is_empty() {
                continue;
            }
            let inputs = prefix
                .iter()
                .map(|value| {
                    let SsaValue::Def(def) = dataflow.use_value(value.instr, value.reg) else {
                        unreachable!("recognized global call prefix must have a direct definition");
                    };
                    fixed_temps[def.index()]
                })
                .collect();
            facts.record_global_call_prefix(protocol.owner, inputs, wide_targets.clone());
        }
    }

    /// 协议认领后才把原环境定义物化为局部声明，不增加新的读写或槽位。
    pub(super) fn bind_environment(
        &self,
        bindings: &mut super::lower::ProtoBindings,
        facts: &mut crate::hir::promotion::ProtoPromotionFacts,
    ) -> Result<Option<crate::hir::LocalId>, crate::hir::HirLowerError> {
        let Some(def) = self.local_environment else {
            return Ok(None);
        };
        let temp = bindings.fixed_temps[def.index()];
        let home = facts.trusted_temp_home_slot(temp).ok_or_else(|| {
            crate::hir::HirLowerError::invalid("local environment definition has no unique home")
        })?;
        let local = match bindings.lvalue_for_temp(temp) {
            crate::hir::HirLValue::Local(local)
                if bindings.temp_decl_locals.get(&temp) == Some(&local) =>
            {
                local
            }
            crate::hir::HirLValue::Temp(_) => {
                let local = crate::hir::LocalId(bindings.local_count);
                bindings.local_count += 1;
                bindings
                    .local_debug_hints
                    .push(bindings.temp_debug_locals[temp.index()].clone());
                bindings
                    .local_debug_scopes
                    .push(bindings.temp_debug_scopes[temp.index()]);
                bindings.temp_decl_locals.insert(temp, local);
                bindings
                    .bound_temp_targets
                    .insert(temp, super::lower::BoundSlotTarget::Local(local));
                bindings.declared_local_home_slots.push((local, home));
                local
            }
            _ => {
                return Err(crate::hir::HirLowerError::invalid(
                    "local environment conflicts with an existing binding",
                ));
            }
        };
        facts.record_local_home_slot(local, home);
        facts.record_temp_to_local_merge(temp, local);
        Ok(Some(local))
    }

    pub(super) fn analyze(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Self {
        let local_environment = environment::entry_snapshot(proto, cfg, dataflow);
        let mut protocols = Vec::new();
        let mut protocol_by_instr = Vec::new();
        for block in &cfg.blocks {
            let mut suffix_ends = None;
            let mut index = block.instrs.start.index();
            let block_end = block.instrs.end();
            while index < block_end {
                let protocol = match recognize_call_protocol(
                    proto,
                    dataflow,
                    local_environment,
                    InstrRef(index),
                    block.instrs,
                    &mut suffix_ends,
                ) {
                    CallProtocolMatch::Claimed(protocol) => protocol,
                    CallProtocolMatch::Blocked { resume_at } => {
                        index = resume_at;
                        continue;
                    }
                    CallProtocolMatch::None => {
                        let Some(protocol) = recognize_value_run_protocol(
                            proto,
                            dataflow,
                            local_environment,
                            InstrRef(index),
                            block_end,
                        ) else {
                            index += 1;
                            continue;
                        };
                        protocol
                    }
                };
                // 每次 claim 后越过完整协议；不重叠的覆盖索引同时服务 owner 与词法边界查询。
                if protocol_by_instr.len() < protocol.end {
                    protocol_by_instr.resize(protocol.end, None);
                }
                protocol_by_instr[protocol.owner.index()..protocol.end].fill(Some(protocols.len()));
                index = protocol.end;
                protocols.push(protocol);
            }
        }
        Self {
            local_environment: local_environment.filter(|_| !protocols.is_empty()),
            protocols,
            protocol_by_instr,
        }
    }

    pub(super) fn owner(&self, instr: InstrRef) -> Option<&GlobalDeclProtocol> {
        self.at(instr.index())
            .filter(|protocol| protocol.owner == instr)
    }

    fn at(&self, instr: usize) -> Option<&GlobalDeclProtocol> {
        let index = self.protocol_by_instr.get(instr).copied().flatten()?;
        Some(&self.protocols[index])
    }

    /// 只检查当前 lowering 区间内开始的协议；owner 与 end 本身都允许作为词法边界。
    pub(super) fn splits_protocol(&self, range_start: usize, boundary: usize) -> bool {
        self.at(boundary).is_some_and(|protocol| {
            protocol.owner.index() >= range_start && protocol.owner.index() < boundary
        })
    }
}

enum CallProtocolMatch {
    Claimed(GlobalDeclProtocol),
    Blocked { resume_at: usize },
    None,
}

fn recognize_call_protocol(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    call_ref: InstrRef,
    block: InstrRange,
    suffix_ends: &mut Option<Vec<Option<usize>>>,
) -> CallProtocolMatch {
    let block_end = block.end();
    let Some(LowInstr::Call(call)) = proto.instrs.get(call_ref.index()) else {
        return CallProtocolMatch::None;
    };
    let ResultPack::Fixed(results) = call.results else {
        return CallProtocolMatch::None;
    };
    if results.len == 0 {
        return CallProtocolMatch::None;
    }
    let Some(mut end) = results
        .len
        .checked_mul(3)
        .and_then(|item_width| item_width.checked_add(1))
        .and_then(|width| call_ref.index().checked_add(width))
    else {
        return CallProtocolMatch::None;
    };
    if end > block_end
        || dataflow
            .instr_defs
            .get(call_ref.index())
            .is_none_or(|defs| defs.len() != results.len)
    {
        return CallProtocolMatch::None;
    }

    let mut names = Vec::with_capacity(results.len);
    for reverse_index in 0..results.len {
        let get_ref = InstrRef(call_ref.index() + 1 + reverse_index * 3);
        let Some(item) = recognize_item(proto, dataflow, local_environment, get_ref) else {
            return CallProtocolMatch::None;
        };
        let source_index = results.len - 1 - reverse_index;
        let Some(source_index) = results.start.index().checked_add(source_index) else {
            return CallProtocolMatch::None;
        };
        let source_reg = Reg(source_index);
        let Some(result_def) = dataflow.instr_def_for_reg(call_ref, source_reg) else {
            return CallProtocolMatch::None;
        };
        if dataflow.use_value(item.set_ref, item.value_reg) != SsaValue::Def(result_def)
            || !def_has_only_direct_use(dataflow, result_def, item.set_ref, item.value_reg)
        {
            return CallProtocolMatch::None;
        }
        names.push(item.name);
    }

    let mut prefix = Vec::new();
    let mut wide_targets = Vec::new();
    while end
        .checked_add(3)
        .is_some_and(|item_end| item_end <= block_end)
    {
        let Some((item, item_end, wide)) =
            recognize_prefix_item(proto, dataflow, local_environment, end, block_end)
        else {
            break;
        };
        let expected = results.start.index().checked_sub(prefix.len() + 1);
        let value = dataflow.use_value(item.set_ref, item.value_reg);
        // 候选拒绝[ProofIncomplete]：前缀必须是 CALL 下方连续的独占准备值，且在 CALL 前
        // 已定义；否则不能把后续独立声明或被闭包修改的现成 local 提前作为 RHS 读取。
        if expected != Some(item.value_reg.index())
            || !matches!(value, SsaValue::Def(def)
                if dataflow.def_instr(def).index() < call_ref.index()
                    && def_has_only_direct_use(dataflow, def, item.set_ref, item.value_reg))
        {
            if results.len == 1 && prefix.is_empty() {
                return CallProtocolMatch::None;
            }
            return CallProtocolMatch::Blocked {
                resume_at: contiguous_item_run_end(
                    proto,
                    dataflow,
                    local_environment,
                    end,
                    block_end,
                ),
            };
        }
        if wide {
            wide_targets.push((item.name.clone(), item.set_ref));
        }
        names.push(item.name);
        prefix.push(GlobalDeclValueUse {
            instr: item.set_ref,
            reg: item.value_reg,
        });
        end = item_end;
    }
    // 候选拒绝[SemanticBarrier:EvalOrder]: wide target descriptors can be prepared before the tail call, so
    // the leading item is not necessarily adjacent to the direct suffix. A later ERRNNIL/SET
    // pair consuming a pre-owner SSA value may still belong to this declaration; splitting it
    // would re-evaluate its environment after the call, which can rebind `_ENV`
    // (regress_410_lua55_wide_mixed_global_rhs).
    let suffix_ends = suffix_ends
        .get_or_insert_with(|| pre_owner_item_ends(proto, dataflow, local_environment, block));
    if let Some(resume_at) =
        suffix_ends[call_ref.index() - block.start.index()].filter(|&item_end| item_end >= end + 3)
    {
        return CallProtocolMatch::Blocked { resume_at };
    }
    names.reverse();
    prefix.reverse();
    wide_targets.reverse();
    let first_value = prefix
        .iter()
        .filter_map(|value| match dataflow.use_value(value.instr, value.reg) {
            SsaValue::Def(def) => Some(dataflow.def_instr(def)),
            _ => None,
        })
        .min()
        .unwrap_or(call_ref);
    let mut previous_target_end = block.start;
    for (_, store_ref) in &wide_targets {
        let LowInstr::SetTable(store) = &proto.instrs[store_ref.index()] else {
            unreachable!()
        };
        let (AccessBase::Reg(base), AccessKey::Reg(key)) = (store.base, store.key) else {
            unreachable!()
        };
        let (SsaValue::Def(base), SsaValue::Def(key)) = (
            dataflow.use_value(*store_ref, base),
            dataflow.use_value(*store_ref, key),
        ) else {
            unreachable!()
        };
        let base = dataflow.def_instr(base);
        let key = dataflow.def_instr(key);
        // 候选拒绝[ProofIncomplete:EvalOrder]：目标快照必须按声明顺序在本块所有 RHS
        // 之前完成；不能把后取得的环境快照提前越过可能改写 _ENV 的前缀表达式。
        if base < previous_target_end || key >= first_value {
            return CallProtocolMatch::Blocked { resume_at: end };
        }
        previous_target_end = InstrRef(key.index() + 1);
    }

    CallProtocolMatch::Claimed(GlobalDeclProtocol {
        owner: call_ref,
        probe: InstrRef(call_ref.index() + 1),
        end,
        names,
        values: GlobalDeclValues::FixedCall {
            prefix,
            results,
            wide_targets,
        },
    })
}

/// 宽 probe 的环境和名字准备是协议的一部分，不能把它们当作下一条声明的边界。
fn recognize_prefix_item(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    start: usize,
    block_end: usize,
) -> Option<(GlobalDeclItem, usize, bool)> {
    if let Some(item) = recognize_item(proto, dataflow, local_environment, InstrRef(start)) {
        return Some((item, start + 3, false));
    }
    let end = start.checked_add(5)?;
    if end > block_end || local_environment.is_some() {
        return None;
    }
    let item = recognize_item(proto, dataflow, local_environment, InstrRef(start + 2))?;
    let LowInstr::GetTable(probe) = &proto.instrs[start + 2] else {
        return None;
    };
    let LowInstr::SetTable(store) = &proto.instrs[item.set_ref.index()] else {
        return None;
    };
    for (site, base, key, at_probe) in [
        (InstrRef(start + 2), probe.base, probe.key, true),
        (item.set_ref, store.base, store.key, false),
    ] {
        let (AccessBase::Reg(base), AccessKey::Reg(key)) = (base, key) else {
            return None;
        };
        let (SsaValue::Def(base_def), SsaValue::Def(key_def)) = (
            dataflow.use_value(site, base),
            dataflow.use_value(site, key),
        ) else {
            return None;
        };
        let base_read = dataflow.def_instr(base_def);
        let key_read = dataflow.def_instr(key_def);
        // 候选拒绝[ProofIncomplete]：只认领独占、相邻的原环境/字符串准备；
        // MOVE、共享快照和其它表达式不能因最终名字相同而失去自己的执行位置。
        if key.index() != base.index() + 1
            || key_read.index() != base_read.index() + 1
            || !def_has_only_direct_use(dataflow, base_def, site, base)
            || !def_has_only_direct_use(dataflow, key_def, site, key)
            || !matches!(&proto.instrs[base_read.index()], LowInstr::GetUpvalue(get)
                if matches!(get.src, crate::transformer::UpvalueOperand::Env(_)))
            || !matches!(&proto.instrs[key_read.index()], LowInstr::LoadConst(load)
                if const_string(proto, load.value).as_ref() == Some(&item.name))
            || (at_probe && (base_read.index() != start || probe.dst != base))
        {
            return None;
        }
        if !at_probe {
            let SsaValue::Def(value) = dataflow.use_value(site, item.value_reg) else {
                return None;
            };
            if key_read >= dataflow.def_instr(value) {
                return None;
            }
        }
    }
    Some((item, end, true))
}

/// 按候选 owner 的物理位置冻结可阻断 item 的最远末端。直接 Def 只从下一条指令起
/// 生效；Entry/Phi 从块入口生效，不能沿 Move 追到更早的值根。前缀最大值保留旧后缀
/// 查询的最后一个 item，避免每个 call 重新识别剩余块内的全部三指令协议。
fn pre_owner_item_ends(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    block: InstrRange,
) -> Vec<Option<usize>> {
    let start = block.start.index();
    let mut ends = vec![None; block.len];
    for set_index in (start + 2)..block.end() {
        let Some(item) =
            recognize_item(proto, dataflow, local_environment, InstrRef(set_index - 2))
        else {
            continue;
        };
        let active_from = match dataflow.use_value(item.set_ref, item.value_reg) {
            SsaValue::Def(def) => (dataflow.def_instr(def).index() + 1).max(start),
            SsaValue::Entry(_) | SsaValue::Phi(_) => start,
        };
        if let Some(end) = ends.get_mut(active_from - start) {
            *end = (*end).max(Some(set_index + 1));
        }
    }
    let mut latest = None;
    for end in &mut ends {
        latest = latest.max(*end);
        *end = latest;
    }
    ends
}

fn recognize_value_run_protocol(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    owner: InstrRef,
    block_end: usize,
) -> Option<GlobalDeclProtocol> {
    let mut cursor = owner.index();
    let mut items = Vec::new();
    while cursor.checked_add(3).is_some_and(|end| end <= block_end) {
        let Some(item) = recognize_item(proto, dataflow, local_environment, InstrRef(cursor))
        else {
            break;
        };
        items.push(item);
        cursor += 3;
    }
    if items.is_empty() {
        return None;
    }

    items.reverse();
    let (names, values) = items
        .into_iter()
        .map(|item| {
            (
                item.name,
                GlobalDeclValueUse {
                    instr: item.set_ref,
                    reg: item.value_reg,
                },
            )
        })
        .unzip();
    Some(GlobalDeclProtocol {
        owner,
        probe: owner,
        end: cursor,
        names,
        values: GlobalDeclValues::ValueUses(values),
    })
}

fn contiguous_item_run_end(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    start: usize,
    block_end: usize,
) -> usize {
    let mut cursor = start;
    while cursor.checked_add(3).is_some_and(|end| end <= block_end)
        && recognize_item(proto, dataflow, local_environment, InstrRef(cursor)).is_some()
    {
        cursor += 3;
    }
    cursor
}

fn recognize_item(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    get_ref: InstrRef,
) -> Option<GlobalDeclItem> {
    let err_ref = InstrRef(get_ref.index().checked_add(1)?);
    let set_ref = InstrRef(get_ref.index().checked_add(2)?);
    let (LowInstr::GetTable(get), LowInstr::ErrNil(err_nil), LowInstr::SetTable(set)) = (
        proto.instrs.get(get_ref.index())?,
        proto.instrs.get(err_ref.index())?,
        proto.instrs.get(set_ref.index())?,
    ) else {
        return None;
    };
    if get.kind != GetTableKind::Normal || set.kind != SetTableKind::Normal {
        return None;
    }

    let probe_name = direct_global_name(
        proto,
        dataflow,
        local_environment,
        get_ref,
        get.base,
        get.key,
    )?;
    let store_name = direct_global_name(
        proto,
        dataflow,
        local_environment,
        set_ref,
        set.base,
        set.key,
    )?;
    let guard_name = const_string(proto, err_nil.name?)?;
    if probe_name != store_name || probe_name != guard_name {
        return None;
    }

    let probe_def = dataflow.instr_def_for_reg(get_ref, get.dst)?;
    if dataflow.use_value(err_ref, err_nil.subject) != SsaValue::Def(probe_def)
        || !def_has_only_direct_use(dataflow, probe_def, err_ref, err_nil.subject)
    {
        return None;
    }

    let ValueOperand::Reg(value_reg) = set.value else {
        return None;
    };
    Some(GlobalDeclItem {
        name: probe_name,
        set_ref,
        value_reg,
    })
}

fn direct_global_name(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    instr: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> Option<crate::LuaString> {
    // 宽常量形状会先把 `_ENV` 和 key 物化到寄存器；这里只追溯无 phi 的
    // move/load 链，保留与直接 operand 相同的 raw-byte 身份，不做文本解码。
    access_base_is_env(proto, dataflow, local_environment, instr, base)
        .then(|| raw_key_for_access(proto, dataflow, instr, key))?
}

fn access_base_is_env(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    local_environment: Option<DefId>,
    instr: InstrRef,
    base: AccessBase,
) -> bool {
    match base {
        AccessBase::Env | AccessBase::EnvironmentUpvalue(_) => true,
        AccessBase::Reg(reg) => {
            // 局部环境角色必须保留实际 GET/SET base 的 Def/home；MOVE 的 canonical
            // 源只证明值相同，不能授权删掉另一个环境槽并下移后续调用帧。
            if let Some(def) = local_environment {
                return reg == dataflow.def_reg(def)
                    && dataflow.use_value(instr, reg) == SsaValue::Def(def);
            }
            resolve_reg_def(dataflow, instr, reg).is_some_and(|def_instr| {
                matches!(
                    proto.instrs.get(def_instr.index()),
                    Some(LowInstr::GetUpvalue(get))
                        if matches!(get.src, crate::transformer::UpvalueOperand::Env(_))
                )
            })
        }
        AccessBase::Upvalue(_) => false,
    }
}

fn raw_key_for_access(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    key: AccessKey,
) -> Option<crate::LuaString> {
    let constant = match key {
        AccessKey::Const(constant) => constant,
        AccessKey::Reg(reg) => {
            let def_instr = resolve_reg_def(dataflow, instr, reg)?;
            let LowInstr::LoadConst(load) = proto.instrs.get(def_instr.index())? else {
                return None;
            };
            load.value
        }
        AccessKey::Integer(_) => return None,
    };
    const_string(proto, constant)
}

fn resolve_reg_def(dataflow: &DataflowFacts, use_instr: InstrRef, reg: Reg) -> Option<InstrRef> {
    let SsaValue::Def(def) = dataflow.canonical_move_value(dataflow.use_value(use_instr, reg))?
    else {
        return None;
    };
    Some(dataflow.def_instr(def))
}

fn const_string(
    proto: &LoweredProto,
    constant: crate::transformer::ConstRef,
) -> Option<crate::LuaString> {
    let RawLiteralConst::String(value) = proto.constants.get(constant.index())? else {
        return None;
    };
    Some(crate::LuaString::from_raw(value))
}

fn def_has_only_direct_use(
    dataflow: &DataflowFacts,
    def: DefId,
    instr: InstrRef,
    reg: Reg,
) -> bool {
    dataflow
        .def_phi_uses
        .get(def.index())
        .is_some_and(Vec::is_empty)
        && matches!(
            dataflow.def_uses.get(def.index()).map(Vec::as_slice),
            Some([site]) if site.instr == instr && site.reg == reg
        )
}
