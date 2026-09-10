//! 这个文件恢复 Lua 5.5 `global` 初始化协议，并冻结协议在 HIR 中的唯一 owner。
//!
//! 编译器先完整求值 RHS，再按源码 target 的逆序发出 `GETTABLE / ERRNNIL / SETTABLE`。
//! 单结果调用可连同唯一 target 由调用指令直接认领；其它标量结果由完整 target run
//! 认领，并在 HIR 中保留原有 value carrier。多结果调用只有在全部 result 与 target
//! item 都能由 SSA 唯一配对时才整体认领，避免部分声明改变写入顺序或 GC root 生命周期。
//! 本模块不根据普通 global 写入猜声明，也不处理声明合并或展示 sugar。
//! 协议中的原始名字只作为 VM 常量身份保留；它能否作为目标 Lua 方言的声明标识符，
//! 由 AST lowering 统一验证，HIR 不依赖 AST 语法规则。
//!
//! 输入形状：`CALL fixed(r0) + GETTABLE + ERRNNIL + SETTABLE`。
//! 输出形状：一个 owner 覆盖完整区间的 typed `HirStmt::GlobalDecl` 协议。

use crate::parser::RawLiteralConst;
use crate::structure::{Cfg, DataflowFacts, DefId, InstrRange, SsaValue};
use crate::transformer::{
    AccessBase, AccessKey, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg, RegRange,
    ResultPack, SetTableKind, ValueOperand,
};

#[derive(Debug)]
pub(super) struct GlobalDeclProtocols {
    protocols: Vec<GlobalDeclProtocol>,
    protocol_by_instr: Vec<Option<usize>>,
}

#[derive(Debug)]
pub(super) struct GlobalDeclProtocol {
    owner: InstrRef,
    pub(super) end: usize,
    pub(super) names: Vec<crate::LuaString>,
    pub(super) values: GlobalDeclValues,
}

#[derive(Debug)]
pub(super) enum GlobalDeclValues {
    FixedCall(RegRange),
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
    pub(super) fn analyze(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Self {
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
    let Some(end) = results
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
        let Some(item) = recognize_item(proto, dataflow, get_ref) else {
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

    // 候选拒绝[SemanticBarrier:ValueArity]: a fixed call can provide only the trailing slots of a wider
    // declaration (`global a, b, c = 11, pair()`). Consuming that suffix would strand the leading
    // item as a different declaration, so any immediately adjacent complete item rejects the run
    // (regress_410_lua55_mixed_global_rhs).
    if end
        .checked_add(3)
        .is_some_and(|item_end| item_end <= block_end)
        && recognize_item(proto, dataflow, InstrRef(end)).is_some()
    {
        if results.len == 1 {
            return CallProtocolMatch::None;
        }
        return CallProtocolMatch::Blocked {
            resume_at: contiguous_item_run_end(proto, dataflow, end, block_end),
        };
    }
    // 候选拒绝[SemanticBarrier:EvalOrder]: wide target descriptors can be prepared before the tail call, so
    // the leading item is not necessarily adjacent to the direct suffix. A later ERRNNIL/SET
    // pair consuming a pre-owner SSA value may still belong to this declaration; splitting it
    // would re-evaluate its environment after the call, which can rebind `_ENV`
    // (regress_410_lua55_wide_mixed_global_rhs).
    let suffix_ends =
        suffix_ends.get_or_insert_with(|| pre_owner_item_ends(proto, dataflow, block));
    if let Some(resume_at) =
        suffix_ends[call_ref.index() - block.start.index()].filter(|&item_end| item_end >= end + 3)
    {
        return CallProtocolMatch::Blocked { resume_at };
    }
    names.reverse();

    CallProtocolMatch::Claimed(GlobalDeclProtocol {
        owner: call_ref,
        end,
        names,
        values: GlobalDeclValues::FixedCall(results),
    })
}

/// 按候选 owner 的物理位置冻结可阻断 item 的最远末端。直接 Def 只从下一条指令起
/// 生效；Entry/Phi 从块入口生效，不能沿 Move 追到更早的值根。前缀最大值保留旧后缀
/// 查询的最后一个 item，避免每个 call 重新识别剩余块内的全部三指令协议。
fn pre_owner_item_ends(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    block: InstrRange,
) -> Vec<Option<usize>> {
    let start = block.start.index();
    let mut ends = vec![None; block.len];
    for set_index in (start + 2)..block.end() {
        let Some(item) = recognize_item(proto, dataflow, InstrRef(set_index - 2)) else {
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
    owner: InstrRef,
    block_end: usize,
) -> Option<GlobalDeclProtocol> {
    let mut cursor = owner.index();
    let mut items = Vec::new();
    while cursor.checked_add(3).is_some_and(|end| end <= block_end) {
        let Some(item) = recognize_item(proto, dataflow, InstrRef(cursor)) else {
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
        end: cursor,
        names,
        values: GlobalDeclValues::ValueUses(values),
    })
}

fn contiguous_item_run_end(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    start: usize,
    block_end: usize,
) -> usize {
    let mut cursor = start;
    while cursor.checked_add(3).is_some_and(|end| end <= block_end)
        && recognize_item(proto, dataflow, InstrRef(cursor)).is_some()
    {
        cursor += 3;
    }
    cursor
}

fn recognize_item(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
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

    let probe_name = direct_global_name(proto, dataflow, get_ref, get.base, get.key)?;
    let store_name = direct_global_name(proto, dataflow, set_ref, set.base, set.key)?;
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
    instr: InstrRef,
    base: AccessBase,
    key: AccessKey,
) -> Option<crate::LuaString> {
    // 宽常量形状会先把 `_ENV` 和 key 物化到寄存器；这里只追溯无 phi 的
    // move/load 链，保留与直接 operand 相同的 raw-byte 身份，不做文本解码。
    access_base_is_env(proto, dataflow, instr, base)
        .then(|| raw_key_for_access(proto, dataflow, instr, key))?
}

fn access_base_is_env(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    instr: InstrRef,
    base: AccessBase,
) -> bool {
    match base {
        AccessBase::Env | AccessBase::EnvironmentUpvalue(_) => true,
        AccessBase::Reg(reg) => resolve_reg_def(dataflow, instr, reg).is_some_and(|def_instr| {
            matches!(
                proto.instrs.get(def_instr.index()),
                Some(LowInstr::GetUpvalue(get))
                    if matches!(get.src, crate::transformer::UpvalueOperand::Env(_))
            )
        }),
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
