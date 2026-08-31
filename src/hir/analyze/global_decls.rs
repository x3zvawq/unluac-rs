//! Lua 5.5 `global` initializer protocol recovery.
//!
//! The compiler evaluates a fixed-result call once, then probes and stores each declared global
//! in reverse source order. This module freezes only complete same-block runs whose SSA identities
//! prove that every probe and call result belongs exclusively to that declaration.

use crate::ast::{AstTargetDialect, is_lua_identifier_name};
use crate::hir::analyze::helpers::decode_raw_string;
use crate::parser::RawLiteralConst;
use crate::structure::{Cfg, DataflowFacts, DefId, SsaValue};
use crate::transformer::{
    AccessBase, AccessKey, GetTableKind, InstrRef, LowInstr, LoweredProto, Reg, RegRange,
    ResultPack, SetTableKind, ValueOperand,
};

#[derive(Debug)]
pub(super) struct GlobalDeclProtocols {
    owners: Vec<Option<GlobalDeclProtocol>>,
}

#[derive(Debug)]
pub(super) struct GlobalDeclProtocol {
    pub(super) end: usize,
    pub(super) names: Vec<String>,
    pub(super) results: RegRange,
}

struct GlobalDeclItem {
    name: String,
    set_ref: InstrRef,
    value_reg: Reg,
}

impl GlobalDeclProtocols {
    pub(super) fn analyze(
        target: AstTargetDialect,
        proto: &LoweredProto,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
    ) -> Self {
        let mut owners = (0..proto.instrs.len()).map(|_| None).collect::<Vec<_>>();
        for block in &cfg.blocks {
            let mut index = block.instrs.start.index();
            let block_end = block.instrs.end();
            while index < block_end {
                let Some(protocol) =
                    recognize_protocol(target, proto, dataflow, InstrRef(index), block_end)
                else {
                    index += 1;
                    continue;
                };
                let owner = protocol_owner(&protocol);
                index = protocol.end;
                owners[owner.index()] = Some(protocol);
            }
        }
        Self { owners }
    }

    pub(super) fn owner(&self, instr: InstrRef) -> Option<&GlobalDeclProtocol> {
        self.owners.get(instr.index())?.as_ref()
    }
}

fn protocol_owner(protocol: &GlobalDeclProtocol) -> InstrRef {
    let width = protocol.results.len;
    InstrRef(protocol.end - 1 - width * 3)
}

fn recognize_protocol(
    target: AstTargetDialect,
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    call_ref: InstrRef,
    block_end: usize,
) -> Option<GlobalDeclProtocol> {
    let LowInstr::Call(call) = proto.instrs.get(call_ref.index())? else {
        return None;
    };
    let ResultPack::Fixed(results) = call.results else {
        return None;
    };
    // Exact HIR tails represent at least two values. Singleton declarations retain the existing
    // syntax recovery path and do not need this multi-result lifetime owner.
    if results.len < 2 {
        return None;
    }
    let end = call_ref
        .index()
        .checked_add(1 + results.len.checked_mul(3)?)?;
    if end > block_end || dataflow.instr_defs.get(call_ref.index())?.len() != results.len {
        return None;
    }

    let mut names = Vec::with_capacity(results.len);
    for reverse_index in 0..results.len {
        let get_ref = InstrRef(call_ref.index() + 1 + reverse_index * 3);
        let item = recognize_item(target, proto, dataflow, get_ref)?;
        let source_index = results.len - 1 - reverse_index;
        let source_reg = Reg(results.start.index().checked_add(source_index)?);
        let result_def = dataflow.instr_def_for_reg(call_ref, source_reg)?;
        if dataflow.use_value(item.set_ref, item.value_reg) != SsaValue::Def(result_def)
            || !def_has_only_direct_use(dataflow, result_def, item.set_ref, item.value_reg)
        {
            return None;
        }
        names.push(item.name);
    }

    // 候选拒绝[SemanticRisk]: a fixed call can provide only the trailing slots of a wider
    // declaration (`global a, b, c = 11, pair()`). Consuming that suffix would strand the leading
    // item as a different declaration, so any immediately adjacent complete item rejects the run.
    if end
        .checked_add(3)
        .is_some_and(|item_end| item_end <= block_end)
        && recognize_item(target, proto, dataflow, InstrRef(end)).is_some()
    {
        return None;
    }
    // 候选拒绝[SemanticRisk]: wide target descriptors can be prepared before the tail call, so
    // the leading item is not necessarily adjacent to the direct suffix. A later ERRNNIL/SET
    // pair consuming a pre-owner SSA value may still belong to this declaration; splitting it
    // would re-evaluate its environment after the call (which can rebind `_ENV`).
    if ((end + 1)..block_end).any(|set_index| {
        matches!(proto.instrs.get(set_index - 1), Some(LowInstr::ErrNil(_)))
            && matches!(proto.instrs.get(set_index), Some(LowInstr::SetTable(_)))
            && set_uses_value_from_before_owner(
                proto,
                dataflow,
                InstrRef(set_index),
                call_ref,
            )
    }) {
        return None;
    }
    names.reverse();

    Some(GlobalDeclProtocol {
        end,
        names,
        results,
    })
}

fn set_uses_value_from_before_owner(
    proto: &LoweredProto,
    dataflow: &DataflowFacts,
    set_ref: InstrRef,
    owner: InstrRef,
) -> bool {
    let Some(LowInstr::SetTable(set)) = proto.instrs.get(set_ref.index()) else {
        return false;
    };
    let ValueOperand::Reg(value_reg) = set.value else {
        return true;
    };
    match dataflow.use_value(set_ref, value_reg) {
        SsaValue::Def(def) => dataflow.def_instr(def).index() < owner.index(),
        SsaValue::Entry(_) | SsaValue::Phi(_) => true,
    }
}

fn recognize_item(
    target: AstTargetDialect,
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

    let probe_name = direct_global_name(target, proto, get.base, get.key)?;
    let store_name = direct_global_name(target, proto, set.base, set.key)?;
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
    target: AstTargetDialect,
    proto: &LoweredProto,
    base: AccessBase,
    key: AccessKey,
) -> Option<String> {
    // 候选拒绝[ProofIncomplete]: Reg/local/wide ENV still needs an explicit lexical identity
    // proof; debug names are not sufficient to recover a global declaration owner.
    let (AccessBase::Env, AccessKey::Const(key)) = (base, key) else {
        return None;
    };
    let name = const_string(proto, key)?;
    is_lua_identifier_name(&name, target.version).then_some(name)
}

fn const_string(proto: &LoweredProto, constant: crate::transformer::ConstRef) -> Option<String> {
    let RawLiteralConst::String(value) = proto.constants.common.literals.get(constant.index())?
    else {
        return None;
    };
    Some(decode_raw_string(value))
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
