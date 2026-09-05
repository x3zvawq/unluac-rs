//! 为入口 debug scope 分配参数或 local 绑定并提取 closure 名称；依赖 Structure 的入口 SSA 身份，不负责循环/捕获合并。例如参数 scope 的后续 nil 写仍写回 ParamId。

use super::*;

/// 函数入口已经活跃、且没有显式 producer 的源码 local 由 VM 的 nil 初值承载。
///
/// 若继续把 `Entry(reg)` 只当作一个普通 nil 值，loop-carried phi 会在循环前才被
/// `locals` 提升，进而把源码声明错误地移动到前置调用之后。这里直接建立 scope 对应的
/// `LocalId`，后续同 scope 的 def/phi temp 都写回这个绑定。参数 scope 则直接使用入口
/// `ParamId`，重绑定不另建会延长旧参数 root 生命周期的 local。
pub(super) fn allocate_debug_entry_bindings(
    proto: &LoweredProto,
    structure: &ReadyStructureFacts,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
    local_debug_hints: &mut Vec<Option<String>>,
) -> (Vec<LocalId>, BTreeMap<usize, BoundSlotTarget>) {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_reg = proto
        .signature
        .has_vararg_param_reg
        .then_some(Reg(param_count));
    let mut declarations = Vec::new();
    let mut scope_targets = BTreeMap::new();

    for fact in &structure.debug_bindings().accepted {
        let SsaValue::Entry(reg) = fact.value else {
            continue;
        };
        if fact.start_pc != 0 || Some(reg) == vararg_reg {
            continue;
        }
        if reg.index() < param_count {
            scope_targets.insert(fact.scope, BoundSlotTarget::Param(ParamId(reg.index())));
            continue;
        }
        let Some(debug_local) = proto.debug_locals.get(fact.scope) else {
            continue;
        };
        let local = if let Some(local) = entry_local_regs.get(&reg).copied() {
            local
        } else {
            let local = LocalId(locals.len());
            locals.push(local);
            local_debug_hints.push(Some(decode_raw_string(&debug_local.name)));
            entry_local_regs.insert(reg, local);
            declarations.push(local);
            local
        };
        scope_targets.insert(fact.scope, BoundSlotTarget::Local(local));
    }

    (declarations, scope_targets)
}

pub(super) fn closure_debug_name(proto: &LoweredProto, instr: Option<&LowInstr>) -> Option<String> {
    let LowInstr::Closure(closure) = instr? else {
        return None;
    };
    proto
        .children
        .get(closure.proto.index())?
        .debug_name
        .as_ref()
        .map(decode_raw_string)
}
