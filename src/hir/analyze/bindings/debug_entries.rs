//! 为函数入口 debug local 分配绑定并提取 closure 名称；依赖 debug scope 与 lowering，不负责循环/捕获合并；例如把 Entry(reg) 映射到稳定 LocalId。

use super::*;

/// 函数入口已经活跃、且没有显式 producer 的源码 local 由 VM 的 nil 初值承载。
///
/// 若继续把 `Entry(reg)` 只当作一个普通 nil 值，loop-carried phi 会在循环前才被
/// `locals` 提升，进而把源码声明错误地移动到前置调用之后。这里直接建立 scope 对应的
/// `LocalId`，后续同 scope 的 def/phi temp 都写回这个绑定。
pub(super) fn allocate_debug_entry_locals(
    proto: &LoweredProto,
    structure: &StructureFacts,
    entry_local_regs: &mut BTreeMap<Reg, LocalId>,
    locals: &mut Vec<LocalId>,
    local_debug_hints: &mut Vec<Option<String>>,
) -> (Vec<LocalId>, BTreeMap<usize, LocalId>) {
    let param_count = usize::from(proto.signature.num_params);
    let vararg_reg = proto
        .signature
        .has_vararg_param_reg
        .then_some(Reg(param_count));
    let mut declarations = Vec::new();
    let mut scope_locals = BTreeMap::new();

    for fact in &structure.debug_bindings().accepted {
        let SsaValue::Entry(reg) = fact.value else {
            continue;
        };
        if fact.start_pc != 0 || reg.index() < param_count || Some(reg) == vararg_reg {
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
        scope_locals.insert(fact.scope, local);
    }

    (declarations, scope_locals)
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
