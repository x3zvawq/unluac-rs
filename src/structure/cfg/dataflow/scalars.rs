//! 从原 SSA 定义、MOVE 和 phi 传播未捕获的标量事实，供结构和 HIR 生命周期共同消费。

use super::*;

/// Luau 没有 debug.setlocal；未按引用捕获的标量经过 MOVE/phi 仍不持有 GC 根。
/// 一次 worklist 传播全部定义，避免每个 COPY 重新展开共享 phi 图。循环只有在所有
/// 输入已有证明时才接受，不把自引用当作标量证据；未知入口和捕获 cell 留在未知域。
pub(super) fn collect(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Vec<bool> {
    let count = dataflow.defs.len();
    let mut inert = vec![false; count + dataflow.phi_candidates.len()];
    let mut pending = vec![usize::MAX; inert.len()];
    let mut users = vec![Vec::new(); inert.len()];
    let mut ready = Vec::new();
    let index = |value: SsaValue| match value {
        SsaValue::Def(def) => Some(def.index()),
        SsaValue::Phi(phi) => Some(count + phi.index()),
        _ => None,
    };
    for def in &dataflow.defs {
        if dataflow.reference_capture_may_be_open(def.reg, def.instr) {
            continue;
        }
        let instr = &proto.instrs[def.instr.index()];
        if !low_instr_def_may_hold_gc_root(instr, def.reg) {
            ready.push(def.id.index());
        } else if let LowInstr::Move(copy) = instr
            && !dataflow.reference_capture_may_be_open(copy.src, def.instr)
            && let Some(input) = index(dataflow.use_value(def.instr, copy.src))
        {
            pending[def.id.index()] = 1;
            users[input].push(def.id.index());
        }
    }
    for phi in &dataflow.phi_candidates {
        if dataflow
            .reference_capture_may_be_open(phi.reg, cfg.blocks[phi.block.index()].instrs.start)
            || phi.incoming.is_empty()
        {
            continue;
        }
        let Some(inputs) = phi
            .incoming
            .iter()
            .map(|input| index(input.value))
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let target = count + phi.id.index();
        pending[target] = inputs.len();
        for input in inputs {
            users[input].push(target);
        }
    }
    while let Some(value) = ready.pop() {
        if std::mem::replace(&mut inert[value], true) {
            continue;
        }
        for &user in &users[value] {
            pending[user] -= 1;
            if pending[user] == 0 {
                ready.push(user);
            }
        }
    }
    inert
}

pub(crate) fn low_instr_def_may_hold_gc_root(instr: &LowInstr, reg: Reg) -> bool {
    match instr {
        LowInstr::LoadNil(load_nil)
            if load_nil.dst.start.index() <= reg.index()
                && reg.index() < load_nil.dst.start.index().saturating_add(load_nil.dst.len) =>
        {
            false
        }
        LowInstr::LoadBool(load_bool) if load_bool.dst == reg => false,
        LowInstr::LoadInteger(load_integer) if load_integer.dst == reg => false,
        LowInstr::LoadNumber(load_number) if load_number.dst == reg => false,
        LowInstr::UnaryOp(unary)
            if unary.dst == reg && matches!(unary.op, crate::transformer::UnaryOpKind::Not) =>
        {
            false
        }
        LowInstr::TypeGuard(guard)
            if guard.subject == reg
                && matches!(
                    guard.kind,
                    crate::transformer::TypeGuardKind::Integer
                        | crate::transformer::TypeGuardKind::Number
                ) =>
        {
            false
        }
        LowInstr::NumericForInit(init) if init.normalizes_slot(reg) => false,
        // body 可改写独立用户槽，退出边未必再写它；JIT dual-number 溢出也可先退出。
        // 这里只保留内部 index 的数值事实，binding 与它共槽时自然消费同一保证。
        LowInstr::NumericForLoop(loop_) if loop_.index == reg => false,
        _ => true,
    }
}
