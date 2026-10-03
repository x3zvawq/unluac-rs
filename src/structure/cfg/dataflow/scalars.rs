//! 从原 SSA 定义、MOVE 和 phi 传播未捕获的标量事实，供结构和 HIR 生命周期共同消费。

use super::*;

/// Luau 没有 debug.setlocal；未按引用捕获的标量经过 MOVE/phi 仍不持有 GC 根。
/// 每个事实域用一次 worklist 传播定义，避免每个 COPY 重新展开共享 phi 图。循环只有在所有
/// 输入已有证明时才接受，不把自引用当作标量证据；未知入口和捕获 cell 留在未知域。
pub(super) fn collect(proto: &LoweredProto, cfg: &Cfg, dataflow: &DataflowFacts) -> Vec<bool> {
    use crate::parser::RawLiteralConst;
    use crate::transformer::BinaryOpKind;

    let count = dataflow.defs.len();
    let size = count + dataflow.phi_candidates.len();
    let mut inert = ScalarPropagation::new(size);
    let mut numeric = ScalarPropagation::new(size);
    let index = |value: SsaValue| match value {
        SsaValue::Def(def) => Some(def.index()),
        SsaValue::Phi(phi) => Some(count + phi.index()),
        _ => None,
    };
    let number_constant = |constant: crate::transformer::ConstRef| {
        matches!(
            proto.constants.get(constant.index()),
            Some(RawLiteralConst::Integer(_) | RawLiteralConst::Number(_))
        )
    };
    for def in &dataflow.defs {
        if dataflow.reference_capture_may_be_open(def.reg, def.instr) {
            continue;
        }
        let target = def.id.index();
        let instr = &proto.instrs[def.instr.index()];
        if !low_instr_def_may_hold_gc_root(instr, def.reg)
            // 字符串常量由当前 proto 持有，额外栈槽不决定其生命周期。
            || matches!(instr, LowInstr::LoadConst(load)
                if matches!(proto.constants.get(load.value.index()), Some(RawLiteralConst::String(_))))
        {
            inert.ready.push(target);
        }
        let input = |reg| {
            (!dataflow.reference_capture_may_be_open(reg, def.instr))
                .then(|| index(dataflow.use_value(def.instr, reg)))
                .flatten()
        };
        if let LowInstr::Move(copy) = instr {
            if let Some(source) = input(copy.src) {
                inert.depends_on(target, &[source]);
                numeric.depends_on(target, &[source]);
            }
            continue;
        }
        // 这里只补充尚未树化的 LENGTH 数值链。字面量自身的 GC-inert 仍由
        // 原 classifier 发布；数值链由 LENGTH 启动，不推导常量算术或 phi 的数值类型。
        let number = matches!(instr, LowInstr::UnaryOp(unary) if unary.op == UnaryOpKind::Length);
        if number {
            numeric.ready.push(target);
        } else if let LowInstr::UnaryOp(unary) = instr
            && unary.op == UnaryOpKind::Neg
            && let Some(source) = input(unary.src)
        {
            numeric.depends_on(target, &[source]);
        } else if let LowInstr::BinaryOp(binary) = instr
            && matches!(
                binary.op,
                BinaryOpKind::Add
                    | BinaryOpKind::Sub
                    | BinaryOpKind::Mul
                    | BinaryOpKind::Div
                    | BinaryOpKind::FloorDiv
                    | BinaryOpKind::Mod
                    | BinaryOpKind::Pow
            )
        {
            // 只有两个操作数都已证明为 number 才排除元方法结果；nil/Boolean 的
            // GC-inert 事实不能充当数值证明，字符串与 bitwise 转换也不在此域中。
            let operand = |value| match value {
                ValueOperand::Reg(reg) => input(reg).map(Some),
                ValueOperand::Integer(_) => Some(None),
                ValueOperand::Const(constant) if number_constant(constant) => Some(None),
                _ => None,
            };
            if let Some(inputs) = [binary.lhs, binary.rhs]
                .into_iter()
                .map(operand)
                .collect::<Option<Vec<_>>>()
            {
                let inputs = inputs.into_iter().flatten().collect::<Vec<_>>();
                if !inputs.is_empty() {
                    numeric.depends_on(target, &inputs);
                }
            }
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
        inert.depends_on(target, &inputs);
    }
    inert.ready.extend(
        numeric
            .finish()
            .into_iter()
            .enumerate()
            .filter_map(|(index, number)| number.then_some(index)),
    );
    inert.finish()
}

/// 每条依赖边只消费一次；环没有外部完整证明时保持未知。
struct ScalarPropagation {
    pending: Vec<usize>,
    users: Vec<Vec<usize>>,
    ready: Vec<usize>,
}

impl ScalarPropagation {
    fn new(size: usize) -> Self {
        Self {
            pending: vec![usize::MAX; size],
            users: vec![Vec::new(); size],
            ready: Vec::new(),
        }
    }

    fn depends_on(&mut self, target: usize, inputs: &[usize]) {
        self.pending[target] = inputs.len();
        if inputs.is_empty() {
            self.ready.push(target);
        }
        for &input in inputs {
            self.users[input].push(target);
        }
    }

    fn finish(mut self) -> Vec<bool> {
        let mut known = vec![false; self.pending.len()];
        while let Some(value) = self.ready.pop() {
            if std::mem::replace(&mut known[value], true) {
                continue;
            }
            for &user in &self.users[value] {
                self.pending[user] -= 1;
                if self.pending[user] == 0 {
                    self.ready.push(user);
                }
            }
        }
        known
    }
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
