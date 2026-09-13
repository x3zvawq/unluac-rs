//! 保留原 Fresh 闭包按值捕获的标量初始化语境。
//!
//! Luau 的常量传播会删除 capture，使原 NEWCLOSURE 变为共享闭包。本 owner 消费原
//! closure/capture、SSA 与入口片段，给数值 initializer 发布独立的源码约束；它不把
//! 标量值域当作删除许可，也不伪造合成 GETVARARGS/分支的原操作来源。
//! 当前接受零固定参数入口：number 写 r0，首个 Fresh closure 写 r1。非 vararg 有限数值使用
//! 相反数的十进制字符串取负；LOADK r1 / MINUS r0 r1 不分配、不调用元方法、不检查 GC，
//! closure 写 r1 及 CAPTURE VAL 后两槽恢复原布局，随后直接返回，新增字符串不改变后缀短 K 指令。
//! 原 vararg 入口的固定首值读取和前向 truthiness 分支不检查 GC，原 vararg 区仍持有复制值。
//! 再生后的同值 phi
//! 按所有 SSA 输入求证，再原子收回整个无观察前缀，不逐分支叠加新屏障。
//! 例如原 `local n=7; return function() return n end` 保留一次数值 capture initializer，
//! HIR/AST 直到发射都不能把它替换成普通 7。ByRef、额外声明/事件不签证。

use std::collections::BTreeSet;

use super::lower::ProtoLowering;
use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirCaptureInitializer, HirCaptureMode, HirClosureCreation, HirExpr,
    HirInlineDispositions, HirInlineRetentionReason, HirLValue, HirLocalDecl, HirStmt,
    HirUnaryOpKind,
};
use crate::hir::visit::{self, HirVisitor};
use crate::structure::SsaValue;
use crate::transformer::{
    BranchSubject, CaptureSource, ClosureCreation, CondOperand, InstrRef, LowInstr, NumberLiteral,
    Reg, ResultPack, UnaryOpKind, ValuePack,
};

/// 原无观察入口与现 lowering 前缀必须在同一事务内通过；失败不改写任一节点。
pub(super) fn preserve(
    lowering: &ProtoLowering<'_>,
    body: &mut HirBlock,
    dispositions: &mut HirInlineDispositions,
) {
    let Some(proof) = prove_entry(lowering) else {
        return;
    };
    let expected = super::exprs::lower_closure_capture(
        lowering,
        lowering.cfg.instr_to_block[proof.closure.index()],
        proof.closure,
        Reg(1),
        CaptureSource::ByValue(Reg(0)),
    );
    let Ok(expected) = expected else {
        return;
    };
    if expected.mode != HirCaptureMode::ByValue {
        return;
    }
    let binding = expected.binding;
    if !matches!(binding, HirBinding::Temp(_) | HirBinding::Local(_)) {
        return;
    }

    let Some(end) = body.stmts.iter().position(|stmt| {
        let value = match stmt {
            HirStmt::Assign(assign) if assign.targets.len() == 1 => single_value(&assign.values),
            HirStmt::LocalDecl(decl) if decl.bindings.len() == 1 => single_value(&decl.values),
            HirStmt::Return(ret) => single_value(&ret.values),
            _ => None,
        };
        matches!(value, Some(HirExpr::Closure(closure))
            if closure.creation == Some(HirClosureCreation::Fresh)
            && closure.proto == proof.child
            && closure.captures.as_slice() == [expected])
    }) else {
        return;
    };
    if end == 0 {
        return;
    }

    let mut prefix = Prefix {
        allowed: &proof.bindings,
        capture: binding,
        writes: BTreeSet::new(),
        valid: true,
    };
    visit::visit_stmts(&body.stmts[..end], &mut prefix);
    // 候选拒绝[ProofIncomplete]：额外声明/事件会改变源码首槽，不能仅靠原 r0 猜布局。
    if !prefix.valid || !prefix.writes.contains(&binding) {
        return;
    }
    prefix.writes.remove(&binding);
    let mut remaining = RemainingReads {
        removed: &prefix.writes,
        found: false,
    };
    visit::visit_stmts(&body.stmts[end..], &mut remaining);
    // 候选拒绝[SemanticBarrier:Lifetime]：只消费整段内部临时值，不删除后缀仍读取的快照。
    if remaining.found {
        return;
    }

    let value = HirExpr::CaptureInitializer(proof.initializer);
    let initializer = match binding {
        HirBinding::Temp(temp) => {
            dispositions.preserve_temp(temp, HirInlineRetentionReason::SharedClosureIdentity);
            super::helpers::assign_stmt(vec![HirLValue::Temp(temp)], vec![value])
        }
        HirBinding::Local(local) => {
            dispositions.preserve_local(local, HirInlineRetentionReason::SharedClosureIdentity);
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: vec![value].into(),
                initializer_merge_transaction: None,
            }))
        }
        _ => unreachable!("capture binding checked before transaction"),
    };
    body.stmts.splice(..end, [initializer]);
}

struct EntryProof {
    closure: InstrRef,
    child: crate::hir::HirProtoRef,
    initializer: HirCaptureInitializer,
    bindings: BTreeSet<HirBinding>,
}

fn prove_entry(lowering: &ProtoLowering<'_>) -> Option<EntryProof> {
    let proto = lowering.proto;
    // 候选拒绝[ProofIncomplete]：当前只证明零固定参数入口的无分配、同槽初始化。
    if lowering.target != DecompileDialect::Luau
        || proto.signature.num_params != 0
        || proto.frame.max_stack_size < 2
        || !lowering.shared_closure_locals.is_empty()
    {
        return None;
    }
    let (index, closure) = proto.instrs.iter().enumerate().find_map(|(i, instr)| {
        if let LowInstr::Closure(closure) = instr {
            Some((i, closure))
        } else {
            None
        }
    })?;
    if index == 0
        || closure.dst != Reg(1)
        || closure.creation != ClosureCreation::Fresh
        || closure.captures.len() != 1
        || closure.captures[0].source != CaptureSource::ByValue(Reg(0))
    {
        return None;
    }
    let site = InstrRef(index);
    let number = captured_number(lowering, lowering.dataflow.use_value(site, Reg(0)))?;
    let initializer = if proto.signature.is_vararg {
        HirCaptureInitializer::FirstVararg(number)
    } else {
        // 候选拒绝[ProofIncomplete]：只证明有限值及直接返回；新增字符串不能改变后缀短 K 布局。
        if !number.to_f64().is_finite()
            || !matches!(&proto.instrs[index + 1..], [LowInstr::Return(ret)]
                if matches!(ret.values, ValuePack::Fixed(range) if range.start == Reg(1) && range.len == 1))
        {
            return None;
        }
        HirCaptureInitializer::NegatedNumericString(number)
    };
    let mut bindings = BTreeSet::new();
    for (i, instr) in proto.instrs[..index].iter().enumerate() {
        let forward = |target: InstrRef| target.index() > i && target.index() <= index;
        match instr {
            LowInstr::LoadNumber(load)
                if load.dst == Reg(0) && NumberLiteral::from_f64(load.value) == number => {}
            LowInstr::LoadInteger(load)
                if load.dst == Reg(0) && NumberLiteral::from_f64(load.value as f64) == number => {}
            LowInstr::LoadConst(load)
                if load.dst == Reg(0)
                    && matches!(proto.constants.get(load.value.index()),
                    Some(crate::parser::RawLiteralConst::Number(value))
                    if NumberLiteral::from_f64(*value) == number) => {}
            LowInstr::LoadConst(load)
                if load.dst == Reg(1) && numeric_string(lowering, load.value).is_some() => {}
            LowInstr::UnaryOp(unary)
                if unary.dst == Reg(0)
                    && unary.src == Reg(1)
                    && unary.op == UnaryOpKind::Neg
                    && negated_string(lowering, InstrRef(i)) == Some(number) => {}
            LowInstr::VarArg(vararg)
                if proto.signature.is_vararg
                    && matches!(vararg.results,
                ResultPack::Fixed(range) if range.start == Reg(1) && range.len == 1) => {}
            LowInstr::Branch(branch)
                if matches!(
                    branch.cond.subject,
                    BranchSubject::Truthy(CondOperand::Reg(Reg(1)))
                ) && forward(branch.then_target)
                    && forward(branch.else_target) => {}
            LowInstr::Jump(jump) if forward(jump.target) => {}
            _ => return None,
        }
        for &def in &lowering.dataflow.instr_defs[i] {
            bindings.insert(HirBinding::Temp(lowering.bindings.fixed_temps[def.index()]));
        }
    }
    // 原进入片段不允许从后缀回跳；否则入口与循环激活的声明窗口不是同一协议。
    for instr in &proto.instrs[index..] {
        let enters = |target: InstrRef| target.index() < index;
        match instr {
            LowInstr::Jump(jump) if enters(jump.target) => return None,
            LowInstr::Branch(branch)
                if enters(branch.then_target) || enters(branch.else_target) =>
            {
                return None;
            }
            _ => {}
        }
    }
    for phi in &lowering.dataflow.phi_candidates {
        if lowering.cfg.blocks[phi.block.index()].instrs.start.index() <= index {
            bindings.insert(HirBinding::Temp(
                lowering.bindings.phi_temps[phi.id.index()],
            ));
        }
    }
    Some(EntryProof {
        closure: site,
        child: lowering.child_refs[closure.proto.index()],
        initializer,
        bindings,
    })
}

fn captured_number(lowering: &ProtoLowering<'_>, value: SsaValue) -> Option<NumberLiteral> {
    let mut pending = vec![value];
    let mut visited = BTreeSet::new();
    let mut result = None;
    while let Some(value) = pending.pop() {
        if !visited.insert(value) {
            continue;
        }
        match value {
            SsaValue::Def(def) => {
                if lowering.dataflow.def_reg(def) != Reg(0) {
                    return None;
                }
                let number = match &lowering.proto.instrs[lowering.dataflow.def_instr(def).index()]
                {
                    LowInstr::LoadNumber(load) => load.value,
                    LowInstr::LoadInteger(load) => load.value as f64,
                    LowInstr::LoadConst(load) => {
                        match lowering.proto.constants.get(load.value.index()) {
                            Some(crate::parser::RawLiteralConst::Number(value)) => *value,
                            _ => return None,
                        }
                    }
                    LowInstr::UnaryOp(unary)
                        if unary.op == UnaryOpKind::Neg && unary.src == Reg(1) =>
                    {
                        negated_string(lowering, lowering.dataflow.def_instr(def))?.to_f64()
                    }
                    _ => return None,
                };
                let number = NumberLiteral::from_f64(number);
                if result.is_some_and(|previous| previous != number) {
                    return None;
                }
                result = Some(number);
            }
            SsaValue::Phi(phi) => {
                let phi = &lowering.dataflow.phi_candidates[phi.index()];
                if phi.reg != Reg(0) || phi.incoming.is_empty() {
                    return None;
                }
                pending.extend(phi.incoming.iter().map(|incoming| incoming.value));
            }
            _ => return None,
        }
    }
    result
}

fn numeric_string(
    lowering: &ProtoLowering<'_>,
    constant: crate::transformer::ConstRef,
) -> Option<f64> {
    let crate::parser::RawLiteralConst::String(value) =
        lowering.proto.constants.get(constant.index())?
    else {
        return None;
    };
    let text = std::str::from_utf8(&value.bytes).ok()?;
    // 只接受 Rust 与 Luau 都按十进制解析的有限数值，不扩展到 NaN、inf 或宿主 locale。
    if !text
        .bytes()
        .all(|byte| byte.is_ascii_digit() || b"+-.eE".contains(&byte))
    {
        return None;
    }
    let number = text.parse::<f64>().ok()?;
    number.is_finite().then_some(number)
}

fn negated_string(lowering: &ProtoLowering<'_>, site: InstrRef) -> Option<NumberLiteral> {
    let SsaValue::Def(def) = lowering.dataflow.use_value(site, Reg(1)) else {
        return None;
    };
    let LowInstr::LoadConst(load) =
        &lowering.proto.instrs[lowering.dataflow.def_instr(def).index()]
    else {
        return None;
    };
    Some(NumberLiteral::from_f64(-numeric_string(
        lowering, load.value,
    )?))
}

struct Prefix<'a> {
    allowed: &'a BTreeSet<HirBinding>,
    capture: HirBinding,
    writes: BTreeSet<HirBinding>,
    valid: bool,
}
impl HirVisitor<'_> for Prefix<'_> {
    fn is_complete(&self) -> bool {
        !self.valid
    }
    fn visit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::Assign(assign) if assign.values.tail.is_none() => {}
            HirStmt::LocalDecl(decl)
                if decl.values.tail.is_none()
                    && decl
                        .bindings
                        .iter()
                        .all(|local| HirBinding::Local(*local) == self.capture) =>
            {
                self.writes.insert(self.capture);
            }
            HirStmt::If(_) => {}
            _ => self.valid = false,
        }
    }
    fn visit_lvalue(&mut self, target: &HirLValue) {
        let Some(binding) = HirBinding::from_lvalue(target) else {
            self.valid = false;
            return;
        };
        self.valid &= binding == self.capture || self.allowed.contains(&binding);
        self.writes.insert(binding);
    }
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.valid &= match expr {
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::VarArg
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_)
            | HirExpr::Decision(_) => true,
            HirExpr::Unary(unary) => matches!(unary.op, HirUnaryOpKind::Not | HirUnaryOpKind::Neg),
            _ => HirBinding::from_expr(expr)
                .is_some_and(|binding| binding == self.capture || self.allowed.contains(&binding)),
        };
    }
}
struct RemainingReads<'a> {
    removed: &'a BTreeSet<HirBinding>,
    found: bool,
}
impl HirVisitor<'_> for RemainingReads<'_> {
    fn is_complete(&self) -> bool {
        self.found
    }
    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |=
            HirBinding::from_expr(expr).is_some_and(|binding| self.removed.contains(&binding));
    }
}

fn single_value(values: &crate::hir::HirValuePack) -> Option<&HirExpr> {
    match (values.fixed.as_slice(), &values.tail) {
        ([value], None) => Some(value),
        _ => None,
    }
}
