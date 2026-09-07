//! low-IR 指令的寄存器读写与副作用摘要。
//!
//! 这里把 Transformer 已冻结的单条指令语义投影成 canonical SSA 和后续移动安全性所需的
//! 稠密事实，并一次性冻结观察期间的 caller root 边界；例如 TFORCALL 只消费三个固定
//! 输入，未产生的 result 槽不属于其存活前缀证明。下游不能从读写集合重新解释调用协议。
//! 本层不识别控制结构，也不根据 opcode 外形猜隐式 owner。例如可能原槽转换的
//! `TypeGuard` 同时读取并定义 subject，而纯类型检查只保留读取。
//! 固定读写先顺序收集，再一次排序去重并冻结；不在逐项插入时搬移有序集合。

use super::*;
use crate::structure::StructureError;

pub(super) fn compute_reg_count(
    proto: &LoweredProto,
    instr_effects: &[InstrEffect],
) -> Result<usize, StructureError> {
    let mut max_reg = proto.frame.max_stack_size as usize;

    for effect in instr_effects {
        for reg in effect
            .fixed_uses()
            .iter()
            .chain(effect.fixed_must_defs().iter())
        {
            let Some(end) = reg.index().checked_add(1) else {
                return Err(StructureError::invalid("register index overflows usize"));
            };
            max_reg = max_reg.max(end);
        }

        if let Some(reg) = effect.open_use {
            let Some(end) = reg.index().checked_add(1) else {
                return Err(StructureError::invalid(
                    "open-use register index overflows usize",
                ));
            };
            max_reg = max_reg.max(end);
        }
        if let Some(reg) = effect.open_must_def {
            let Some(end) = reg.index().checked_add(1) else {
                return Err(StructureError::invalid(
                    "open-def register index overflows usize",
                ));
            };
            max_reg = max_reg.max(end);
        }
    }

    Ok(max_reg)
}

pub(super) fn compute_instr_effect(instr: &LowInstr) -> InstrEffect {
    let mut fixed_uses = Vec::new();
    let mut fixed_must_defs = Vec::new();
    let mut open_use = None;
    let mut open_must_def = None;

    match instr {
        LowInstr::Move(instr) => {
            fixed_uses.push(instr.src);
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::LoadNil(instr) => insert_reg_range(&mut fixed_must_defs, instr.dst),
        LowInstr::LoadBool(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::LoadConst(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::LoadInteger(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::LoadNumber(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::UnaryOp(instr) => {
            fixed_uses.push(instr.src);
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::BinaryOp(instr) => {
            insert_value_operand_use(&mut fixed_uses, instr.lhs);
            insert_value_operand_use(&mut fixed_uses, instr.rhs);
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::Concat(instr) => {
            insert_reg_range(&mut fixed_uses, instr.src);
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::GetUpvalue(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::SetUpvalue(instr) => {
            insert_value_operand_use(&mut fixed_uses, instr.src);
        }
        LowInstr::GetTable(instr) => {
            insert_access_base_use(&mut fixed_uses, instr.base);
            insert_access_key_use(&mut fixed_uses, instr.key);
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::SetTable(instr) => {
            insert_access_base_use(&mut fixed_uses, instr.base);
            insert_access_key_use(&mut fixed_uses, instr.key);
            insert_value_operand_use(&mut fixed_uses, instr.value);
        }
        LowInstr::ErrNil(instr) => {
            fixed_uses.push(instr.subject);
        }
        LowInstr::TypeGuard(instr) => {
            fixed_uses.push(instr.subject);
            if instr.kind.normalizes_subject() {
                fixed_must_defs.push(instr.subject);
            }
        }
        LowInstr::NewTable(instr) => {
            fixed_must_defs.push(instr.dst);
        }
        LowInstr::SetList(instr) => {
            fixed_uses.push(instr.base);
            insert_value_pack_use(&mut fixed_uses, &mut open_use, instr.values);
        }
        LowInstr::Call(instr) => {
            fixed_uses.push(instr.callee);
            insert_value_pack_use(&mut fixed_uses, &mut open_use, instr.args);
            insert_result_pack_def(&mut fixed_must_defs, &mut open_must_def, instr.results);
        }
        LowInstr::TailCall(instr) => {
            fixed_uses.push(instr.callee);
            insert_value_pack_use(&mut fixed_uses, &mut open_use, instr.args);
        }
        LowInstr::VarArg(instr) => {
            insert_result_pack_def(&mut fixed_must_defs, &mut open_must_def, instr.results)
        }
        LowInstr::Return(instr) => {
            insert_value_pack_use(&mut fixed_uses, &mut open_use, instr.values);
        }
        LowInstr::Closure(instr) => {
            fixed_must_defs.push(instr.dst);
            for capture in &instr.captures {
                match capture.source {
                    CaptureSource::ByValue(reg) | CaptureSource::ByReference(reg) => {
                        fixed_uses.push(reg);
                    }
                    CaptureSource::Upvalue(_) => {}
                }
            }
        }
        LowInstr::Close(_instr) => {}
        LowInstr::Tbc(instr) => {
            fixed_uses.push(instr.reg);
        }
        LowInstr::NumericForInit(instr) => {
            fixed_uses.push(instr.index);
            fixed_uses.push(instr.limit);
            fixed_uses.push(instr.step);
            fixed_must_defs.push(instr.index);
            // `binding` 是循环可见变量槽位；在 CFG 模型下 NumericForInit 直接跳
            // 向循环体入口（body_target），此时体内首次读取 binding 前，它已经
            // 被 FORLOOP/FORI 写入。如果不把 binding 计入 must-def，则体外对该
            // 寄存器的值会经过 phi 合流进入循环体，制造出虚假的 exit phi，把
            // 纯粹的体内作用域寄存器误判为循环承载变量（见 luajit_01 回归）。
            fixed_must_defs.push(instr.binding);
        }
        LowInstr::NumericForLoop(instr) => {
            fixed_uses.push(instr.index);
            fixed_uses.push(instr.limit);
            fixed_uses.push(instr.step);
            fixed_must_defs.push(instr.index);
            // FORLOOP/IFORL/JFORL 回边在迭代继续时会把新的 index 写入
            // binding，与 NumericForInit 对称，避免体内重新定义前的 phi 被错
            // 误当成真正的入口值。
            fixed_must_defs.push(instr.binding);
        }
        LowInstr::GenericForPrep(instr) => {
            // Lua 5.5 在同一条 TFORPREP 内交换 control/closing；先登记全部 use、
            // 再登记变化的 target，才能让 SSA 把它解释成并行复制而非顺序覆盖。
            fixed_uses.extend([
                instr.iterator,
                instr.state,
                instr.control_source,
                instr.closing_source,
            ]);
            if instr.control_target != instr.control_source {
                fixed_must_defs.push(instr.control_target);
            }
            if instr.closing_target != instr.closing_source {
                fixed_must_defs.push(instr.closing_target);
            }
        }
        LowInstr::GenericForCall(instr) => {
            fixed_uses.extend([instr.iterator, instr.state, instr.control]);
            insert_result_pack_def(&mut fixed_must_defs, &mut open_must_def, instr.results);
        }
        LowInstr::GenericForLoop(instr) => {
            if instr.bindings.len != 0 {
                fixed_uses.push(instr.bindings.start);
                // 5.1--5.4、LuaJIT 与 Luau 在继续迭代时把首个结果写回隐藏
                // control 槽；缺少这个 def 会让下一轮仍读取首轮 control。
                if instr.control_target != instr.bindings.start {
                    fixed_must_defs.push(instr.control_target);
                }
            }
        }
        LowInstr::Jump(_instr) => {}
        LowInstr::Branch(instr) => match instr.cond.subject {
            BranchSubject::Truthy(operand) => insert_cond_operand_use(&mut fixed_uses, operand),
            BranchSubject::Compare { lhs, rhs, .. } => {
                insert_cond_operand_use(&mut fixed_uses, lhs);
                insert_cond_operand_use(&mut fixed_uses, rhs);
            }
        },
    }

    InstrEffect::new(fixed_uses, fixed_must_defs, open_use, open_must_def)
}

pub(super) fn compute_side_effect_summary(
    instr: &LowInstr,
    effect: &InstrEffect,
) -> SideEffectSummary {
    let mut summary = SideEffectSummary::default();

    match instr {
        LowInstr::UnaryOp(instr) if instr.op != UnaryOpKind::Not => {
            summary.add_tag(EffectTag::Metamethod);
            summary.add_tag(EffectTag::MayThrow);
        }
        LowInstr::BinaryOp(_) | LowInstr::Concat(_) => {
            summary.add_tag(EffectTag::Metamethod);
            summary.add_tag(EffectTag::MayThrow);
        }
        LowInstr::GetUpvalue(_instr) => {
            summary.add_tag(EffectTag::ReadUpvalue);
        }
        LowInstr::SetUpvalue(_instr) => {
            summary.add_tag(EffectTag::WriteUpvalue);
        }
        LowInstr::GetTable(instr) => {
            summary.add_tag(EffectTag::ReadTable);
            match instr.base {
                AccessBase::Env | AccessBase::EnvironmentUpvalue(_) => {
                    summary.add_tag(EffectTag::ReadEnv);
                }
                AccessBase::Upvalue(_) => {
                    summary.add_tag(EffectTag::ReadUpvalue);
                }
                AccessBase::Reg(_) => {}
            }
        }
        LowInstr::SetTable(instr) => {
            summary.add_tag(EffectTag::WriteTable);
            match instr.base {
                AccessBase::Env | AccessBase::EnvironmentUpvalue(_) => {
                    summary.add_tag(EffectTag::WriteEnv);
                }
                AccessBase::Upvalue(_) => {
                    summary.add_tag(EffectTag::ReadUpvalue);
                }
                AccessBase::Reg(_) => {}
            }
        }
        LowInstr::ErrNil(_instr) => {
            summary.add_tag(EffectTag::MayThrow);
        }
        LowInstr::TypeGuard(_instr) => {
            summary.add_tag(EffectTag::Call);
        }
        LowInstr::NewTable(_instr) => {
            summary.add_tag(EffectTag::Alloc);
        }
        LowInstr::Closure(_instr) => {
            summary.add_tag(EffectTag::Alloc);
        }
        LowInstr::SetList(_instr) => {
            summary.add_tag(EffectTag::WriteTable);
        }
        LowInstr::Call(_) | LowInstr::GenericForCall(_) => {
            summary.add_tag(EffectTag::Call);
        }
        LowInstr::Close(_instr) => {
            summary.add_tag(EffectTag::Close);
        }
        LowInstr::Tbc(_instr) => {
            summary.add_tag(EffectTag::MayThrow);
            summary.add_tag(EffectTag::RegisterClose);
        }
        _ => {}
    }

    summary.root_observation = match instr {
        LowInstr::Return(_) | LowInstr::TailCall(_) => RootObservation::FrameExit,
        // callee base 才是跨方言共同成立的 caller-frame 边界；LuaJIT FR1/FR2
        // frame link 使 args.start 不能代替它，更不能用尚未写入的结果槽抬高边界。
        LowInstr::Call(call) => RootObservation::Call {
            caller_end: call.callee,
        },
        LowInstr::Close(_) => RootObservation::Close,
        LowInstr::Tbc(tbc) => RootObservation::PrefixLowerBound {
            end: tbc.reg.index() + 1,
        },
        LowInstr::GenericForCall(call) => RootObservation::PrefixLowerBound {
            end: [call.iterator, call.state, call.control]
                .into_iter()
                .map(|reg| reg.index() + 1)
                .max()
                .expect("iterator has three fixed inputs"),
        },
        _ if summary.may_observe_gc_roots() => RootObservation::PrefixLowerBound {
            end: effect
                .fixed_uses()
                .iter()
                .chain(effect.fixed_must_defs())
                .map(|reg| reg.index().saturating_add(1))
                .chain(effect.open_use.map(Reg::index))
                .chain(effect.open_must_def.map(Reg::index))
                .max()
                .unwrap_or_default(),
        },
        _ => RootObservation::None,
    };
    summary
}

fn insert_reg_range(target: &mut Vec<Reg>, range: RegRange) {
    target.extend((0..range.len).map(|offset| Reg(range.start.index() + offset)));
}

fn insert_value_operand_use(target: &mut Vec<Reg>, operand: ValueOperand) {
    match operand {
        ValueOperand::Reg(reg) => {
            target.push(reg);
        }
        ValueOperand::Const(_)
        | ValueOperand::Integer(_)
        | ValueOperand::Nil
        | ValueOperand::Boolean(_) => {}
    }
}

fn insert_access_base_use(target: &mut Vec<Reg>, base: AccessBase) {
    if let AccessBase::Reg(reg) = base {
        target.push(reg);
    }
}

fn insert_access_key_use(target: &mut Vec<Reg>, key: AccessKey) {
    match key {
        AccessKey::Reg(reg) => {
            target.push(reg);
        }
        AccessKey::Const(_) | AccessKey::Integer(_) => {}
    }
}

fn insert_value_pack_use(target: &mut Vec<Reg>, open_target: &mut Option<Reg>, pack: ValuePack) {
    match pack {
        ValuePack::Fixed(range) => insert_reg_range(target, range),
        ValuePack::Open(reg) => *open_target = Some(reg),
    }
}

fn insert_result_pack_def(target: &mut Vec<Reg>, open_target: &mut Option<Reg>, pack: ResultPack) {
    match pack {
        ResultPack::Fixed(range) => insert_reg_range(target, range),
        ResultPack::Open(reg) => *open_target = Some(reg),
        ResultPack::Ignore => {}
    }
}

fn insert_cond_operand_use(target: &mut Vec<Reg>, operand: CondOperand) {
    match operand {
        CondOperand::Reg(reg) => {
            target.push(reg);
        }
        CondOperand::Const(_)
        | CondOperand::Nil
        | CondOperand::Boolean(_)
        | CondOperand::Integer(_)
        | CondOperand::Number(_) => {}
    }
}
