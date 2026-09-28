//! 将 Transformer 冻结的指令语义投影为寄存器读写与副作用摘要。
//!
//! 为 SSA 和移动安全性分析发布调用及观察期间的根边界，不识别源码控制结构。

use super::*;
use crate::structure::StructureError;

pub(super) fn compute_reg_count(
    proto: &LoweredProto,
    instr_effects: &[InstrEffect],
) -> Result<usize, StructureError> {
    let mut max_reg = proto.frame.max_stack_size as usize;

    for effect in instr_effects {
        if let Some(reg) = effect.max_fixed_reg() {
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
            if instr.normalizes_controls {
                // 读取仍是 FORPREP 之前的输入；正常后态的新数值版本结束旧 COPY 根，
                // 不把可收集输入错误延续到整个循环与后继覆盖点。
                fixed_must_defs.extend([instr.limit, instr.step]);
            }
            // `binding` 是循环可见变量槽位；在 CFG 模型下 NumericForInit 直接跳
            // 向循环体入口（body_target），此时体内首次读取 binding 前，它已经
            // 被 FORLOOP/FORI 写入。如果不把 binding 计入 must-def，则体外对该
            // 寄存器的值会经过 phi 合流进入循环体，制造出虚假的 exit phi，把
            // 纯粹的体内作用域寄存器误判为循环承载变量（见 luajit_01 回归）。
            // 该逻辑 Def 不保证 skip 边写入；物理根/残值消费者另查 normalizes_slot。
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
            // 退出边可能保留用户写入的对象；此处只定义下一次body所读的逻辑版本。
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
    frame_size: usize,
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
        // 比较即使不写 Boolean 结果，也可能通过 __eq/__lt/__le 观察原 frame；
        // truthiness 没有这类事件，此处也尚无操作数值域可排除元方法。
        LowInstr::Branch(branch)
            if matches!(branch.cond.subject, BranchSubject::Compare { .. }) =>
        {
            // 比较分支只有控制结果，没有写回值，但 __eq/__lt/__le 仍可执行用户代码。
            // 当前尚无 operand 值域；LuaJIT cdata 与 false 的比较也不能按 primitive 判纯。
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
        LowInstr::Close(close) => RootObservation::Close { from: close.from },
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
        // 普通索引和算术的 metamethod frame 建在当前函数 frame 末尾之上。
        // PUC Protect/常规 top、LuaJIT mmcall、Luau callTMres 均保留整个 frame；
        // 不能仅用显式操作数下界丢失未读取的旧槽。分配、CONCAT、调用及 TBC
        // 有各自的 top 收缩协议，仍走其专属边界或下面的保守下界。
        LowInstr::GetTable(_)
        | LowInstr::SetTable(_)
        | LowInstr::BinaryOp(_)
        | LowInstr::UnaryOp(_)
        | LowInstr::Branch(_)
            if summary.may_observe_gc_roots() =>
        {
            RootObservation::PrefixLowerBound { end: frame_size }
        }
        _ if summary.may_observe_gc_roots() => RootObservation::PrefixLowerBound {
            end: effect
                .max_fixed_reg()
                .map(|reg| reg.index().saturating_add(1))
                .into_iter()
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
