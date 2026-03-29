use super::*;

pub(super) fn compute_reg_count(proto: &LoweredProto, instr_effects: &[InstrEffect]) -> usize {
    let mut max_reg = proto.frame.max_stack_size as usize;

    for effect in instr_effects {
        for reg in effect
            .fixed_uses
            .iter()
            .chain(effect.fixed_must_defs.iter())
            .chain(effect.fixed_may_defs.iter())
        {
            max_reg = max_reg.max(reg.index() + 1);
        }

        if let Some(reg) = effect.open_use {
            max_reg = max_reg.max(reg.index() + 1);
        }
        if let Some(reg) = effect.open_must_def {
            max_reg = max_reg.max(reg.index() + 1);
        }
        if let Some(reg) = effect.open_may_def {
            max_reg = max_reg.max(reg.index() + 1);
        }
    }

    max_reg
}

pub(super) fn compute_instr_effect(instr: &LowInstr) -> InstrEffect {
    let mut effect = InstrEffect::default();

    match instr {
        LowInstr::Move(instr) => {
            effect.fixed_uses.insert(instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadNil(instr) => insert_reg_range_defs(&mut effect.fixed_must_defs, instr.dst),
        LowInstr::LoadBool(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadConst(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadInteger(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::LoadNumber(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::UnaryOp(instr) => {
            effect.fixed_uses.insert(instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::BinaryOp(instr) => {
            insert_value_operand_use(&mut effect.fixed_uses, instr.lhs);
            insert_value_operand_use(&mut effect.fixed_uses, instr.rhs);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::Concat(instr) => {
            insert_reg_range_uses(&mut effect.fixed_uses, instr.src);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::GetUpvalue(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetUpvalue(instr) => {
            effect.fixed_uses.insert(instr.src);
        }
        LowInstr::GetTable(instr) => {
            insert_access_base_use(&mut effect.fixed_uses, instr.base);
            insert_access_key_use(&mut effect.fixed_uses, instr.key);
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetTable(instr) => {
            insert_access_base_use(&mut effect.fixed_uses, instr.base);
            insert_access_key_use(&mut effect.fixed_uses, instr.key);
            insert_value_operand_use(&mut effect.fixed_uses, instr.value);
        }
        LowInstr::ErrNil(instr) => {
            effect.fixed_uses.insert(instr.subject);
        }
        LowInstr::NewTable(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
        }
        LowInstr::SetList(instr) => {
            effect.fixed_uses.insert(instr.base);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.values);
        }
        LowInstr::Call(instr) => {
            effect.fixed_uses.insert(instr.callee);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.args);
            insert_result_pack_def(
                &mut effect.fixed_must_defs,
                &mut effect.open_must_def,
                instr.results,
            );
        }
        LowInstr::TailCall(instr) => {
            effect.fixed_uses.insert(instr.callee);
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.args);
        }
        LowInstr::VarArg(instr) => insert_result_pack_def(
            &mut effect.fixed_must_defs,
            &mut effect.open_must_def,
            instr.results,
        ),
        LowInstr::Return(instr) => {
            insert_value_pack_use(&mut effect.fixed_uses, &mut effect.open_use, instr.values);
        }
        LowInstr::Closure(instr) => {
            effect.fixed_must_defs.insert(instr.dst);
            for capture in &instr.captures {
                if let CaptureSource::Reg(reg) = capture.source {
                    effect.fixed_uses.insert(reg);
                }
            }
        }
        LowInstr::Close(_instr) => {}
        LowInstr::Tbc(instr) => {
            effect.fixed_uses.insert(instr.reg);
        }
        LowInstr::NumericForInit(instr) => {
            effect.fixed_uses.insert(instr.index);
            effect.fixed_uses.insert(instr.limit);
            effect.fixed_uses.insert(instr.step);
            effect.fixed_must_defs.insert(instr.index);
        }
        LowInstr::NumericForLoop(instr) => {
            effect.fixed_uses.insert(instr.index);
            effect.fixed_uses.insert(instr.limit);
            effect.fixed_uses.insert(instr.step);
            effect.fixed_must_defs.insert(instr.index);
        }
        LowInstr::GenericForCall(instr) => {
            insert_reg_range_uses(&mut effect.fixed_uses, instr.state);
            insert_result_pack_def(
                &mut effect.fixed_must_defs,
                &mut effect.open_must_def,
                instr.results,
            );
        }
        LowInstr::GenericForLoop(instr) => {
            effect.fixed_uses.insert(instr.control);
            if instr.bindings.len != 0 {
                effect.fixed_uses.insert(instr.bindings.start);
            }
        }
        LowInstr::Jump(_instr) => {}
        LowInstr::Branch(instr) => match instr.cond.operands {
            BranchOperands::Unary(operand) => {
                insert_cond_operand_use(&mut effect.fixed_uses, operand)
            }
            BranchOperands::Binary(lhs, rhs) => {
                insert_cond_operand_use(&mut effect.fixed_uses, lhs);
                insert_cond_operand_use(&mut effect.fixed_uses, rhs);
            }
        },
    }

    effect
}

pub(super) fn compute_side_effect_summary(instr: &LowInstr) -> SideEffectSummary {
    let mut tags = BTreeSet::new();

    match instr {
        LowInstr::GetUpvalue(_instr) => {
            tags.insert(EffectTag::ReadUpvalue);
        }
        LowInstr::SetUpvalue(_instr) => {
            tags.insert(EffectTag::WriteUpvalue);
        }
        LowInstr::GetTable(instr) => {
            tags.insert(EffectTag::ReadTable);
            match instr.base {
                AccessBase::Env => {
                    tags.insert(EffectTag::ReadEnv);
                }
                AccessBase::Upvalue(_) => {
                    tags.insert(EffectTag::ReadUpvalue);
                }
                AccessBase::Reg(_) => {}
            }
        }
        LowInstr::SetTable(instr) => {
            tags.insert(EffectTag::WriteTable);
            match instr.base {
                AccessBase::Env => {
                    tags.insert(EffectTag::WriteEnv);
                }
                AccessBase::Upvalue(_) => {
                    tags.insert(EffectTag::ReadUpvalue);
                }
                AccessBase::Reg(_) => {}
            }
        }
        LowInstr::ErrNil(_instr) => {}
        LowInstr::NewTable(_instr) => {
            tags.insert(EffectTag::Alloc);
        }
        LowInstr::Closure(_instr) => {
            tags.insert(EffectTag::Alloc);
        }
        LowInstr::SetList(_instr) => {
            tags.insert(EffectTag::WriteTable);
        }
        LowInstr::Call(_instr) => {
            tags.insert(EffectTag::Call);
        }
        LowInstr::Close(_instr) => {
            tags.insert(EffectTag::Close);
        }
        _ => {}
    }

    SideEffectSummary { tags }
}

fn insert_reg_range_uses(target: &mut BTreeSet<Reg>, range: RegRange) {
    for offset in 0..range.len {
        target.insert(Reg(range.start.index() + offset));
    }
}

fn insert_reg_range_defs(target: &mut BTreeSet<Reg>, range: RegRange) {
    for offset in 0..range.len {
        target.insert(Reg(range.start.index() + offset));
    }
}

fn insert_value_operand_use(target: &mut BTreeSet<Reg>, operand: ValueOperand) {
    match operand {
        ValueOperand::Reg(reg) => {
            target.insert(reg);
        }
        ValueOperand::Const(_) | ValueOperand::Integer(_) => {}
    }
}

fn insert_access_base_use(target: &mut BTreeSet<Reg>, base: AccessBase) {
    if let AccessBase::Reg(reg) = base {
        target.insert(reg);
    }
}

fn insert_access_key_use(target: &mut BTreeSet<Reg>, key: AccessKey) {
    match key {
        AccessKey::Reg(reg) => {
            target.insert(reg);
        }
        AccessKey::Const(_) | AccessKey::Integer(_) => {}
    }
}

fn insert_value_pack_use(
    target: &mut BTreeSet<Reg>,
    open_target: &mut Option<Reg>,
    pack: ValuePack,
) {
    match pack {
        ValuePack::Fixed(range) => insert_reg_range_uses(target, range),
        ValuePack::Open(reg) => *open_target = Some(reg),
    }
}

fn insert_result_pack_def(
    target: &mut BTreeSet<Reg>,
    open_target: &mut Option<Reg>,
    pack: ResultPack,
) {
    match pack {
        ResultPack::Fixed(range) => insert_reg_range_defs(target, range),
        ResultPack::Open(reg) => *open_target = Some(reg),
        ResultPack::Ignore => {}
    }
}

fn insert_cond_operand_use(target: &mut BTreeSet<Reg>, operand: CondOperand) {
    match operand {
        CondOperand::Reg(reg) => {
            target.insert(reg);
        }
        CondOperand::Const(_)
        | CondOperand::Nil
        | CondOperand::Boolean(_)
        | CondOperand::Integer(_)
        | CondOperand::Number(_) => {}
    }
}
