//! 保存 Boolean 初始化、字段谓词及共同返回的原程序。
//! 模板的返回边规范为内联出口，caller 的全部写入和最终 COPY 仍按 SSA 分别核对。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct Body {
    pub program: Program,
    pub parameter: Reg,
    pub result: Reg,
    pub scratch: Reg,
    pub initial: bool,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Frame {
    pub region: Region,
    pub body: Body,
    pub seed: TempId,
    pub input: TempId,
    pub output: TempId,
    pub output_home: Reg,
}

impl Frame {
    pub(in crate::hir::promotion) fn valid(&self, facts: &ProtoPromotionFacts) -> bool {
        self.region.valid(facts)
            && self
                .region
                .writes
                .iter()
                .all(|(value, _)| facts.temp_definition_reference_unaliased(*value))
            && facts.temp_definition_reference_unaliased(self.region.result)
            && facts.trusted_temp_home_slot(self.seed)
                == Some(HomeSlotKey::new(self.body.result.index(), 0))
            && facts.trusted_temp_home_slot(self.output)
                == Some(HomeSlotKey::new(self.output_home.index(), 0))
            && facts.temp_definition_reference_unaliased(self.input)
    }
}

#[derive(Debug, Clone, Default)]
pub(in crate::hir) struct Facts {
    pub body: Option<Body>,
    pub frames: Vec<Frame>,
}

fn shape(program: Program) -> Option<Body> {
    let Operation::Load(Literal::Boolean(initial)) = program.shape.first()? else {
        return None;
    };
    let initial = *initial;
    let [result] = program.registers.first()?.as_slice() else {
        return None;
    };
    let result = *result;
    let mut fields = None;
    for (index, (operation, registers)) in program.shape.iter().zip(&program.registers).enumerate()
    {
        match operation {
            Operation::Load(Literal::Boolean(_)) if registers.as_slice() == [result] => {}
            Operation::Field(_) => {
                let [scratch, parameter] = registers.as_slice() else {
                    return None;
                };
                if !matches!(program.shape.get(index + 1), Some(Operation::Branch { .. }))
                    || *scratch != Reg(result.index() + 1)
                    || parameter.index() >= result.index()
                    || fields.is_some_and(|prior| prior != (*parameter, *scratch))
                {
                    return None;
                }
                fields = Some((*parameter, *scratch));
            }
            Operation::Branch {
                predicate: Predicate::Truthy,
                operands,
                truthy,
                falsy,
                ..
            } if index > 0
                && matches!(program.shape[index - 1], Operation::Field(_))
                && operands.as_slice() == [None]
                && registers.as_slice() == [Reg(result.index() + 1)]
                && !matches!(program.shape.get(*truthy), Some(Operation::Branch { .. }))
                && !matches!(program.shape.get(*falsy), Some(Operation::Branch { .. })) => {}
            Operation::Jump(target)
                if !matches!(program.shape.get(*target), Some(Operation::Branch { .. })) => {}
            _ => return None,
        }
    }
    let (parameter, scratch) = fields?;
    Some(Body {
        program,
        parameter,
        result,
        scratch,
        initial,
    })
}

pub(super) fn collect(collector: &Collector<'_>) -> Facts {
    let proto = collector.proto;
    let body = (|| {
        if proto.signature.num_params != 1
            || proto.signature.is_vararg
            || proto.upvalue_count != 0
            || !proto.children.is_empty()
        {
            return None;
        }
        let LowInstr::Return(ret) = proto.instrs.last()? else {
            return None;
        };
        if !matches!(ret.values, ValuePack::Fixed(pack) if pack.start == Reg(1) && pack.len == 1) {
            return None;
        }
        let body = shape(program(
            proto,
            InstrRef(0),
            InstrRef(proto.instrs.len() - 1),
            Some(Reg(1)),
        )?)?;
        (body.parameter == Reg(0) && body.result == Reg(1)).then_some(body)
    })();
    let mut frames = Vec::new();
    for (index, instr) in proto.instrs.iter().enumerate() {
        let Some((result_home, HirExpr::Boolean(_))) =
            copy_assignments::scalar_literal(proto, instr)
        else {
            continue;
        };
        // 候选拒绝[ResourceLimit]：每个初始化只检查固定上界；不为每个 COPY 回扫任意长前缀。
        let end = proto
            .instrs
            .iter()
            .enumerate()
            .skip(index + 1)
            .take(MAX_OPERATIONS)
            .find_map(|(end, instr)| matches!(instr, LowInstr::Move(_)).then_some(end));
        let candidate = (|| {
            let end = end?;
            let LowInstr::Move(output) = &proto.instrs[end] else {
                unreachable!()
            };
            if output.src != result_home || output.dst.index() >= result_home.index() {
                return None;
            }
            let body = shape(program(proto, InstrRef(index), InstrRef(end), None)?)?;
            let result = canonical_value_temp(
                collector.dataflow.use_value(InstrRef(end), output.src),
                collector.fixed.len(),
                collector.fixed,
                collector.phis,
            )?;
            let seed = collector.fixed[collector
                .dataflow
                .instr_def_for_reg(InstrRef(index), result_home)?
                .index()];
            let returned = collector.fixed[collector
                .dataflow
                .instr_def_for_reg(InstrRef(end), output.dst)?
                .index()];
            // None 要求 region 核对每次内部读取均由区间内的定义/合流产生，
            // 不能因为结果槽曾被写过就漏掉某条路径上的旧值。
            let region = collector.region(InstrRef(index), InstrRef(end), None, result)?;
            if region.inputs.len() != 1 {
                return None;
            }
            let input = *region.inputs.get(&body.parameter)?;
            Some(Frame {
                region,
                body,
                seed,
                input,
                output: returned,
                output_home: output.dst,
            })
        })();
        frames.extend(candidate);
    }
    Facts { body, frames }
}
