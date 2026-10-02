//! 从封闭标量程序保存参数比较、选值及返回 COPY 的完整写回帧。
//! 固定长度窗口沿原 SSA 验证内部写和外部输入，后层仍须匹配当前树和源码前缀。

use super::*;

#[derive(Debug, Clone)]
pub(in crate::hir) struct Body {
    pub program: Program,
    pub predicate: Predicate,
    pub values: [Literal; 2],
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Frame {
    pub region: Region,
    pub body: Body,
    pub initial: TempId,
    pub initial_value: Literal,
    pub parameter_home: Reg,
    pub argument_homes: [Reg; 2],
}

#[derive(Debug, Clone, Default)]
pub(in crate::hir) struct Facts {
    pub body: Option<Body>,
    pub frames: Vec<Frame>,
}

fn shape(program: Program) -> Option<Body> {
    let (predicate, operands, hit, miss, materialized) = match program.shape.as_slice() {
        [
            Operation::Branch {
                predicate,
                negated: false,
                operands,
                truthy: 3,
                falsy: 1,
            },
            Operation::Load(Literal::Boolean(false)),
            Operation::Jump(4),
            Operation::Load(Literal::Boolean(true)),
            Operation::Branch {
                predicate: Predicate::Truthy,
                negated: true,
                operands: test,
                truthy: 7,
                falsy: 5,
            },
            Operation::Load(hit),
            Operation::Jump(8),
            Operation::Load(miss),
            Operation::Copy,
        ] if test.as_slice() == [None] => (predicate, operands, hit, miss, true),
        [
            Operation::Branch {
                predicate,
                negated: true,
                operands,
                truthy: 3,
                falsy: 1,
            },
            Operation::Load(hit),
            Operation::Jump(4),
            Operation::Load(miss),
            Operation::Copy,
        ] => (predicate, operands, hit, miss, false),
        _ => return None,
    };
    if !matches!(predicate, Predicate::Eq | Predicate::Lt | Predicate::Le)
        || operands.as_slice() != [None, None]
        || matches!(hit, Literal::Nil | Literal::Boolean(false))
    {
        return None;
    }
    let [left, right] = program.registers[0].as_slice() else {
        return None;
    };
    let [parameter, scratch] = program.registers.last()?.as_slice() else {
        return None;
    };
    if [left, right, scratch].contains(&parameter)
        || left == right
        || scratch == left
        || scratch == right
    {
        return None;
    }
    let registers = if materialized {
        vec![
            vec![*left, *right],
            vec![*parameter],
            vec![],
            vec![*parameter],
            vec![*parameter],
            vec![*scratch],
            vec![],
            vec![*scratch],
            vec![*parameter, *scratch],
        ]
    } else {
        vec![
            vec![*left, *right],
            vec![*scratch],
            vec![],
            vec![*scratch],
            vec![*parameter, *scratch],
        ]
    };
    if program.registers != registers {
        return None;
    }
    let predicate = *predicate;
    let values = [hit.clone(), miss.clone()];
    Some(Body {
        program,
        predicate,
        values,
    })
}

pub(super) fn collect(collector: &Collector<'_>) -> Facts {
    let proto = collector.proto;
    let body = (|| {
        if proto.signature.num_params != 3
            || proto.signature.is_vararg
            || proto.upvalue_count != 0
            || !proto.children.is_empty()
            || !matches!(proto.instrs.len(), 6 | 10)
        {
            return None;
        }
        let LowInstr::Return(ret) = proto.instrs.last()? else {
            return None;
        };
        if !matches!(ret.values, ValuePack::Fixed(pack) if pack.start == Reg(0) && pack.len == 1) {
            return None;
        }
        let body = shape(program(
            proto,
            InstrRef(0),
            InstrRef(proto.instrs.len() - 1),
            None,
        )?)?;
        (body.program.registers[0] == [Reg(1), Reg(2)]
            && body.program.registers.last()?.as_slice() == [Reg(0), Reg(3)])
        .then_some(body)
    })();
    let mut frames = Vec::new();
    for (index, instruction) in proto.instrs.iter().enumerate().skip(6) {
        let LowInstr::Move(output) = instruction else {
            continue;
        };
        // 每种已证明的源码形式只检查固定上界，不对任意前缀回扫。
        for width in [6, 10] {
            let candidate = (|| {
                let source = InstrRef(index.checked_sub(width)?);
                let (parameter, literal) =
                    copy_assignments::scalar_literal(proto, &proto.instrs[source.index()])?;
                let body = shape(program(
                    proto,
                    InstrRef(source.index() + 1),
                    InstrRef(index),
                    None,
                )?)?;
                let [left, right] = body.program.registers[0].as_slice() else {
                    return None;
                };
                if body.program.registers.last()?.as_slice()
                    != [parameter, Reg(parameter.index() + 1)]
                    || output.src != parameter
                    || output.dst.index() + 1 != parameter.index()
                    || left.index() >= output.dst.index()
                    || right.index() >= output.dst.index()
                {
                    return None;
                }
                let initial = collector.dataflow.instr_def_for_reg(source, parameter)?;
                let result = collector
                    .dataflow
                    .instr_def_for_reg(InstrRef(index), output.dst)?;
                let region = collector.region(
                    source,
                    InstrRef(index + 1),
                    None,
                    collector.fixed[result.index()],
                )?;
                if region.inputs.len() != 2 {
                    return None;
                }
                Some(Frame {
                    region,
                    initial: collector.fixed[initial.index()],
                    initial_value: Literal::from_expr(&literal)?,
                    parameter_home: parameter,
                    argument_homes: [*left, *right],
                    body,
                })
            })();
            frames.extend(candidate);
        }
    }
    Facts { body, frames }
}
