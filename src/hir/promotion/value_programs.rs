//! 从原标量指令和决策边界保存封闭表达式帧，连接参数版本、结果和内部控制关系。
//!
//! 冻结有界的标量与字段谓词区间；后层必须匹配当前 HIR 并重放完整参数准备，不能删除原检查或字段观察。

use super::*;
use crate::transformer::{BranchPredicate, BranchSubject, CondOperand, ValuePack};

/// 目标内联成本限制之外的扫描上界；不为每个候选复制整个决策子图。
const MAX_OPERATIONS: usize = 128;
pub(in crate::hir) mod parameter_writebacks;
pub(in crate::hir) mod seeded_predicates;
// 候选拒绝[ResourceLimit]：键比较限制单个字面量字节数，避免重复长字符串造成乘积扫描。
const MAX_LITERAL_BYTES: usize = 256;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::hir) enum Literal {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(u64),
    String(crate::LuaString),
}

impl Literal {
    pub(in crate::hir) fn from_expr(value: &HirExpr) -> Option<Self> {
        Some(match value {
            HirExpr::Nil => Self::Nil,
            HirExpr::Boolean(value) => Self::Boolean(*value),
            HirExpr::Integer(value) => Self::Integer(*value),
            HirExpr::Number(value) => Self::Number(value.to_bits()),
            HirExpr::String(value) if value.as_bytes().len() <= MAX_LITERAL_BYTES => {
                Self::String(value.clone())
            }
            _ => return None,
        })
    }
}

/// 寄存器另存为有序输入，索引键只包含原操作、常量和相对控制边。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::hir) enum Predicate {
    Truthy,
    Eq,
    Lt,
    Le,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::hir) enum Operation {
    Copy,
    Load(Literal),
    Field(crate::LuaString),
    Branch {
        predicate: Predicate,
        negated: bool,
        operands: Vec<Option<Literal>>,
        truthy: usize,
        falsy: usize,
    },
    Jump(usize),
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Program {
    pub shape: Vec<Operation>,
    pub registers: Vec<Vec<Reg>>,
    reads: Vec<Vec<Reg>>,
    writes: BTreeSet<Reg>,
}

impl Program {
    /// 完整操作形状相同后才解寄存器映射；一个模板寄存器不能在不同路径映射到不同槽。
    pub fn register_mapping(&self, actual: &Self) -> Option<BTreeMap<Reg, Reg>> {
        if self.shape != actual.shape {
            return None;
        }
        let mut mapping = BTreeMap::new();
        for (expected, actual) in self.registers.iter().zip(&actual.registers) {
            if expected.len() != actual.len() {
                return None;
            }
            for (&source, &target) in expected.iter().zip(actual) {
                if mapping
                    .insert(source, target)
                    .is_some_and(|old| old != target)
                {
                    return None;
                }
            }
        }
        Some(mapping)
    }
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Template {
    pub program: Program,
    pub parameters: usize,
    pub result: Reg,
}

#[derive(Debug, Clone)]
pub(in crate::hir) struct Region {
    pub program: Program,
    pub source: InstrRef,
    pub source_pc: u32,
    pub end: InstrRef,
    /// 只有原返回 COPY 的帧带此身份；普通决策程序不制造结果预写。
    pub initial: Option<TempId>,
    pub result: TempId,
    pub inputs: BTreeMap<Reg, TempId>,
    writes: Vec<(TempId, Reg)>,
}

impl Region {
    pub(super) fn valid(&self, facts: &ProtoPromotionFacts) -> bool {
        let Some(home) = facts.trusted_temp_home_slot(self.result) else {
            return false;
        };
        self.initial
            .is_none_or(|initial| facts.trusted_temp_home_slot(initial) == Some(home))
            && self.inputs.iter().all(|(reg, temp)| {
                facts
                    .trusted_temp_home_slot(*temp)
                    .is_some_and(|home| home.slot() == reg.index())
            })
            && self.writes.iter().all(|(temp, reg)| {
                facts
                    .trusted_temp_home_slot(*temp)
                    .is_some_and(|home| home.slot() == reg.index())
            })
    }
}

#[derive(Debug, Clone, Default)]
pub(in crate::hir) struct Facts {
    pub template: Option<Template>,
    pub regions: BTreeMap<TempId, Region>,
    pub parameter_writebacks: parameter_writebacks::Facts,
    pub seeded_predicates: seeded_predicates::Facts,
}

fn operand(
    proto: &LoweredProto,
    value: CondOperand,
    registers: &mut Vec<Reg>,
) -> Option<Option<Literal>> {
    use crate::parser::RawLiteralConst;
    Some(Some(match value {
        CondOperand::Reg(reg) => {
            registers.push(reg);
            return Some(None);
        }
        CondOperand::Nil => Literal::Nil,
        CondOperand::Boolean(value) => Literal::Boolean(value),
        CondOperand::Integer(value) => Literal::Integer(value),
        CondOperand::Number(value) => Literal::Number(value.0),
        CondOperand::Const(key) => match &proto.constants[key.index()] {
            RawLiteralConst::Nil => Literal::Nil,
            RawLiteralConst::Boolean(value) => Literal::Boolean(*value),
            RawLiteralConst::Integer(value) => Literal::Integer(*value),
            RawLiteralConst::Number(value) => Literal::Number(value.to_bits()),
            RawLiteralConst::String(value) if value.bytes.len() <= MAX_LITERAL_BYTES => {
                Literal::String(crate::LuaString::from_raw(value))
            }
            _ => return None,
        },
    }))
}

fn program(
    proto: &LoweredProto,
    start: InstrRef,
    end: InstrRef,
    returned: Option<Reg>,
) -> Option<Program> {
    let count = end.index().checked_sub(start.index())?;
    // 候选拒绝[ResourceLimit]：每个原决策结果至多扫描固定上界，避免嵌套区间造成平方复制。
    if count == 0 || count > MAX_OPERATIONS {
        return None;
    }
    let target = |site: InstrRef| {
        let offset = site.index().checked_sub(start.index())?;
        (offset <= count).then_some(offset)
    };
    let mut result = Program {
        shape: Vec::new(),
        registers: Vec::new(),
        reads: Vec::new(),
        writes: BTreeSet::new(),
    };
    for (offset, instr) in proto
        .instrs
        .get(start.index()..end.index())?
        .iter()
        .enumerate()
    {
        let mut registers = Vec::new();
        let mut reads = Vec::new();
        let operation = match instr {
            LowInstr::Move(copy) => {
                registers.extend([copy.dst, copy.src]);
                reads.push(copy.src);
                result.writes.insert(copy.dst);
                Operation::Copy
            }
            LowInstr::GetTable(read) if read.kind == crate::transformer::GetTableKind::Normal => {
                let crate::transformer::AccessBase::Reg(base) = read.base else {
                    return None;
                };
                let crate::transformer::AccessKey::Const(key) = read.key else {
                    return None;
                };
                let crate::parser::RawLiteralConst::String(key) = &proto.constants[key.index()]
                else {
                    return None;
                };
                if key.bytes.len() > MAX_LITERAL_BYTES {
                    return None;
                }
                registers.extend([read.dst, base]);
                reads.push(base);
                result.writes.insert(read.dst);
                Operation::Field(crate::LuaString::from_raw(key))
            }
            LowInstr::Return(ret) if returned.is_some() => {
                // 只供已证明 Boolean 结果槽的内联模板使用；原返回值不再求值，
                // O2 将各出口转向同一次最终 COPY，不能用于一般返回包。
                if !matches!(ret.values, ValuePack::Fixed(pack)
                    if pack.len == 1 && Some(pack.start) == returned)
                {
                    return None;
                }
                Operation::Jump(count)
            }
            LowInstr::Branch(branch) => {
                let (predicate, operands) = match branch.cond.subject {
                    BranchSubject::Truthy(value) => (
                        Predicate::Truthy,
                        vec![operand(proto, value, &mut registers)?],
                    ),
                    BranchSubject::Compare {
                        predicate,
                        lhs,
                        rhs,
                    } => (
                        match predicate {
                            BranchPredicate::Eq => Predicate::Eq,
                            BranchPredicate::Lt => Predicate::Lt,
                            BranchPredicate::Le => Predicate::Le,
                        },
                        vec![
                            operand(proto, lhs, &mut registers)?,
                            operand(proto, rhs, &mut registers)?,
                        ],
                    ),
                };
                reads.clone_from(&registers);
                let truthy = target(branch.then_target)?;
                let falsy = target(branch.else_target)?;
                // 候选拒绝[LayerBoundary]：回边与状态更新属于循环帧，不属于封闭表达式。
                if truthy <= offset || falsy <= offset {
                    return None;
                }
                Operation::Branch {
                    predicate,
                    negated: branch.cond.negated,
                    operands,
                    truthy,
                    falsy,
                }
            }
            LowInstr::Jump(jump) => {
                let target = target(jump.target)?;
                if target <= offset {
                    return None;
                }
                Operation::Jump(target)
            }
            instr => {
                let (reg, value) = copy_assignments::scalar_literal(proto, instr)?;
                registers.push(reg);
                result.writes.insert(reg);
                Operation::Load(Literal::from_expr(&value)?)
            }
        };
        result.shape.push(operation);
        result.registers.push(registers);
        result.reads.push(reads);
    }
    Some(result)
}

pub(super) fn collect(
    proto: &LoweredProto,
    cfg: &Cfg,
    dataflow: &DataflowFacts,
    plan: &StructurePlan,
    fixed: &[TempId],
    phis: &[TempId],
    copies: &BTreeMap<TempId, TempId>,
) -> Facts {
    let template = (|| {
        let parameters = usize::from(proto.signature.num_params);
        if !(2..=4).contains(&parameters)
            || proto.signature.is_vararg
            || proto.upvalue_count != 0
            || !proto.children.is_empty()
        {
            return None;
        }
        let (LowInstr::Return(ret), body) = proto.instrs.split_last()? else {
            return None;
        };
        let ValuePack::Fixed(pack) = ret.values else {
            return None;
        };
        if pack.len != 1 || pack.start.index() != parameters {
            return None;
        }
        let program = program(proto, InstrRef(0), InstrRef(body.len()), None)?;
        if program.writes.iter().any(|reg| reg.index() < parameters) {
            return None;
        }
        let inputs = program
            .reads
            .iter()
            .flatten()
            .copied()
            .filter(|reg| !program.writes.contains(reg))
            .collect::<BTreeSet<_>>();
        if !inputs.iter().copied().eq((0..parameters).map(Reg)) {
            return None;
        }
        Some(Template {
            program,
            parameters,
            result: pack.start,
        })
    })();
    let mut ends = BTreeMap::new();
    for (_, decision) in plan.value_decisions() {
        ends.insert(
            phis[decision.result_phi.index()],
            cfg.blocks[decision.merge.index()].instrs.start,
        );
        for operand in &decision.operands {
            ends.insert(
                phis[operand.phi.index()],
                decision.nodes[operand.continuation.index()].predicate,
            );
        }
    }
    let collector = Collector {
        proto,
        cfg,
        dataflow,
        fixed,
        phis,
    };
    let mut regions = BTreeMap::new();
    for (&result, &initial) in copies {
        let candidate = (|| {
            let def = dataflow.defs.get(initial.index())?;
            if fixed[def.id.index()] != initial {
                return None;
            }
            let source = def.instr;
            let end = *ends.get(&result)?;
            collector.region(source, end, Some(initial), result)
        })();
        if let Some(region) = candidate {
            regions.insert(result, region);
        }
    }
    for (_, decision) in plan.value_decisions() {
        let result = phis[decision.result_phi.index()];
        if regions.contains_key(&result) {
            continue;
        }
        let candidate = (|| {
            let predicate = decision.nodes[decision.entry.index()].predicate;
            let end = cfg.blocks[decision.merge.index()].instrs.start;
            let header = cfg.blocks[decision.header()?.index()].instrs.start;
            let mut source = predicate;
            // 决策前的纯准备与第一谓词位于同一原基本块；遇到 CONCAT 等效果即停止。
            // 有界后缀保留全部操作，不能挑着略过不匹配的原指令。
            while source > header {
                if end.index().checked_sub(source.index())? >= MAX_OPERATIONS {
                    return None;
                }
                let prior = InstrRef(source.index() - 1);
                if !matches!(proto.instrs[prior.index()], LowInstr::Move(_))
                    && copy_assignments::scalar_literal(proto, &proto.instrs[prior.index()])
                        .is_none()
                {
                    break;
                }
                source = prior;
            }
            collector.region(source, end, None, result)
        })();
        if let Some(region) = candidate {
            regions.insert(result, region);
        }
    }
    let parameter_writebacks = parameter_writebacks::collect(&collector);
    Facts {
        template,
        regions,
        parameter_writebacks,
        seeded_predicates: seeded_predicates::collect(&collector),
    }
}

struct Collector<'a> {
    proto: &'a LoweredProto,
    cfg: &'a Cfg,
    dataflow: &'a DataflowFacts,
    fixed: &'a [TempId],
    phis: &'a [TempId],
}

impl Collector<'_> {
    fn region(
        &self,
        source: InstrRef,
        end: InstrRef,
        initial: Option<TempId>,
        result: TempId,
    ) -> Option<Region> {
        let program = program(self.proto, source, end, None)?;
        let mut inputs = BTreeMap::new();
        let mut writes = Vec::new();
        let mut internal = Vec::new();
        for (offset, reads) in program.reads.iter().enumerate() {
            let site = InstrRef(source.index() + offset);
            for &reg in reads {
                let input = self.dataflow.use_value(site, reg);
                if program.writes.contains(&reg) {
                    if initial.is_none() {
                        internal.push(input);
                    }
                } else {
                    let value =
                        canonical_value_temp(input, self.fixed.len(), self.fixed, self.phis)?;
                    if inputs.insert(reg, value).is_some_and(|old| old != value) {
                        return None;
                    }
                }
            }
            for &def in &self.dataflow.instr_defs[site.index()] {
                let value = canonical_value_temp(
                    SsaValue::Def(def),
                    self.fixed.len(),
                    self.fixed,
                    self.phis,
                )?;
                writes.push((value, self.dataflow.def_reg(def)));
            }
        }
        let mut visited = BTreeSet::new();
        let mut budget = MAX_OPERATIONS * 4;
        while let Some(value) = internal.pop() {
            if !visited.insert(value) {
                continue;
            }
            budget = budget.checked_sub(1)?;
            match value {
                SsaValue::Def(def) if (source..end).contains(&self.dataflow.def_instr(def)) => {}
                SsaValue::Phi(phi) => {
                    let phi = self.dataflow.phi_candidate(phi)?;
                    if !(source..end).contains(&self.cfg.blocks[phi.block.index()].instrs.start)
                        || phi.incoming.len() > budget
                    {
                        return None;
                    }
                    internal.extend(phi.incoming.iter().map(|input| input.value));
                }
                // 候选拒绝[ProofIncomplete:ProgramInput]：写过该槽不等于每条路径都已定义。
                // 有区间外旧值流入 scratch 时不把它漏记为纯内部状态。
                _ => return None,
            }
        }
        Some(Region {
            program,
            source,
            source_pc: *self.proto.lowering_map.pc_map()[source.index()].first()?,
            end,
            initial,
            result,
            inputs,
            writes,
        })
    }
}
