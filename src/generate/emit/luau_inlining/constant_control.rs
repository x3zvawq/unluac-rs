//! 验证常量控制调用的最终操作轨迹、内联成本和保留调用。
//! 成本沿 pinned Luau 的常量分支、局部传播和循环计费规则计算，饱和及阈值复用共享实现。

use super::*;
use crate::hir::luau_inlining::constant_control::{Action, Trace};
use crate::hir::luau_loop_cost::{Cost, trips};

fn truth(expr: &AstExpr, func: &AstFunctionExpr, mask: Option<u8>) -> Option<bool> {
    match expr {
        AstExpr::Boolean(value) => Some(*value),
        AstExpr::Nil => Some(false),
        AstExpr::Integer(_) | AstExpr::Number(_) | AstExpr::String(_) => Some(true),
        AstExpr::Var(AstNameRef::Param(param)) => {
            let index = func.params.iter().position(|other| other == param)?;
            (index + 1 < func.params.len())
                .then(|| mask.map(|mask| mask & (1 << index) != 0))
                .flatten()
        }
        AstExpr::Unary(unary) if unary.op == AstUnaryOpKind::Not => {
            Some(!truth(&unary.expr, func, mask)?)
        }
        AstExpr::LogicalAnd(logical) => {
            if truth(&logical.lhs, func, mask)? {
                truth(&logical.rhs, func, mask)
            } else {
                Some(false)
            }
        }
        AstExpr::LogicalOr(logical) => {
            if truth(&logical.lhs, func, mask)? {
                Some(true)
            } else {
                truth(&logical.rhs, func, mask)
            }
        }
        AstExpr::SingleValue(value) => truth(value, func, mask),
        _ => None,
    }
}

fn binary_op(op: AstBinaryOpKind) -> Option<crate::hir::HirBinaryOpKind> {
    use crate::hir::HirBinaryOpKind as H;
    Some(match op {
        AstBinaryOpKind::Add => H::Add,
        AstBinaryOpKind::Sub => H::Sub,
        AstBinaryOpKind::Mul => H::Mul,
        AstBinaryOpKind::Div => H::Div,
        AstBinaryOpKind::Mod => H::Mod,
        AstBinaryOpKind::Pow => H::Pow,
        _ => return None,
    })
}

#[derive(PartialEq)]
enum Flow {
    Next,
    Return,
    Break,
    Continue,
}

struct TraceBuilder<'a> {
    function: &'a AstFunctionExpr,
    mask: u8,
    locals: BTreeMap<AstNameRef, usize>,
    trace: Trace,
    budget: usize,
}
impl TraceBuilder<'_> {
    fn block(&mut self, block: &AstBlock, root: bool) -> Option<Flow> {
        for stmt in &block.stmts {
            self.budget = self.budget.checked_sub(1)?;
            let flow = match stmt {
                AstStmt::LocalDecl(decl) if root && decl.bindings.len() == decl.values.len() => {
                    for (binding, value) in decl.bindings.iter().zip(&decl.values) {
                        let state = self.locals.len();
                        if self
                            .locals
                            .insert(binding.id.to_name_ref(), state)
                            .is_some()
                        {
                            return None;
                        }
                        self.trace
                            .actions
                            .push(Action::Initialize(counter_repeat::integer(value)?));
                    }
                    Flow::Next
                }
                AstStmt::Assign(assign) => {
                    let ([AstLValue::Name(local)], [AstExpr::Binary(binary)]) =
                        (assign.targets.as_slice(), assign.values.as_slice())
                    else {
                        return None;
                    };
                    if binary.lhs != AstExpr::Var(local.clone()) {
                        return None;
                    }
                    self.trace.actions.push(Action::Update {
                        state: *self.locals.get(local)?,
                        op: binary_op(binary.op)?,
                        value: counter_repeat::integer(&binary.rhs)?,
                    });
                    Flow::Next
                }
                AstStmt::If(branch) => {
                    if truth(&branch.cond, self.function, Some(self.mask))? {
                        self.block(&branch.then_block, false)?
                    } else if let Some(other) = &branch.else_block {
                        self.block(other, false)?
                    } else {
                        Flow::Next
                    }
                }
                AstStmt::While(loop_) => {
                    if !truth(&loop_.cond, self.function, Some(self.mask))? {
                        Flow::Next
                    } else {
                        match self.block(&loop_.body, false)? {
                            Flow::Break => Flow::Next,
                            Flow::Return => Flow::Return,
                            _ => return None,
                        }
                    }
                }
                AstStmt::NumericFor(loop_) => {
                    let start = counter_repeat::integer(&loop_.start)?;
                    let limit = counter_repeat::integer(&loop_.limit)?;
                    let step = counter_repeat::integer(&loop_.step)?;
                    let count = trips(start, limit, step)?;
                    // 候选拒绝[TargetConstraint]：轨迹相等不足以让原数值循环消失；
                    // 最终源码的专化循环体还必须满足 pinned Luau 展开阈值。
                    if count > 25
                        || block_cost(self.function, &loop_.body, Some(self.mask))?
                            .blocks_unroll(start, limit, step)
                    {
                        return None;
                    }
                    let mut exit = Flow::Next;
                    for _ in 0..count {
                        match self.block(&loop_.body, false)? {
                            Flow::Break => break,
                            Flow::Return => {
                                exit = Flow::Return;
                                break;
                            }
                            Flow::Next | Flow::Continue => {}
                        }
                    }
                    exit
                }
                AstStmt::Repeat(loop_) => match self.block(&loop_.body, false)? {
                    Flow::Return => Flow::Return,
                    Flow::Break => Flow::Next,
                    Flow::Next | Flow::Continue
                        if truth(&loop_.cond, self.function, Some(self.mask)) == Some(true) =>
                    {
                        Flow::Next
                    }
                    _ => return None,
                },
                AstStmt::Return(ret) => {
                    self.trace.returned = ret
                        .values
                        .iter()
                        .map(|value| {
                            let AstExpr::Var(local) = value else {
                                return None;
                            };
                            self.locals.get(local).copied()
                        })
                        .collect::<Option<Vec<_>>>()?;
                    Flow::Return
                }
                AstStmt::Break => Flow::Break,
                AstStmt::Continue => Flow::Continue,
                AstStmt::DoBlock(block) => self.block(block, false)?,
                _ => return None,
            };
            if flow != Flow::Next {
                return Some(flow);
            }
        }
        Some(Flow::Next)
    }
}

struct Model<'a> {
    function: &'a AstFunctionExpr,
    mask: Option<u8>,
    locals: BTreeMap<AstNameRef, Cost>,
    budget: usize,
    written: BTreeSet<crate::hir::LocalId>,
    // 只用于循环展开的保守下界；base 仍是无实参专化的完整函数成本。
    discount_all: bool,
    stable_loops: BTreeSet<AstBindingRef>,
}
impl Model<'_> {
    fn expression(&mut self, expr: &AstExpr) -> Option<Cost> {
        self.costed(expr).map(|(cost, _)| cost)
    }

    // 成本和真正已知的常量真值在同一次后序遍历中产生；不能对每个父节点
    // 重扫整棵真值子树，也不能把 CostModel 的局部折扣当作常量折叠事实。
    fn costed(&mut self, expr: &AstExpr) -> Option<(Cost, Option<bool>)> {
        self.budget = self.budget.checked_sub(1)?;
        let cost = match expr {
            AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_) => {
                return Some((Cost::literal(), truth(expr, self.function, self.mask)));
            }
            AstExpr::Var(AstNameRef::Global(_)) => Cost::fixed(1),
            AstExpr::Var(name @ AstNameRef::Local(_)) => self
                .locals
                .get(name)
                .copied()
                .unwrap_or(Cost::variable(self.discount_all)),
            AstExpr::Var(AstNameRef::Param(_)) => {
                let known = truth(expr, self.function, self.mask);
                return Some((
                    if known.is_some() {
                        Cost::literal()
                    } else {
                        Cost::variable(self.discount_all)
                    },
                    known,
                ));
            }
            AstExpr::Unary(unary) => {
                let (cost, known) = self.costed(&unary.expr)?;
                if let Some(value) = known {
                    if unary.op == AstUnaryOpKind::Not {
                        return Some((Cost::literal(), Some(!value)));
                    }
                    // 候选拒绝[ProofIncomplete:Cost]：数值/字符串的常量运算
                    // 尚未求值，不能猜测其后续条件会保留哪个分支。
                    return None;
                }
                cost.fold(Cost::literal(), false)?
            }
            AstExpr::Binary(binary) => {
                let (left, lknown) = self.costed(&binary.lhs)?;
                let (right, rknown) = self.costed(&binary.rhs)?;
                if lknown.is_some() && rknown.is_some() {
                    return None;
                }
                left.fold(right, false)?
            }
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                let (left, known) = self.costed(&logical.lhs)?;
                let is_and = matches!(expr, AstExpr::LogicalAnd(_));
                if known == Some(!is_and) {
                    return Some((Cost::literal(), known));
                }
                let (right, rknown) = self.costed(&logical.rhs)?;
                if known.is_some() && rknown.is_some() {
                    return Some((Cost::literal(), rknown));
                }
                left.fold(right, false)?
            }
            AstExpr::IndexAccess(index) => self
                .expression(&index.base)?
                .add(self.expression(&index.index)?)
                .add(Cost::fixed(1)),
            AstExpr::FieldAccess(field) => self.expression(&field.base)?.add(Cost::fixed(1)),
            AstExpr::Call(call)
                if call.method_key.is_none()
                    && matches!(call.callee, AstExpr::Var(AstNameRef::Local(_))) =>
            {
                // 源码 CostModel 对普通 local CALL 按原始调用计费；
                // 其保留或内联义务由函数体和 occurrence 合同另行验证。
                let mut cost = Cost::fixed(3);
                for argument in &call.args {
                    cost = cost.add(self.expression(argument)?.argument());
                }
                cost
            }
            AstExpr::Call(call)
                if call.method_key.is_none()
                    && call.required_luau_inlining.is_none()
                    && matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name)) if name.text == "print") =>
            {
                let mut cost = Cost::fixed(4);
                for arg in &call.args {
                    cost = cost.add(self.expression(arg)?.argument());
                }
                cost
            }
            AstExpr::FunctionExpr(_) => Cost::fixed(10),
            AstExpr::TableConstructor(table) => {
                let mut cost = Cost::fixed(10);
                for field in &table.fields {
                    let value = match field {
                        AstTableField::Array(value) => value,
                        AstTableField::Record(record) => {
                            if let AstTableKey::Expr(key) = &record.key {
                                cost = cost.add(self.expression(key)?);
                            }
                            &record.value
                        }
                    };
                    cost = cost.add(self.expression(value)?).add(Cost::fixed(1));
                }
                cost
            }
            AstExpr::Call(call)
                if call.method_key.is_none() && call.required_luau_inlining.is_none() =>
            {
                let builtin = matches!(&call.callee, AstExpr::Var(AstNameRef::Global(name))
                    if matches!(name.text.as_str(), "assert" | "rawset" | "setmetatable"));
                let ordinary = matches!(&call.callee, AstExpr::FieldAccess(field)
                    if field.field == "concat" && matches!(&field.base,
                        AstExpr::Var(AstNameRef::Global(name)) if name.text == "table"));
                if !builtin && !ordinary {
                    return None;
                }
                let mut cost = if builtin {
                    Cost::fixed(2)
                } else {
                    Cost::fixed(3).add(self.expression(&call.callee)?)
                };
                for arg in &call.args {
                    let value = self.expression(arg)?;
                    cost = cost.add(if builtin && call.args.len() <= 2 {
                        value
                    } else {
                        value.argument()
                    });
                }
                cost
            }
            AstExpr::SingleValue(value) => return self.costed(value),
            _ => return None,
        };
        Some((cost, None))
    }
    fn block(&mut self, block: &AstBlock) -> Option<(Cost, bool)> {
        let mut cost = Cost::fixed(0);
        for stmt in &block.stmts {
            self.budget = self.budget.checked_sub(1)?;
            let (item, stops) = match stmt {
                AstStmt::LocalDecl(decl) if decl.bindings.len() == decl.values.len() => {
                    let mut current = Cost::fixed(0);
                    for (binding, value) in decl.bindings.iter().zip(&decl.values) {
                        let value = self.expression(value)?;
                        // 候选拒绝[ProofIncomplete:Cost]：只读局部常量可能另行折叠分支；
                        // 非常量副本可传播成本掩码；常量副本尚未传播真值，不能据此选择分支。
                        let AstBindingRef::Local(local) = binding.id else {
                            return None;
                        };
                        if !self.written.contains(&local) && value.is_constant() {
                            return None;
                        }
                        self.locals.insert(binding.id.to_name_ref(), value.local());
                        current = current.add(value);
                    }
                    (current, false)
                }
                AstStmt::LocalFunctionDecl(decl) => {
                    self.locals
                        .insert(decl.name.to_name_ref(), Cost::variable(self.discount_all));
                    (Cost::fixed(10), false)
                }
                AstStmt::Assign(assign) => {
                    for target in &assign.targets {
                        if let AstLValue::Name(name) = target {
                            if !matches!(name, AstNameRef::Local(_))
                                && !matches!(name, AstNameRef::Param(param) if self.mask.is_none() || self.function.params.last()==Some(param))
                            {
                                // 候选拒绝[ProofIncomplete:Cost]：前面的 Boolean 形参由 mask 提供真值；
                                // 对它们写入会使该事实失效，末参数则从不参与 mask。
                                return None;
                            }
                            self.locals
                                .insert(name.clone(), Cost::variable(self.discount_all));
                        }
                    }
                    if assign.targets.len() != assign.values.len() {
                        return None;
                    }
                    let mut current = Cost::fixed(0);
                    for (target, value) in assign.targets.iter().zip(&assign.values) {
                        let target_cost = match target {
                            AstLValue::Name(_) => Cost::fixed(0),
                            AstLValue::FieldAccess(field) => {
                                self.expression(&field.base)?.add(Cost::fixed(1))
                            }
                            AstLValue::IndexAccess(index) => self
                                .expression(&index.base)?
                                .add(self.expression(&index.index)?)
                                .add(Cost::fixed(1)),
                        };
                        current = current.add(target_cost.add(self.expression(value)?).argument());
                    }
                    (current, false)
                }
                AstStmt::CallStmt(stmt) => {
                    let AstCallKind::Call(call) = &stmt.call else {
                        return None;
                    };
                    (self.expression(&AstExpr::Call(call.clone()))?, false)
                }
                AstStmt::Return(ret) => {
                    let mut current = Cost::fixed(0);
                    for value in &ret.values {
                        current = current.add(self.expression(value)?);
                    }
                    (current, true)
                }
                AstStmt::If(branch) => {
                    let (condition, known) = self.costed(&branch.cond)?;
                    match known {
                        Some(true) => self.block(&branch.then_block)?,
                        Some(false) => {
                            if let Some(other) = &branch.else_block {
                                self.block(other)?
                            } else {
                                (Cost::fixed(0), false)
                            }
                        }
                        None => {
                            let (left, lstop) = self.block(&branch.then_block)?;
                            let (right, rstop) = if let Some(other) = &branch.else_block {
                                self.block(other)?
                            } else {
                                (Cost::fixed(0), false)
                            };
                            let jump = branch.else_block.as_ref().is_some_and(|other| {
                                !matches!(other.stmts.as_slice(), [AstStmt::If(_)])
                            });
                            (
                                condition
                                    .add(Cost::fixed(1 + usize::from(jump)))
                                    .add(left)
                                    .add(right),
                                lstop && rstop,
                            )
                        }
                    }
                }
                AstStmt::While(loop_) => {
                    let condition = self.expression(&loop_.cond)?;
                    (self.block(&loop_.body)?.0.add(condition).multiply(3), false)
                }
                AstStmt::Repeat(loop_) => {
                    let condition = self.expression(&loop_.cond)?;
                    (self.block(&loop_.body)?.0.add(condition).multiply(3), false)
                }
                AstStmt::GenericFor(loop_) => {
                    let mut input = Cost::fixed(0);
                    for value in &loop_.iterator {
                        input = input.add(self.expression(value)?);
                    }
                    (
                        input.add(self.block(&loop_.body)?.0.add(Cost::fixed(1)).multiply(3)),
                        false,
                    )
                }
                AstStmt::NumericFor(loop_) => {
                    let from = self.expression(&loop_.start)?;
                    let limit = self.expression(&loop_.limit)?;
                    let step = self.expression(&loop_.step)?;
                    let bounds = match (
                        counter_repeat::integer(&loop_.start),
                        counter_repeat::integer(&loop_.limit),
                        counter_repeat::integer(&loop_.step),
                    ) {
                        (Some(from), Some(to), Some(step)) => Some((from, to, step)),
                        (Some(_), None, Some(_))
                            if !limit.is_constant()
                                && (self.discount_all
                                    || matches!(&loop_.limit, AstExpr::Unary(length)
                                if length.op == AstUnaryOpKind::Length && matches!(length.expr, AstExpr::Var(AstNameRef::Param(_))))) =>
                        {
                            None
                        }
                        _ => return None,
                    };
                    let count = bounds.map_or(Some(3), |(a, b, c)| trips(a, b, c))?;
                    let body = self.block(&loop_.body)?.0;
                    if self.discount_all
                        && (bounds.is_none()
                            || count > 25
                            || body.discounted_floor().blocks_unroll_at_max_profit(count))
                    {
                        self.stable_loops.insert(loop_.binding);
                    }
                    (
                        from.add(limit)
                            .add(step)
                            .add(body.add(Cost::fixed(1)).multiply(count)),
                        false,
                    )
                }
                AstStmt::Break | AstStmt::Continue => (Cost::fixed(1), true),
                AstStmt::DoBlock(block) => self.block(block)?,
                _ => return None,
            };
            cost = cost.add(item);
            if stops {
                return Some((cost, true));
            }
        }
        Some((cost, false))
    }
}

pub(super) fn cost(func: &AstFunctionExpr, mask: Option<u8>) -> Option<Cost> {
    block_cost(func, &func.body, mask)
}

/// 独立循环成本从该 body 的局部环境开始；不沿用函数外部的临时折扣。
pub(super) fn block_cost(
    func: &AstFunctionExpr,
    body: &AstBlock,
    mask: Option<u8>,
) -> Option<Cost> {
    Model {
        function: func,
        mask,
        locals: BTreeMap::new(),
        budget: 1024,
        written: crate::ast::written_locals(&func.body),
        discount_all: false,
        stable_loops: BTreeSet::new(),
    }
    .block(body)
    .map(|(cost, _)| cost)
}

/// 完整函数中的动态形参不作常量专化；全部变量折扣只用来降低循环成本下界。
/// 函数成本和所有循环的最大收益拒绝证明在同一次遍历中计算。
pub(super) fn runtime_summary(func: &AstFunctionExpr) -> Option<(Cost, BTreeSet<AstBindingRef>)> {
    let mut model = Model {
        function: func,
        mask: None,
        locals: BTreeMap::new(),
        budget: 1024,
        written: crate::ast::written_locals(&func.body),
        discount_all: true,
        stable_loops: BTreeSet::new(),
    };
    let cost = model.block(&func.body)?.0;
    Some((cost, model.stable_loops))
}

fn trace_matches(
    func: &AstFunctionExpr,
    proto: &crate::hir::HirProto,
    parameters: usize,
    mask: u8,
) -> bool {
    if func.function != proto.id
        || func.params.len() != parameters
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.captured_bindings.is_empty()
        || !func.captured_params.is_empty()
        || !func.capture_write_names.is_empty()
    {
        return false;
    }
    let Some(expected) = crate::hir::luau_inlining::constant_control::trace(proto, mask) else {
        return false;
    };
    let mut builder = TraceBuilder {
        function: func,
        mask,
        locals: BTreeMap::new(),
        trace: Trace {
            actions: Vec::new(),
            returned: Vec::new(),
        },
        budget: 256,
    };
    builder.block(&func.body, true) == Some(Flow::Return) && builder.trace == expected
}

fn argument_mask(args: &[AstExpr], parameters: usize) -> Option<u8> {
    if args.len() != parameters {
        return None;
    }
    args[..parameters - 1]
        .iter()
        .enumerate()
        .try_fold(0, |mask, (bit, arg)| {
            let AstExpr::Boolean(value) = arg else {
                return None;
            };
            Some(mask | (u8::from(*value) << bit))
        })
}

struct FunctionCosts {
    parameters: usize,
    baseline: Cost,
    profiles: Vec<Option<Cost>>,
    inlined: Vec<bool>,
}

pub(super) struct Models(BTreeMap<crate::hir::LocalId, FunctionCosts>);

impl Models {
    pub(super) fn new(
        statements: &[&AstStmt],
        bodies: &BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
        hir: &crate::hir::HirModule,
    ) -> Option<Self> {
        let mut models = BTreeMap::new();
        for stmt in statements {
            let AstStmt::LocalFunctionDecl(decl) = stmt else {
                continue;
            };
            let AstBindingRef::Local(local) = decl.name else {
                continue;
            };
            let Some(&HirLuauInliningBody::ConstantControl {
                template,
                parameters,
            }) = bodies.get(&local)
            else {
                continue;
            };
            if !(2..=8).contains(&parameters) {
                return None;
            }
            let baseline = cost(&decl.func, None)?;
            let profiles: Vec<_> = (0..1u8 << (parameters - 1))
                .map(|mask| cost(&decl.func, Some(mask)))
                .collect();
            let proto = hir.protos.get(template)?;
            let inlined = profiles
                .iter()
                .enumerate()
                .map(|(mask, cost)| {
                    cost.is_some_and(|cost| cost.permits_inline(baseline))
                        && trace_matches(&decl.func, proto, parameters, mask as u8)
                })
                .collect();
            models.insert(
                local,
                FunctionCosts {
                    parameters,
                    baseline,
                    profiles,
                    inlined,
                },
            );
        }
        Some(Self(models))
    }

    pub(super) fn declaration(&self, local: crate::hir::LocalId) -> bool {
        self.0
            .get(&local)
            .is_some_and(|model| model.inlined.iter().any(|valid| *valid))
    }

    pub(super) fn inlined(&self, local: crate::hir::LocalId, args: &[AstExpr]) -> bool {
        let Some(model) = self.0.get(&local) else {
            return false;
        };
        argument_mask(args, model.parameters).is_some_and(|mask| model.inlined[usize::from(mask)])
            && matches!(args.last(), Some(AstExpr::TableConstructor(table)) if table.fields.is_empty())
    }

    pub(super) fn retained(
        &self,
        local: crate::hir::LocalId,
        args: &[AstExpr],
        nonconstant: &BTreeSet<crate::hir::LocalId>,
    ) -> bool {
        let Some(model) = self.0.get(&local) else {
            return false;
        };
        if args.len() != model.parameters {
            return false;
        }
        let controls = &args[..args.len() - 1];
        let profile = argument_mask(args, model.parameters);
        if let Some(mask) = profile {
            return model.profiles[usize::from(mask)]
                .is_some_and(|cost| !cost.permits_inline(model.baseline));
        }
        // 候选拒绝[ProofIncomplete:Cost]：混合常量配置尚未建表；全部动态控制
        // 必须来自原不展开循环/显式写入，不能把任意 local 当成不可折叠实参。
        controls.iter().all(|arg| matches!(arg, AstExpr::Var(AstNameRef::Local(local)) if nonconstant.contains(local)))
            && !model.baseline.permits_inline(model.baseline)
    }
}

/// 编译器不能常量折叠的输入沿单个显式 RHS 传播；不穿过任意可内联函数调用。
pub(super) fn extend_runtime_values(body: &AstBlock, values: &mut BTreeSet<crate::hir::LocalId>) {
    fn runtime(expr: &AstExpr, values: &BTreeSet<crate::hir::LocalId>) -> bool {
        match expr {
            AstExpr::Var(AstNameRef::Local(local)) => values.contains(local),
            AstExpr::Binary(binary) => runtime(&binary.lhs, values) || runtime(&binary.rhs, values),
            AstExpr::Unary(unary) => runtime(&unary.expr, values),
            // pinned ConstantFolding 只有左操作数已知时才选择短路分支；
            // 动态左臂使结果保持未知，不能仅因右臂动态就作相同推断。
            AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
                runtime(&logical.lhs, values)
            }
            AstExpr::Call(call)
                if matches!(&call.callee, AstExpr::FieldAccess(field)
                if field.field == "floor" && matches!(&field.base, AstExpr::Var(AstNameRef::Global(name)) if name.text == "math")) =>
            {
                call.args.iter().any(|arg| runtime(arg, values))
            }
            _ => false,
        }
    }
    let mut pending = vec![body];
    while let Some(block) = pending.pop() {
        for stmt in &block.stmts {
            if let AstStmt::LocalDecl(decl) = stmt {
                for (binding, value) in decl.bindings.iter().zip(&decl.values) {
                    if let AstBindingRef::Local(local) = binding.id
                        && runtime(value, values)
                    {
                        values.insert(local);
                    }
                }
            }
            crate::ast::traverse::traverse_stmt_children!(stmt, iter=iter, opt=as_ref, borrow=[&],
                expr(_expr) => {}, lvalue(_lvalue) => {}, block(block) => { pending.push(block); },
                function(_function) => {}, condition(_condition) => {}, call(_call) => {});
        }
    }
}
