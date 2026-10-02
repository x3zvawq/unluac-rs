//! 用现存封闭函数承接已展开的常量选值帧。
//!
//! Structure 决策事实连接实参版本与结果，FrameBuilder 重放实参准备；整个结果包和后缀
//! 必须一起通过源码前缀事务，Generate 再确认恢复的调用会消失。

use super::*;
use crate::hir::promotion::LiteralChoiceTest;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::hir::simplify::call_frames) enum Literal {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(u64),
    String(crate::LuaString),
    Vector(crate::parser::VectorLiteral),
}

fn literal(value: &HirExpr) -> Option<Literal> {
    Some(match value {
        HirExpr::Nil => Literal::Nil,
        HirExpr::Boolean(value) => Literal::Boolean(*value),
        HirExpr::Integer(value) => Literal::Integer(*value),
        HirExpr::Number(value) => Literal::Number(value.to_bits()),
        HirExpr::String(value) => Literal::String(value.clone()),
        HirExpr::Vector(value) => Literal::Vector(*value),
        _ => return None,
    })
}

#[derive(Clone)]
pub(super) struct Body {
    values: Vec<Literal>,
    expression: HirExpr,
    comparisons: Vec<LiteralChoiceTest>,
}

pub(in crate::hir::simplify::call_frames) struct ComparedCallees<'a> {
    templates: BTreeMap<(Vec<LiteralChoiceTest>, Vec<Literal>), Option<&'a Callee>>,
    inputs: BTreeSet<TempId>,
    constants: BTreeMap<Literal, Option<(&'a Callee, HirExpr)>>,
}

impl ComparedCallees<'_> {
    pub(in crate::hir::simplify::call_frames) fn owns_input(&self, input: TempId) -> bool {
        self.inputs.contains(&input)
    }

    pub(super) fn constant(&self, value: &HirExpr) -> Option<(&Callee, HirExpr)> {
        self.constants.get(&literal(value)?)?.clone()
    }
}

pub(super) fn compared_callees<'a>(
    callees: &'a Callees,
    facts: &ProtoPromotionFacts,
) -> ComparedCallees<'a> {
    let mut index = BTreeMap::new();
    let mut constants = BTreeMap::new();
    for callee in callees.values() {
        if let Some(body) = &callee.literal_choice
            && !body.comparisons.is_empty()
        {
            index
                .entry((body.comparisons.clone(), body.values.clone()))
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
            // 只用无求值的规范实参重发已存在的常量 LOAD，不声称恢复被优化掉的原实参。
            // pinned O2 先折叠调用外部常量，再内联模板；完整比较因而不会被删去。
            for argument in [
                HirExpr::Nil,
                HirExpr::Boolean(false),
                HirExpr::Boolean(true),
                HirExpr::Integer(0),
            ] {
                let selected = body
                    .comparisons
                    .iter()
                    .position(|test| match test {
                        LiteralChoiceTest::EqualNil => matches!(argument, HirExpr::Nil),
                        LiteralChoiceTest::EqualBoolean(expected) => {
                            matches!(argument, HirExpr::Boolean(actual) if actual == *expected)
                        }
                        LiteralChoiceTest::Truthy => false,
                    })
                    .unwrap_or(body.comparisons.len());
                constants
                    .entry(body.values[selected].clone())
                    .and_modify(|entry: &mut Option<(&Callee, HirExpr)>| {
                        if entry
                            .as_ref()
                            .is_some_and(|(previous, _)| previous.local != callee.local)
                        {
                            *entry = None;
                        }
                    })
                    .or_insert(Some((callee, argument)));
            }
        }
    }
    let inputs = facts
        .literal_choices()
        .filter_map(|choice| {
            let input = *choice.inputs.first()?;
            let values = choice
                .values
                .iter()
                .map(literal)
                .collect::<Option<Vec<_>>>()?;
            (choice.inputs.iter().all(|other| *other == input)
                && index
                    .get(&(choice.tests.clone(), values))
                    .is_some_and(Option::is_some))
            .then_some(input)
        })
        .collect();
    ComparedCallees {
        templates: index,
        inputs,
        constants,
    }
}

/// 只在未提交副本上把完整展开区间的身份交给原 child 形参；每份投影都必须
/// 由相同调用点的内联证书承接，不能单凭名字相同删除普通 debug local。
pub(super) fn debug_arguments(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
) -> Option<(HirProto, Vec<(crate::hir::HirSourceSite, LocalId)>)> {
    let index = compared_callees(callees, facts);
    let mut projected = Vec::new();
    for choice in facts.literal_choices() {
        let Some(&input) = choice.inputs.first() else {
            continue;
        };
        if !index.owns_input(input) {
            continue;
        }
        let candidate = (|| {
            let values = choice
                .values
                .iter()
                .map(literal)
                .collect::<Option<Vec<_>>>()?;
            let callee = (*index.templates.get(&(choice.tests.clone(), values))?)?;
            let local = facts.promoted_local_for_temp(input)?;
            let name = proto.local_debug_hints[local.index()].as_ref()?;
            let scope_id = proto.local_debug_scopes[local.index()]?;
            let scope = proto.debug_scopes.get(scope_id)?.as_ref()?;
            let home = facts.trusted_temp_home_slot(input)?;
            if callee.parameter_name.as_ref() != Some(name)
                || scope.initializer_temp != Some(input)
                || scope.initializer_phi.is_some()
                || scope.initializer_end_instr?.index() + 1 != choice.source.index()
                || scope.end_instr != Some(choice.end)
                || !facts.temp_definition_is_uncaptured(input)
                || !facts
                    .complete_local_definition_write_homes(local)
                    .iter()
                    .copied()
                    .eq([home])
                || !choice.inputs.iter().all(|other| *other == input)
            {
                return None;
            }
            Some((
                input,
                local,
                crate::hir::HirSourceSite {
                    proto: proto.id,
                    instr: choice.source,
                },
                callee.local,
            ))
        })();
        if let Some(candidate) = candidate {
            projected.push(candidate);
        }
    }
    if projected.is_empty() {
        return None;
    }
    let mut draft = proto.clone();
    let mut obligations = Vec::new();
    for (input, local, site, callee) in projected {
        draft.local_debug_hints[local.index()] = None;
        draft.local_debug_scopes[local.index()] = None;
        draft.temp_debug_locals[input.index()] = None;
        draft.temp_debug_scopes[input.index()] = None;
        obligations.push((site, callee));
    }
    Some((draft, obligations))
}

fn comparison_test(expr: &HirExpr) -> Option<LiteralChoiceTest> {
    let HirExpr::Binary(binary) = expr else {
        return None;
    };
    if binary.op != crate::hir::HirBinaryOpKind::Eq {
        return None;
    }
    match binary.rhs {
        HirExpr::Nil => Some(LiteralChoiceTest::EqualNil),
        HirExpr::Boolean(value) => Some(LiteralChoiceTest::EqualBoolean(value)),
        _ => None,
    }
}

fn comparison_body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let [parameter] = proto.params.as_slice() else {
        return None;
    };
    let expression = returned(&proto.body)?;

    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    if !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack)
        if pack.start.index() == 1 && pack.len == 1)
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }
    let mut value = expression;
    let mut values = Vec::new();
    let mut comparisons = Vec::new();
    while let HirExpr::LogicalOr(other) = value {
        let HirExpr::LogicalAnd(selected) = &other.lhs else {
            return None;
        };
        let HirExpr::Binary(binary) = &selected.lhs else {
            return None;
        };
        let test = comparison_test(&selected.lhs)?;
        let layout = facts.native_binary_layout(binary)?;
        if binary.lhs != HirExpr::ParamRef(*parameter)
            || layout.lhs != facts.trusted_param_home_slot(*parameter)
            || layout.rhs.is_some()
            || crate::hir::value_facts::value_facts(&selected.rhs).truthiness() != Some(true)
        {
            return None;
        }
        comparisons.push(test);
        values.push(literal(&selected.rhs)?);
        value = &other.rhs;
    }
    values.push(literal(value)?);
    // 每项比较、两层逻辑和常量各计费，不以实参的已知类型折扣原显式检查。
    if comparisons.is_empty()
        || comparisons.len() * 5 + 1 > 25
        || values
            .iter()
            .any(|value| matches!(value, Literal::Vector(_)))
    {
        return None;
    }
    Some(Body {
        values,
        expression: expression.clone(),
        comparisons,
    })
}

fn returned(block: &HirBlock) -> Option<&HirExpr> {
    let [HirStmt::Return(ret)] = block.stmts.as_slice() else {
        return None;
    };
    let ([value], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    Some(value)
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    if proto.params.is_empty()
        || proto.params.len() > 4
        || proto.signature.is_vararg
        || !proto.children.is_empty()
        || !proto.upvalues.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    if let Some(body) = comparison_body(proto, facts) {
        return Some(body);
    }
    let mut block = &proto.body;
    let mut values = Vec::new();
    let mut cost = 0;
    let mut arms = Vec::new();
    let valid_return = |block: &HirBlock| {
        matches!(block.stmts.as_slice(), [HirStmt::Return(ret)]
            if ret.pending_cleanup_source.is_none()
                && facts.native_return_frame(ret).is_some_and(|frame| matches!(frame.values,
                    ValuePack::Fixed(pack) if pack.start.index() == proto.params.len() && pack.len == 1)))
    };
    for parameter in &proto.params {
        let [HirStmt::If(branch)] = block.stmts.as_slice() else {
            return None;
        };
        if branch.cond != HirExpr::ParamRef(*parameter) {
            return None;
        }
        if !valid_return(&branch.then_block) {
            return None;
        }
        let value = returned(&branch.then_block)?;
        arms.push((*parameter, value.clone()));
        if crate::hir::value_facts::value_facts(value).truthiness() != Some(true) {
            return None;
        }
        cost += 2 + if matches!(value, HirExpr::Vector(_)) {
            6
        } else {
            1
        };
        values.push(literal(value)?);
        block = branch.else_block.as_ref()?;
    }
    if !valid_return(block) {
        return None;
    }
    let value = returned(block)?;
    cost += if matches!(value, HirExpr::Vector(_)) {
        6
    } else {
        1
    };
    values.push(literal(value)?);
    // 按最终 and/or 的两层操作以及四分量向量构造上界计费；不借常量折扣。
    let mut expression = value.clone();
    for (parameter, value) in arms.into_iter().rev() {
        expression = HirExpr::LogicalOr(Box::new(crate::hir::common::HirLogicalExpr {
            preserves_boolean_prewrite: false,
            lhs: HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr {
                preserves_boolean_prewrite: false,
                lhs: HirExpr::ParamRef(parameter),
                rhs: value,
            })),
            rhs: expression,
        }));
    }
    (cost <= 25).then_some(Body {
        values,
        expression,
        comparisons: Vec::new(),
    })
}

fn matches_value(
    value: &HirExpr,
    choice: &crate::hir::promotion::LiteralChoice,
    facts: &ProtoPromotionFacts,
) -> bool {
    let mut value = value;
    for (&input, expected) in choice.inputs.iter().zip(&choice.values) {
        let HirExpr::LogicalOr(other) = value else {
            return false;
        };
        let HirExpr::LogicalAnd(selected) = &other.lhs else {
            return false;
        };
        if facts
            .promoted_local_for_temp(input)
            .map(HirExpr::LocalRef)
            .as_ref()
            != Some(&selected.lhs)
            || literal(&selected.rhs) != literal(expected)
        {
            return false;
        }
        value = &other.rhs;
    }
    literal(value) == choice.values.last().and_then(literal)
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    roots: &[usize],
) -> Vec<Plan> {
    let mut templates = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|callees| callees.values())
    {
        if let Some(body) = &callee.literal_choice
            && body.comparisons.is_empty()
        {
            templates
                .entry(&body.values)
                .and_modify(|value| *value = None)
                .or_insert(Some(callee));
        }
    }
    if templates.is_empty() {
        return Vec::new();
    }
    let mut choices = BTreeMap::new();
    for choice in facts.literal_choices() {
        if choice
            .tests
            .iter()
            .any(|test| *test != LiteralChoiceTest::Truthy)
        {
            continue;
        }
        if let Some(local) = facts.promoted_local_for_temp(choice.result) {
            choices
                .entry(local)
                .and_modify(|value| *value = None)
                .or_insert(Some(choice));
        }
    }
    let nils = facts
        .nil_write_groups()
        .filter_map(|group| {
            let [temp] = group else {
                return None;
            };
            facts
                .temp_definition_reference_unaliased(*temp)
                .then_some(())?;
            Some((facts.promoted_local_for_temp(*temp)?, *temp))
        })
        .collect::<BTreeMap<_, _>>();
    let mut flat = Vec::new();
    prefix::coordinates::visit(&context.proto.body, &mut 0, &mut |index, kind, stmt| {
        flat.push((kind == PointKind::Statement).then_some((index, stmt)));
    });
    let mut floor = 0;
    let mut plans = Vec::new();
    for (position, entry) in flat.iter().enumerate() {
        let Some((index, stmt)) = *entry else {
            floor = position + 1;
            continue;
        };
        let Some((result, value)) = scalar_local(stmt) else {
            floor = position + 1;
            continue;
        };
        let Some(Some(choice)) = choices.get(&result) else {
            continue;
        };
        if choice
            .tests
            .iter()
            .any(|test| *test != LiteralChoiceTest::Truthy)
        {
            continue;
        }
        let candidate = (|| {
            if !matches!(stmt, HirStmt::LocalDecl(_)) || !matches_value(value, choice, facts) {
                return None;
            }
            let key = choice
                .values
                .iter()
                .map(literal)
                .collect::<Option<Vec<_>>>()?;
            let callee = (*templates.get(&key)?)?;
            let base = facts.trusted_local_home_slot(result)?;
            let &(nil_index, nil_stmt) = flat.get(position + 1)?.as_ref()?;
            let (extra, HirExpr::Nil) = scalar_local(nil_stmt)? else {
                return None;
            };
            if !matches!(nil_stmt, HirStmt::LocalDecl(_))
                || facts.trusted_temp_home_slot(*nils.get(&extra)?)
                    != Some(HomeSlotKey::new(base.slot() + 1, 0))
                || roots[callee.declaration] >= index
                || base != HomeSlotKey::new(base.slot(), 0)
                || context.barred.contains(&base)
                || context.closed.contains(&base)
            {
                return None;
            }
            let run = flat[floor..position]
                .iter()
                .map(|entry| entry.map(|(_, stmt)| stmt))
                .collect::<Option<Vec<_>>>()?;
            let mut builder =
                frame_builder(context, &run, facts, DecompileDialect::Luau, base.slot())?;
            builder.declaration_reserved_top = Some(base.slot() + 2);
            let mut args = Vec::new();
            for (offset, &input) in choice.inputs.iter().enumerate() {
                let home = HomeSlotKey::new(base.slot() + 2 + offset, 0);
                if facts.trusted_temp_home_slot(input) != Some(home) {
                    return None;
                }
                let local = facts.promoted_local_for_temp(input)?;
                args.push(builder.expr(
                    &HirExpr::LocalRef(local),
                    run.len(),
                    home.slot(),
                    None,
                    false,
                    true,
                    Some(input),
                )?);
            }
            if builder.next_event != run.len() || !args.iter().all(predicate_argument) {
                return None;
            }
            let first = floor + builder.first_event?;
            let start = flat[first]?.0;
            let source = crate::hir::HirSourceSite {
                proto: context.proto.id,
                instr: choice.source,
            };
            let mut plan = factories::invocation(callee, source, base, result, start, nil_index);
            plan.values = HirValuePack {
                fixed: Vec::new(),
                tail: Some(HirPackTail::exact(
                    factories::factory_call(callee.local, Some(source), args.into()),
                    2,
                )),
            };
            plan.result_locals.push(extra);
            Some(plan)
        })();
        plans.extend(candidate);
        // 每个候选只读自己之前的窗口，失败也不把旧准备重复归入后续候选。
        floor = position + 1;
    }
    plans
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn has_compared_choice(
        &self,
        result: TempId,
    ) -> bool {
        let Some(choice) = self.facts.compared_literal_choice(result) else {
            return false;
        };
        let Some(index) = self.native.and_then(|context| context.compared_choices) else {
            return false;
        };
        if choice.tests.len() > 4 || choice.tests.contains(&LiteralChoiceTest::Truthy) {
            return false;
        }
        let Some(values) = choice
            .values
            .iter()
            .map(literal)
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        index
            .templates
            .get(&(choice.tests.clone(), values))
            .is_some_and(Option::is_some)
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_compared_choice(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        result: TempId,
    ) -> Option<HirExpr> {
        let context = self.native?;

        let choice = self.facts.compared_literal_choice(result)?;
        let input = *choice.inputs.first()?;
        let input_local = self.facts.promoted_local_for_temp(input)?;
        let result_home = self.facts.trusted_temp_home_slot(result)?;
        if choice.inputs.iter().any(|value| *value != input)
            || choice.tests.contains(&LiteralChoiceTest::Truthy)
            || result_home != HomeSlotKey::new(slot, 0)
            || self.facts.trusted_temp_home_slot(input) != Some(HomeSlotKey::new(slot + 1, 0))
            || !self.facts.temp_definition_is_uncaptured(input)
            || context.barred.contains(&result_home)
            || context.closed.contains(&result_home)
        {
            return None;
        }
        let key = (
            choice.tests.clone(),
            choice
                .values
                .iter()
                .map(literal)
                .collect::<Option<Vec<_>>>()?,
        );
        let callee = (*context.compared_choices?.templates.get(&key)?)?;

        if callee.creation.proto != context.proto.id || callee.creation.instr >= choice.source {
            return None;
        }
        let mut value = expr;
        for (offset, &test) in choice.tests.iter().enumerate() {
            let HirExpr::LogicalOr(other) = value else {
                return None;
            };
            let HirExpr::LogicalAnd(selected) = &other.lhs else {
                return None;
            };
            let HirExpr::Binary(binary) = &selected.lhs else {
                return None;
            };
            if comparison_test(&selected.lhs) != Some(test)
                || binary.lhs != HirExpr::LocalRef(input_local)
                || binary.source_site
                    != Some(crate::hir::HirSourceSite {
                        proto: context.proto.id,
                        instr: choice.predicates[offset],
                    })
                || literal(&selected.rhs) != literal(&choice.values[offset])
            {
                return None;
            }
            value = &other.rhs;
        }
        if literal(value) != choice.values.last().and_then(literal) {
            return None;
        }
        let source = crate::hir::HirSourceSite {
            proto: context.proto.id,
            instr: choice.source,
        };
        // 一次原输入准备供整条比较链读取；消费完整模板后才退休该声明，不能逐比较内联输入。

        let argument = self.expr(
            &HirExpr::LocalRef(input_local),
            before,
            slot + 1,
            None,
            false,
            true,
            Some(input),
        )?;

        Some(factories::factory_call(
            callee.local,
            Some(source),
            vec![argument].into(),
        ))
    }
}

/// 单值逻辑返回使内联后的补 nil 位于共同出口；分支末尾的裸向量构造会成为开放调用。
pub(super) fn publish(body: &Body, proto: &mut HirProto) {
    proto.body.stmts = vec![HirStmt::Return(Box::new(
        crate::hir::common::HirReturn::synthetic(vec![body.expression.clone()].into()),
    ))];
}

// 候选拒绝[TargetConstraint]：仅认领运行时比较实参；额外 CALL、函数解析及常量折叠
// 需要各自的编译合同，不能因实参帧可重放就自动允许它们启用 O2。
fn predicate_argument(value: &HirExpr) -> bool {
    fn operand(value: &HirExpr) -> bool {
        match value {
            HirExpr::LocalRef(_)
            | HirExpr::ParamRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => true,
            HirExpr::Binary(binary) => {
                matches!(
                    binary.op,
                    crate::hir::HirBinaryOpKind::Add | crate::hir::HirBinaryOpKind::Mod
                ) && matches!(binary.lhs, HirExpr::LocalRef(_))
                    && matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
            }
            _ => false,
        }
    }
    let HirExpr::Binary(binary) = value else {
        return false;
    };
    matches!(
        binary.op,
        crate::hir::HirBinaryOpKind::Eq
            | crate::hir::HirBinaryOpKind::Lt
            | crate::hir::HirBinaryOpKind::Le
            | crate::hir::HirBinaryOpKind::Gt
            | crate::hir::HirBinaryOpKind::Ge
    ) && operand(&binary.lhs)
        && operand(&binary.rhs)
        && (crate::hir::visit::any_expr(&binary.lhs, &mut |value| {
            matches!(
                value,
                HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::UpvalueRef(_)
            )
        }) || crate::hir::visit::any_expr(&binary.rhs, &mut |value| {
            matches!(
                value,
                HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::UpvalueRef(_)
            )
        }))
}
