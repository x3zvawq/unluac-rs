//! 恢复已有封闭函数的标量表达式展开帧。
//!
//! 原指令区间签证参数、结果与 scratch 映射；当前 HIR 值树再次匹配，参数准备和后缀交给完整帧事务。

use super::*;
use crate::hir::promotion::value_programs::{Literal, Operation, Region, Template};
use crate::transformer::Reg;

#[derive(Clone)]
pub(super) struct Body {
    template: Template,
    expression: HirExpr,
    names: Vec<Option<String>>,
}

fn cost(expr: &HirExpr, budget: &mut usize) -> Option<()> {
    if *budget == 0 {
        return None;
    }
    *budget -= 1;
    match expr {
        HirExpr::ParamRef(_) => Some(()),
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                crate::hir::HirBinaryOpKind::Eq
                    | crate::hir::HirBinaryOpKind::Lt
                    | crate::hir::HirBinaryOpKind::Le
            ) =>
        {
            cost(&binary.lhs, budget)?;
            cost(&binary.rhs, budget)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            cost(&logical.lhs, budget)?;
            cost(&logical.rhs, budget)
        }
        value => Literal::from_expr(value).map(|_| ()),
    }
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let template = facts.value_program_template()?;

    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([expression], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    if proto.failure.is_some()
        || !proto.children.is_empty()
        || !proto.upvalues.is_empty()
        || proto.params.len() != template.parameters
        || ret.pending_cleanup_source.is_some()
        || !matches!(template.program.shape.first(), Some(Operation::Copy))
        || template.program.registers.first()?.as_slice().first() != Some(&template.result)
    {
        return None;
    }
    // 候选拒绝[TargetConstraint]：按全部节点收费，不借常量实参折扣删掉原比较或分支。
    cost(expression, &mut 25)?;

    Some(Body {
        template: template.clone(),
        expression: expression.clone(),
        names: proto.param_debug_hints.clone(),
    })
}

pub(in crate::hir::simplify::call_frames) struct Frames<'a> {
    matches: BTreeMap<TempId, Match<'a>>,
    original_nil: BTreeSet<LocalId>,
}

struct Match<'a> {
    callee: &'a Callee,
    arguments: Vec<TempId>,
    first_parameter: usize,
}

impl Frames<'_> {
    pub(in crate::hir::simplify::call_frames) fn contains(&self, result: TempId) -> bool {
        self.matches.contains_key(&result)
    }
}

pub(super) fn frames<'a>(
    proto: &HirProto,
    callees: &'a Callees,
    facts: &ProtoPromotionFacts,
) -> Frames<'a> {
    let mut templates = BTreeMap::new();
    for callee in callees.values() {
        if let Some(body) = &callee.value_expression {
            templates
                .entry(body.template.program.shape.clone())
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    let mut writes = BTreeMap::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingWriteCollector(|binding| {
            *writes.entry(binding).or_insert(0usize) += 1;
        }),
    );
    let matches: BTreeMap<_, _> = facts
        .value_programs()
        .filter_map(|region| {
            region.initial?;
            let callee = (*templates.get(&region.program.shape)?)?;

            let body = callee.value_expression.as_ref()?;
            if callee.creation.instr >= region.source {
                return None;
            }
            let mapping = body.template.program.register_mapping(&region.program)?;

            let home = facts.trusted_temp_home_slot(region.result)?;
            if mapping.get(&body.template.result)?.index() != home.slot() {
                return None;
            }
            let mut top = home.slot() + 1;
            let mut arguments = Vec::new();
            for parameter in 0..body.template.parameters {
                let reg = *mapping.get(&Reg(parameter))?;
                let input = *region.inputs.get(&reg)?;
                let local = facts.promoted_local_for_temp(input)?;

                if !facts.temp_definition_reference_unaliased(input) {
                    return None;
                }
                if reg.index() < home.slot() {
                    // 候选拒绝[ProofIncomplete:Binding]：只有现存只读 local 才由编译器复用原参数槽。
                    if writes.get(&HirBinding::Local(local)) != Some(&1) {
                        return None;
                    }
                } else {
                    if reg.index() != top {
                        return None;
                    }
                    top += 1;
                }
                arguments.push(input);
            }
            for (&reg, &actual) in &mapping {
                if reg.index() > body.template.result.index()
                    && actual.index() != top + reg.index() - body.template.result.index() - 1
                {
                    return None;
                }
            }
            let first_parameter = body.template.program.registers.first()?.get(1)?.index();
            (first_parameter < arguments.len()).then_some((
                region.result,
                Match {
                    callee,
                    arguments,
                    first_parameter,
                },
            ))
        })
        .collect();

    let original_nil = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect();
    Frames {
        matches,
        original_nil,
    }
}

pub(super) fn debug_arguments(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
) -> Option<(HirProto, Vec<(crate::hir::HirSourceSite, LocalId)>)> {
    let frames = frames(proto, callees, facts);
    let mut projected = Vec::new();
    for (&result, matched) in &frames.matches {
        let region = facts.value_program(result)?;
        let body = matched.callee.value_expression.as_ref()?;
        for (parameter, &input) in matched.arguments.iter().enumerate() {
            let local = facts.promoted_local_for_temp(input)?;
            let Some(scope_id) = proto.local_debug_scopes[local.index()] else {
                continue;
            };
            let Some(scope) = proto.debug_scopes.get(scope_id).and_then(Option::as_ref) else {
                continue;
            };
            if scope.start_pc != region.source_pc
                || scope.end_instr != Some(region.end)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(input)
                || proto.local_debug_hints[local.index()].is_none()
                || proto.local_debug_hints[local.index()] != body.names[parameter]
            {
                continue;
            }
            projected.push((
                input,
                local,
                crate::hir::HirSourceSite {
                    proto: proto.id,
                    instr: region.source,
                },
                matched.callee.local,
            ));
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

fn same_expression(
    template: &HirExpr,
    actual: &HirExpr,
    arguments: &[LocalId],
    initial: LocalId,
    first: usize,
) -> bool {
    match (template, actual) {
        (HirExpr::ParamRef(param), HirExpr::LocalRef(local)) => {
            arguments.get(param.index()) == Some(local)
                || param.index() == first && *local == initial
        }
        (HirExpr::Binary(a), HirExpr::Binary(b)) => {
            a.op == b.op
                && same_expression(&a.lhs, &b.lhs, arguments, initial, first)
                && same_expression(&a.rhs, &b.rhs, arguments, initial, first)
        }
        (HirExpr::LogicalAnd(a), HirExpr::LogicalAnd(b))
        | (HirExpr::LogicalOr(a), HirExpr::LogicalOr(b)) => {
            same_expression(&a.lhs, &b.lhs, arguments, initial, first)
                && same_expression(&a.rhs, &b.rhs, arguments, initial, first)
        }
        (a, b) => Literal::from_expr(a).is_some_and(|a| Some(a) == Literal::from_expr(b)),
    }
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn has_value_expression(
        &self,
        result: TempId,
    ) -> bool {
        self.native
            .and_then(|context| context.value_expressions)
            .is_some_and(|frames| frames.contains(result))
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_value_expression(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        result: TempId,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let matched = context.value_expressions?.matches.get(&result)?;
        let region: &Region = self.facts.value_program(result)?;
        let body = matched.callee.value_expression.as_ref()?;
        let home = self.facts.trusted_temp_home_slot(result)?;
        let initial = self.facts.promoted_local_for_temp(region.initial?)?;
        let arguments = matched
            .arguments
            .iter()
            .map(|input| self.facts.promoted_local_for_temp(*input))
            .collect::<Option<Vec<_>>>()?;
        let copy = self.definition(initial, before)?;

        if home.slot() != slot
            || context.barred.contains(&home)
            || context.closed.contains(&home)
            || self.definitions.get(&initial)?.as_slice() != [copy]
            || !self.homes_match(initial, copy, slot, None, region.initial)
            || context.proto.local_debug_hints[initial.index()].is_some()
            || context.proto.local_debug_scopes[initial.index()].is_some()
            || scalar_local(self.run[copy])
                != Some((
                    initial,
                    &HirExpr::LocalRef(arguments[matched.first_parameter]),
                ))
            || !same_expression(
                &body.expression,
                expr,
                &arguments,
                initial,
                matched.first_parameter,
            )
        {
            return None;
        }
        let mut values = Vec::new();
        for (&input, &local) in matched.arguments.iter().zip(&arguments) {
            let home = self.facts.trusted_temp_home_slot(input)?;
            let value = HirExpr::LocalRef(local);
            values.push(if home.slot() < slot {
                value
            } else {
                let definition = self.definition(local, copy)?;
                if let Some(empty) = definition.checked_sub(1)
                    && let HirStmt::LocalDecl(decl) = self.run[empty]
                    && decl.bindings == [local]
                    && decl.values.is_empty()
                {
                    // 原 phi 参数只有合成声明入口；完整实参准备退休它，不跳过真实 LOADNIL。
                    if !self.facts.is_phi_carrier_temp(input)
                        || context.value_expressions?.original_nil.contains(&local)
                        || decl.initializer_merge_transaction.is_some()
                        || decl.generic_for_initializer_producer.is_some()
                        || context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some()
                    {
                        return None;
                    }
                    self.finish_event(empty)?;
                }
                self.expr(&value, copy, home.slot(), None, false, true, Some(input))?
            });
        }
        if !values
            .iter()
            .zip(&matched.arguments)
            .all(|(value, input)| match value {
                HirExpr::LocalRef(_) => self
                    .facts
                    .trusted_temp_home_slot(*input)
                    .is_some_and(|home| home.slot() < slot),
                HirExpr::Binary(binary) => {
                    matches!(
                        binary.op,
                        crate::hir::HirBinaryOpKind::Eq
                            | crate::hir::HirBinaryOpKind::Lt
                            | crate::hir::HirBinaryOpKind::Le
                    ) && matches!(binary.lhs, HirExpr::LocalRef(_))
                        && (matches!(binary.rhs, HirExpr::LocalRef(_))
                            || Literal::from_expr(&binary.rhs).is_some())
                }
                _ => false,
            })
        {
            return None;
        }
        self.finish_event(copy)?;

        Some(factories::factory_call(
            matched.callee.local,
            Some(crate::hir::HirSourceSite {
                proto: context.proto.id,
                instr: region.source,
            }),
            values.into(),
        ))
    }
}
