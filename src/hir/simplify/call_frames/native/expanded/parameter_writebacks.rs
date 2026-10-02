//! 恢复首参数经比较和选值重写后的完整调用。
//! 原封闭程序负责操作与 COPY 身份，当前树负责唯一使用，整批前缀负责结果预留槽。

use super::value_uses::ValueUses;
use super::*;
use crate::hir::promotion::value_programs::parameter_writebacks::{Body, Frame};
use crate::hir::promotion::value_programs::{Literal, Predicate};

fn predicate(op: crate::hir::HirBinaryOpKind) -> Option<Predicate> {
    use crate::hir::HirBinaryOpKind::*;
    match op {
        Eq => Some(Predicate::Eq),
        Lt => Some(Predicate::Lt),
        Le => Some(Predicate::Le),
        _ => None,
    }
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    let (compare, values) = crate::hir::luau_inlining::parameter_writeback_template(proto)?;
    let body = facts.parameter_writeback_body()?;
    (predicate(compare.op) == Some(body.predicate)
        && values
            .iter()
            .zip(&body.values)
            .all(|(a, b)| Literal::from_expr(a).as_ref() == Some(b)))
    .then(|| body.clone())
}

struct Candidate<'a> {
    frame: &'a Frame,
    callee: &'a Callee,
    initial: HirBinding,
    value: HirExpr,
    arguments: [LocalId; 2],
    result: LocalId,
    start: usize,
    sink: usize,
}

fn candidates<'a>(
    proto: &HirProto,
    facts: &'a ProtoPromotionFacts,
    callees: &'a Callees,
    bodies: &[Option<Body>],
) -> Vec<Candidate<'a>> {
    let mut templates = BTreeMap::new();
    for callee in callees.values() {
        if let HirLuauInliningBody::ParameterWriteback { template } = callee.body
            && let Some(body) = &bodies[template]
        {
            templates
                .entry(body.program.shape.clone())
                .and_modify(|entry| *entry = None)
                .or_insert(Some(callee));
        }
    }
    let frames = facts
        .parameter_writeback_frames()
        .map(|frame| {
            (
                crate::transformer::InstrRef(frame.region.source.index() + 1),
                frame,
            )
        })
        .collect::<BTreeMap<_, _>>();
    if templates.is_empty() || frames.is_empty() {
        return Vec::new();
    }
    let uses = ValueUses::new(proto);
    let mut points = Vec::new();
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        points.push((kind == PointKind::Statement).then_some((index, stmt)));
    });
    let mut output = Vec::new();
    for window in points
        .windows(2)
        .chain(points.windows(3))
        .chain(points.windows(4))
    {
        let candidate = (|| {
            let (start, initial_stmt) = window[0]?;
            let (initial, initial_value) = scalar_binding(initial_stmt)?;
            let (_, next) = window[1]?;
            let (_, expression) = scalar_local(next)?;
            let (compare, selected, result) = match (window.len(), expression) {
                (2, value) => {
                    let (HirExpr::Binary(compare), values) =
                        crate::hir::luau_inlining::selection(value)?
                    else {
                        return None;
                    };
                    (compare.as_ref(), values, scalar_local(next)?.0)
                }
                (3, value) => {
                    let HirBinding::Local(local) = initial else {
                        return None;
                    };
                    let (HirExpr::Binary(compare), values) =
                        crate::hir::luau_inlining::selection(value)?
                    else {
                        return None;
                    };
                    let (_, sink) = window[2]?;
                    let (result, last) = scalar_local(sink)?;
                    if scalar_local(next)?.0 != local || *last != HirExpr::LocalRef(local) {
                        return None;
                    }
                    (compare.as_ref(), values, result)
                }
                (4, HirExpr::Binary(compare)) => {
                    let HirBinding::Local(local) = initial else {
                        return None;
                    };
                    if scalar_local(next)?.0 != local {
                        return None;
                    }
                    let (_, selection) = window[2]?;
                    let (target, value) = scalar_local(selection)?;
                    let (input, values) = crate::hir::luau_inlining::selection(value)?;
                    let (_, sink) = window[3]?;
                    let (result, last) = scalar_local(sink)?;
                    if target != local
                        || *input != HirExpr::LocalRef(local)
                        || *last != HirExpr::LocalRef(local)
                    {
                        return None;
                    }
                    (compare.as_ref(), values, result)
                }
                _ => return None,
            };
            let frame = *frames.get(&compare.source_site?.instr)?;
            let callee = (*templates.get(&frame.body.program.shape)?)?;
            let expected = bodies[callee.child.index()].as_ref()?;
            let mapping = expected.program.register_mapping(&frame.body.program)?;
            if mapping.get(&crate::transformer::Reg(0)) != Some(&frame.parameter_home)
                || Literal::from_expr(initial_value).as_ref() != Some(&frame.initial_value)
                || predicate(compare.op) != Some(frame.body.predicate)
                || !selected
                    .iter()
                    .zip(&frame.body.values)
                    .all(|(a, b)| Literal::from_expr(a).as_ref() == Some(b))
                || !window
                    .iter()
                    .all(|point| point.is_some_and(|(_, stmt)| calling_values::scalar_write(stmt)))
            {
                return None;
            }
            let [left, right] = frame.argument_homes;
            let inputs = [
                *frame.region.inputs.get(&left)?,
                *frame.region.inputs.get(&right)?,
            ];
            let arguments = [
                facts.promoted_local_for_temp(inputs[0])?,
                facts.promoted_local_for_temp(inputs[1])?,
            ];
            let base = facts.trusted_temp_home_slot(frame.region.result)?;
            if compare.lhs != HirExpr::LocalRef(arguments[0])
                || compare.rhs != HirExpr::LocalRef(arguments[1])
                || facts.promoted_local_for_temp(frame.region.result) != Some(result)
                || facts.trusted_local_home_slot(result) != Some(base)
                || arguments.iter().any(|&local| uses.writes(local) != 1)
                || inputs
                    .iter()
                    .any(|&input| !facts.temp_definition_reference_unaliased(input))
                || callee.creation.instr >= frame.region.source
                || !matches!(window.last()?.as_ref()?.1, HirStmt::LocalDecl(_))
            {
                return None;
            }
            let expected_reads = window.len() - 2;
            if uses.binding_reads(initial, 0, uses.count) != expected_reads
                || uses.binding_writes(initial) != window.len() - 1
                || match initial {
                    HirBinding::Temp(temp) => {
                        temp != frame.initial
                            || proto.temp_debug_locals[temp.index()].is_some()
                            || proto.temp_debug_scopes[temp.index()].is_some()
                    }
                    HirBinding::Local(local) => {
                        facts.promoted_local_for_temp(frame.initial) != Some(local)
                    }
                    _ => true,
                }
            {
                return None;
            }
            Some(Candidate {
                frame,
                callee,
                initial,
                value: initial_value.clone(),
                arguments,
                result,
                start,
                sink: window.last()?.as_ref()?.0,
            })
        })();
        output.extend(candidate);
    }
    output
}

pub(super) fn debug_arguments(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
    bodies: &[Option<Body>],
    parameter_names: &[Option<String>],
) -> Option<(HirProto, Vec<(crate::hir::HirSourceSite, LocalId)>)> {
    let candidates = candidates(proto, facts, callees, bodies);
    let mut draft = None;
    let mut obligations = Vec::new();
    for candidate in candidates {
        let HirBinding::Local(local) = candidate.initial else {
            continue;
        };
        if proto.local_debug_hints[local.index()].is_none()
            && proto.local_debug_scopes[local.index()].is_none()
        {
            continue;
        }
        let scope = proto
            .debug_scopes
            .get(proto.local_debug_scopes[local.index()]?)?
            .as_ref()?;
        if scope.initializer_end_instr != Some(candidate.frame.region.source)
            || scope.end_instr != Some(candidate.frame.region.end)
            || scope.initializer_temp != Some(candidate.frame.initial)
            || proto.local_debug_hints[local.index()].is_none()
            || proto.local_debug_hints[local.index()]
                != parameter_names[candidate.callee.child.index()]
        {
            return None;
        }
        let draft = draft.get_or_insert_with(|| proto.clone());
        draft.local_debug_hints[local.index()] = None;
        draft.local_debug_scopes[local.index()] = None;
        draft.temp_debug_locals[candidate.frame.initial.index()] = None;
        draft.temp_debug_scopes[candidate.frame.initial.index()] = None;
        obligations.push((
            crate::hir::HirSourceSite {
                proto: proto.id,
                instr: candidate.frame.region.source,
            },
            candidate.callee.local,
        ));
    }
    draft.map(|proto| (proto, obligations))
}

pub(super) fn plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    bodies: &[Option<Body>],
) -> Vec<Plan> {
    let Some(callees) = context.expanded_callees else {
        return Vec::new();
    };
    candidates(context.proto, facts, callees, bodies)
        .into_iter()
        .filter_map(|candidate| {
            if let HirBinding::Local(local) = candidate.initial
                && (context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some())
            {
                return None;
            }
            let base = facts.trusted_temp_home_slot(candidate.frame.region.result)?;
            let source = crate::hir::HirSourceSite {
                proto: context.proto.id,
                instr: candidate.frame.region.source,
            };
            let mut plan = factories::invocation(
                candidate.callee,
                source,
                base,
                candidate.result,
                candidate.start,
                candidate.sink,
            );
            plan.values = vec![factories::factory_call(
                candidate.callee.local,
                Some(source),
                vec![
                    candidate.value,
                    HirExpr::LocalRef(candidate.arguments[0]),
                    HirExpr::LocalRef(candidate.arguments[1]),
                ]
                .into(),
            )]
            .into();
            Some(plan)
        })
        .collect()
}
