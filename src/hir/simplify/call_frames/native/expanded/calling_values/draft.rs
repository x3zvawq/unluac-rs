//! 把已完整配对的调用体和复制的 debug 身份投影到未发布草稿。
//! 单值参数预写交给共享 FrameBuilder，双返回交给完整计划；每个投影必须取得 occurrence 证书才能发布。

use super::*;
use crate::transformer::InstrRef;

pub(in crate::hir::simplify::call_frames::native::expanded) struct Prepared {
    pub proto: HirProto,
    pub(super) invocations: Vec<index::Invocation>,
    pub(super) pairs: Vec<index::PairInvocation>,
    pub(super) nil: Vec<index::NilInvocation>,
    pub(super) shared: Vec<index::SharedInvocation>,
    pub(super) observed: Vec<observed::Invocation>,
    pub(super) anonymous: Vec<anonymous::Invocation>,
}

pub(in crate::hir::simplify::call_frames::native::expanded) fn prepare(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    templates: &index::Templates,
) -> Option<Prepared> {
    let index::Invocations {
        values: invocations,
        pairs,
        nil,
        shared,
    } = index::invocations(proto, facts, templates);
    let observed = observed::invocations(proto, facts, templates);
    let anonymous = anonymous::invocations(proto, facts, templates);
    if invocations.is_empty()
        && pairs.is_empty()
        && nil.is_empty()
        && shared.is_empty()
        && observed.is_empty()
        && anonymous.is_empty()
    {
        return None;
    }
    let mut draft = prefixes::prepare(proto, facts);
    shared::prepare(&mut draft, proto, facts, templates, &shared)?;
    observed::prepare(&mut draft, proto, facts, templates, &observed)?;
    anonymous::prepare(&mut draft, proto, templates, &anonymous)?;
    let mut nil_replacements = BTreeMap::new();
    for invocation in &nil {
        let candidate = &invocation.candidate;
        if proto.local_debug_hints[candidate.value.index()].is_some()
            || proto.local_debug_scopes[candidate.value.index()].is_some()
        {
            let scope = proto
                .debug_scopes
                .get(proto.local_debug_scopes[candidate.value.index()]?)?
                .as_ref()?;
            let name = &templates.bodies[invocation.callee.child.index()]
                .as_ref()?
                .names[1];
            // 候选拒绝[PolicyBoundary:DebugIdentity]：只退休该原调用的形参副本，
            // 独立源码声明不能因当前值相同而失去 debug 身份。
            if scope.start_pc != candidate.source_pc
                || scope.end_instr != Some(candidate.end)
                || scope.initializer_temp != Some(candidate.value_input)
                || name.is_none()
                || &proto.local_debug_hints[candidate.value.index()] != name
            {
                return None;
            }
            draft.local_debug_hints[candidate.value.index()] = None;
            draft.local_debug_scopes[candidate.value.index()] = None;
            draft.temp_debug_locals[candidate.value_input.index()] = None;
            draft.temp_debug_scopes[candidate.value_input.index()] = None;
        }
        nil_replacements.insert(
            candidate.end,
            (
                candidate.result_local,
                candidate.value,
                factories::factory_call(
                    invocation.callee.local,
                    Some(candidate.source),
                    vec![
                        HirExpr::Nil,
                        HirExpr::LocalRef(candidate.value),
                        invocation
                            .reader
                            .as_ref()
                            .map_or(HirExpr::Nil, |reader| HirExpr::LocalRef(reader.local)),
                    ]
                    .into(),
                ),
            ),
        );
    }
    for invocation in &pairs {
        let candidate = &invocation.candidate;
        let body = templates.bodies[invocation.callee.child.index()].as_ref()?;
        let argument = candidate
            .argument
            .as_ref()
            .map(|arg| (arg.local, arg.input, arg.body_pc, &body.names[1]));
        for (local, input, pc, name) in argument.into_iter().chain([(
            candidate.item,
            candidate.item_value,
            candidate.item_pc,
            &body.item.as_ref()?.1,
        )]) {
            if proto.local_debug_hints[local.index()].is_none()
                && proto.local_debug_scopes[local.index()].is_none()
            {
                continue;
            }
            let scope = proto
                .debug_scopes
                .get(proto.local_debug_scopes[local.index()]?)?
                .as_ref()?;
            if scope.start_pc != pc
                || scope.end_instr != Some(candidate.end)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(input)
                || proto.local_debug_hints[local.index()].as_ref() != name.as_ref()
                || name.is_none()
            {
                return None;
            }
            draft.local_debug_hints[local.index()] = None;
            draft.local_debug_scopes[local.index()] = None;
            draft.temp_debug_locals[input.index()] = None;
            draft.temp_debug_scopes[input.index()] = None;
        }
    }
    let mut replacements = BTreeMap::new();
    for invocation in &invocations {
        let candidate = &invocation.candidate;
        let frame = facts.branch_value_frame(candidate.result)?;
        let result = frame
            .results
            .iter()
            .find(|result| result.value == candidate.result)?;
        let initial = result
            .incoming
            .iter()
            .find(|incoming| incoming.value == candidate.initial)?;
        let (HirBinding::Temp(flag), home) = initial.copy? else {
            return None;
        };
        let flag = facts.promoted_local_for_temp(flag)?;
        if facts.trusted_local_home_slot(flag) != Some(home) {
            return None;
        }
        let value = candidate.value;
        if proto.local_debug_hints[value.index()].is_some()
            || proto.local_debug_scopes[value.index()].is_some()
        {
            let scope = proto
                .debug_scopes
                .get(proto.local_debug_scopes[value.index()]?)?
                .as_ref()?;
            let body = templates.bodies[invocation.callee.child.index()].as_ref()?;
            if scope.start_pc != candidate.source_pc
                || scope.end_instr != Some(candidate.end)
                || scope.initializer_temp.or(scope.initializer_phi) != Some(candidate.value_input)
                || proto.local_debug_hints[value.index()].is_none()
                || proto.local_debug_hints[value.index()] != body.names[1]
            {
                return None;
            }
            draft.local_debug_hints[value.index()] = None;
            draft.local_debug_scopes[value.index()] = None;
            draft.temp_debug_locals[candidate.value_input.index()] = None;
            draft.temp_debug_scopes[candidate.value_input.index()] = None;
        }
        replacements.insert(
            InstrRef(candidate.source.instr.index() + 1),
            factories::factory_call(
                invocation.callee.local,
                Some(candidate.source),
                vec![
                    HirExpr::LocalRef(flag),
                    HirExpr::LocalRef(value),
                    HirExpr::LocalRef(invocation.reader.local),
                ]
                .into(),
            ),
        );
    }
    let mut count = 0;
    fn rewrite(
        block: &mut HirBlock,
        replacements: &BTreeMap<InstrRef, HirExpr>,
        count: &mut usize,
    ) {
        for stmt in &mut block.stmts {
            crate::hir::simplify::walk::for_each_nested_block_mut(stmt, &mut |child| {
                rewrite(child, replacements, count)
            });
            let HirStmt::If(branch) = stmt else { continue };
            let Some(value) = branch
                .predicate_source
                .and_then(|source| replacements.get(&source.instr))
            else {
                continue;
            };
            let Some(HirStmt::Assign(write)) = branch.then_block.stmts.last() else {
                continue;
            };
            let mut write = write.clone();
            write.values = vec![value.clone()].into();
            *stmt = HirStmt::Assign(write);
            *count += 1;
        }
    }
    rewrite(&mut draft.body, &replacements, &mut count);
    fn rewrite_nil(
        block: &mut HirBlock,
        replacements: &BTreeMap<InstrRef, (LocalId, LocalId, HirExpr)>,
        count: &mut usize,
    ) {
        for stmt in &mut block.stmts {
            crate::hir::simplify::walk::for_each_nested_block_mut(stmt, &mut |child| {
                rewrite_nil(child, replacements, count)
            });
        }
        for index in 1..block.stmts.len() {
            let call = match &block.stmts[index] {
                HirStmt::CallStmt(stmt) => Some(&stmt.call),
                stmt => scalar_local(stmt).and_then(|(_, value)| match value {
                    HirExpr::Call(call) => Some(call.as_ref()),
                    _ => None,
                }),
            };
            let Some(&(local, copied, ref value)) = call
                .and_then(|call| call.source_site)
                .and_then(|site| replacements.get(&site.instr))
            else {
                continue;
            };
            let previous = if matches!(block.stmts[index - 1], HirStmt::LocalRootRelease(released) if released == copied)
            {
                let Some(previous) = index.checked_sub(2) else {
                    continue;
                };
                &mut block.stmts[previous]
            } else {
                &mut block.stmts[index - 1]
            };
            if scalar_local(previous) != Some((local, &HirExpr::Nil)) {
                continue;
            }
            match previous {
                HirStmt::LocalDecl(decl) => decl.values = vec![value.clone()].into(),
                HirStmt::Assign(assign) => assign.values = vec![value.clone()].into(),
                _ => continue,
            }
            *count += 1;
        }
    }
    rewrite_nil(&mut draft.body, &nil_replacements, &mut count);
    (count == invocations.len() + nil.len()).then_some(Prepared {
        proto: draft,
        invocations,
        pairs,
        nil,
        shared,
        observed,
        anonymous,
    })
}
