//! 配对捕获状态、原迭代器模板和立即退出的 generic-for，恢复低槽调用结果。
//! 跨块结果先在未提交草稿内提升；仍须与其余展开帧共同通过完整前缀事务。

use super::*;
use crate::hir::common::{HirClosureCreation, HirClosureExpr, HirGenericFor};
use crate::hir::luau_inlining::small_integer;

fn iteration(
    for_: &HirGenericFor,
    iterator: LocalId,
    facts: &ProtoPromotionFacts,
    base: usize,
) -> bool {
    let Some(frame) = facts.generic_for_body_frame(for_) else {
        return false;
    };
    for_.iterator.fixed.as_slice() == [HirExpr::LocalRef(iterator)]
        && for_.iterator.tail.is_none()
        && for_.bindings.len() == 1
        && matches!(for_.body.stmts.as_slice(), [HirStmt::Break])
        && frame
            .initializers
            .iter()
            .copied()
            .eq((base..base + 3).map(|slot| HomeSlotKey::new(slot, 0)))
        && frame.controls == frame.initializers
        && frame.bindings == [HomeSlotKey::new(base + 3, 0)]
        // Luau 的通用迭代帧至少预留两个结果槽；单 binding 仍有一个 padding。
        && frame.binding_padding == 1
}

fn captured(closure: &HirClosureExpr, state: LocalId) -> Option<usize> {
    let Some(HirClosureCreation::Fresh { template }) = closure.creation else {
        return None;
    };
    matches!(closure.captures.as_slice(), [capture]
        if capture.mode == HirCaptureMode::ByReference && capture.binding == HirBinding::Local(state)).then_some(template)
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    protos: &[HirProto],
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || proto.children.len() != 1
        || proto.failure.is_some()
    {
        return None;
    }
    let [
        first,
        second,
        HirStmt::GenericFor(for_),
        HirStmt::Return(ret),
    ] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (state, value) = scalar_local(first)?;
    let (iterator, HirExpr::Closure(closure)) = scalar_local(second)? else {
        return None;
    };
    let child = protos.get(closure.proto.index())?;
    if facts.trusted_local_home_slot(state) != Some(HomeSlotKey::new(0, 0))
        || facts.trusted_local_home_slot(iterator) != Some(HomeSlotKey::new(1, 0))
        || facts.operation_result_home(closure.source_site?) != Some(HomeSlotKey::new(1, 0))
        || !iteration(for_, iterator, facts, 2)
        || !child.params.is_empty()
        || child.signature.is_vararg
        || child.upvalues.as_slice() != [crate::hir::UpvalueId(0)]
        || !child.mutable_upvalues.contains(&crate::hir::UpvalueId(0))
        || ret.values.fixed.as_slice() != [HirExpr::LocalRef(state)]
        || ret.values.tail.is_some()
        || ret.pending_cleanup_source.is_some()
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 0 && pack.len == 1)
    {
        return None;
    }
    Some((
        HirLuauInliningBody::GenericBreak {
            template: proto.id.index(),
            iterator: captured(closure, state)?,
            initial: small_integer(value)?,
        },
        "".into(),
    ))
}

/// 仅返回事务草稿。调用方必须使用独立 facts 快照，且在整批验证通过后一起发布。
pub(super) fn prepare(
    original: &HirProto,
    facts: &mut ProtoPromotionFacts,
    bodies: &[Option<(HirLuauInliningBody, crate::LuaString)>],
) -> Option<HirProto> {
    let mut reads = BTreeMap::new();
    let mut writes = BTreeMap::new();
    visit_stmts(
        &original.body.stmts,
        &mut (
            BindingReadCollector(|binding| *reads.entry(binding).or_insert(0) += 1),
            BindingWriteCollector(|binding| *writes.entry(binding).or_insert(0) += 1),
        ),
    );
    let mut available = BTreeMap::new();
    for (index, stmt) in original.body.stmts.iter().enumerate() {
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            continue;
        };
        let Some(Some((
            HirLuauInliningBody::GenericBreak {
                iterator, initial, ..
            },
            _,
        ))) = bodies.get(closure.proto.index())
        else {
            continue;
        };
        if !matches!(stmt, HirStmt::LocalDecl(_))
            || !closure.captures.is_empty()
            || writes.get(&HirBinding::Local(local)) != Some(&1)
            || reads.contains_key(&HirBinding::Local(local))
        {
            continue;
        }
        available
            .entry((*iterator, *initial))
            .and_modify(|entry| *entry = None)
            .or_insert(Some((local, index)));
    }
    if available.is_empty() {
        return None;
    }
    let mut candidates = Vec::new();
    for (index, stmt) in original.body.stmts.iter().enumerate() {
        let candidate = (|| {
            let HirStmt::Block(block) = stmt else {
                return None;
            };
            let [
                first @ HirStmt::LocalDecl(_),
                second @ HirStmt::LocalDecl(_),
                HirStmt::GenericFor(for_),
                HirStmt::Assign(copy),
            ] = block.stmts.as_slice()
            else {
                return None;
            };
            let (state, value) = scalar_local(first)?;
            let (iterator, HirExpr::Closure(closure)) = scalar_local(second)? else {
                return None;
            };
            let template = captured(closure, state)?;
            let &(callee, declaration) = available
                .get(&(template, small_integer(value)?))?
                .as_ref()?;
            let ([HirLValue::Temp(result)], [HirExpr::LocalRef(source)], None) = (
                copy.targets.as_slice(),
                copy.values.fixed.as_slice(),
                &copy.values.tail,
            ) else {
                return None;
            };
            let home = facts.trusted_temp_home_slot(*result)?;
            let site = closure.source_site?;
            // 候选拒绝[ProofIncomplete:Identity]：原模板相同还不足以退休对象；完整 cell、唯一迭代读取和结果 COPY 必须一起消费。
            if declaration >= index
                || *source != state
                || copy.is_phi_transfer
                || copy.initializer_merge_transaction.is_some()
                || facts.is_phi_carrier_temp(*result)
                || !facts.temp_definition_reference_unaliased(*result)
                || home != HomeSlotKey::new(home.slot(), 0)
                || facts.trusted_local_home_slot(state)
                    != Some(HomeSlotKey::new(home.slot() + 1, 0))
                || facts.trusted_local_home_slot(iterator)
                    != Some(HomeSlotKey::new(home.slot() + 2, 0))
                || facts.operation_result_home(site) != Some(HomeSlotKey::new(home.slot() + 2, 0))
                || !facts.operation_result_reference_unaliased(site)
                || !iteration(for_, iterator, facts, home.slot() + 3)
                || reads.get(&HirBinding::Local(state)) != Some(&2)
                || reads.get(&HirBinding::Local(iterator)) != Some(&1)
                || writes.get(&HirBinding::Local(state)) != Some(&1)
                || writes.get(&HirBinding::Local(iterator)) != Some(&1)
                || writes.get(&HirBinding::Temp(*result)) != Some(&1)
                || writes.get(&HirBinding::Local(for_.bindings[0])) != Some(&1)
                || reads.contains_key(&HirBinding::Local(for_.bindings[0]))
                || [state, iterator, for_.bindings[0]].iter().any(|local| {
                    original.local_debug_hints[local.index()].is_some()
                        || original.local_debug_scopes[local.index()].is_some()
                })
                || original.temp_debug_scopes[result.index()].is_some()
                || original.temp_debug_locals[result.index()].is_some()
            {
                return None;
            }
            Some((index, *result, home, callee, site))
        })();
        candidates.extend(candidate);
    }
    if candidates.is_empty() {
        return None;
    }
    let mut proto = original.clone();
    let mut substitutions = BTreeMap::new();
    for (index, result, home, callee, site) in candidates {
        let local = LocalId(proto.local_count);
        proto.local_count += 1;
        proto.local_debug_hints.push(None);
        proto.local_debug_scopes.push(None);
        facts.record_local_home_slot(local, home);
        facts.record_temp_to_local_merge(result, local);
        proto
            .inline_dispositions
            .promote_temp_to_local(result, local);
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        substitutions.insert(result, HirExpr::LocalRef(local));
        proto.body.stmts[index] = HirStmt::LocalDecl(Box::new(HirLocalDecl {
            bindings: vec![local],
            values: vec![factories::factory_call(
                callee,
                Some(site),
                Vec::new().into(),
            )]
            .into(),
            initializer_merge_transaction: None,
            generic_for_initializer_producer: None,
        }));
    }
    for stmt in &mut proto.body.stmts {
        crate::hir::rewrite::replace_temps_in_stmt(stmt, &substitutions);
    }
    Some(proto)
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let by_local = context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
        .filter(|callee| matches!(callee.body, HirLuauInliningBody::GenericBreak { .. }))
        .map(|callee| (callee.local, callee))
        .collect::<BTreeMap<_, _>>();
    context
        .proto
        .body
        .stmts
        .iter()
        .enumerate()
        .filter_map(|(index, stmt)| {
            let (local, HirExpr::Call(call)) = scalar_local(stmt)? else {
                return None;
            };
            let HirExpr::LocalRef(callee) = call.callee else {
                return None;
            };
            let site = call.required_luau_inlining?;
            let callee = by_local.get(&callee)?;
            Some(factories::invocation(
                callee,
                site,
                facts.trusted_local_home_slot(local)?,
                local,
                index,
                index,
            ))
        })
        .collect()
}
