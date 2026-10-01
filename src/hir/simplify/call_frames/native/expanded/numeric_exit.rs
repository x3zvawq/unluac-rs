//! 将已展开的数值遍历和正常出口恢复为现存闭包调用。
//!
//! 消费完整函数体、只读捕获、原数组/循环/调用槽及私有出口标志，整批验证后发布强制内联要求。

use super::*;
use crate::hir::luau_inlining::{
    NumericExitTemplate, insert_tag, integer_one, numeric_exit_template,
};
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};

#[derive(Clone)]
struct Template {
    callee: LocalId,
    child: crate::hir::HirProtoRef,
    declaration: usize,
    capture: LocalId,
}

struct Candidate {
    argument: usize,
    flag: usize,
    result: TempId,
    home: HomeSlotKey,
    source: crate::hir::HirSourceSite,
    value: HirExpr,
    template: Template,
}

fn literal_result(
    stmts: &[HirStmt],
    value: &HirExpr,
    facts: &ProtoPromotionFacts,
) -> Option<TempId> {
    let first = stmts.first()?;
    let (temp, expression) = first.scalar_temp_assignment()?;
    if expression != value {
        return None;
    }
    let result = match stmts {
        [_] => temp,
        [_, HirStmt::Assign(copy)]
            if copy.is_phi_transfer
                && copy.values.tail.is_none()
                && copy.values.fixed.as_slice() == [HirExpr::TempRef(temp)] =>
        {
            let [HirLValue::Temp(result)] = copy.targets.as_slice() else {
                return None;
            };
            if facts.trusted_temp_home_slot(temp) != facts.trusted_temp_home_slot(*result) {
                return None;
            }
            *result
        }
        _ => return None,
    };
    facts.is_phi_carrier_temp(result).then_some(result)
}

fn event(
    stmt: &HirStmt,
    home: usize,
    facts: &ProtoPromotionFacts,
) -> Option<(LocalId, crate::LuaString)> {
    let HirStmt::CallStmt(stmt_) = stmt else {
        return None;
    };
    let [HirExpr::LocalRef(capture), _] = stmt_.call.args.fixed.as_slice() else {
        return None;
    };
    let tag = insert_tag(stmt, &HirExpr::LocalRef(*capture))?;
    let frame = facts.native_fastcall_frame(&stmt_.call)?;
    (frame.home == HomeSlotKey::new(home, 0)
        && frame.arguments_unaliased
        && matches!(frame.results, Some(crate::transformer::ResultPack::Ignore)))
    .then(|| (*capture, tag.clone()))
}

fn candidate(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    index: usize,
    flags: &BTreeMap<LocalId, usize>,
    templates: &BTreeMap<(LocalId, NumericExitTemplate), Option<Template>>,
) -> Option<Candidate> {
    let (argument, HirExpr::TableConstructor(table)) = scalar_local(proto.body.stmts.get(index)?)?
    else {
        return None;
    };
    let HirStmt::NumericFor(for_) = proto.body.stmts.get(index + 1)? else {
        return None;
    };
    let HirStmt::If(tail) = proto.body.stmts.get(index + 2)? else {
        return None;
    };
    let HirExpr::Unary(guard) = &tail.cond else {
        return None;
    };
    let HirExpr::LocalRef(flag) = guard.expr else {
        return None;
    };
    let flag_index = *flags.get(&flag)?;
    if flag_index >= index
        || guard.op != crate::hir::HirUnaryOpKind::Not
        || guard.source_site.is_some()
        || tail.else_block.is_some()
        || table.trailing_multivalue.is_some()
        || !table.implicit_template_fields.is_empty()
        || !table
            .fields
            .iter()
            .all(|field| matches!(field, crate::hir::HirTableField::Array(HirExpr::Boolean(_))))
        || proto.local_debug_hints[argument.index()].is_some()
        || proto.local_debug_scopes[argument.index()].is_some()
        || !integer_one(&for_.start)
        || !integer_one(&for_.step)
    {
        return None;
    }
    let argument_home = facts.trusted_local_home_slot(argument)?;
    let base = argument_home.slot().checked_sub(1)?;
    if argument_home != HomeSlotKey::new(base + 1, 0)
        || facts.allocation_result_home(table) != Some(argument_home)
        || for_.control_homes
            != [
                HomeSlotKey::new(base + 4, 0),
                HomeSlotKey::new(base + 2, 0),
                HomeSlotKey::new(base + 3, 0),
            ]
        || facts.trusted_local_home_slot(for_.binding) != Some(HomeSlotKey::new(base + 4, 0))
        || !matches!(&for_.limit, HirExpr::Unary(value)
            if value.op == crate::hir::HirUnaryOpKind::Length
                && value.expr == HirExpr::LocalRef(argument)
                && facts.unary_result_home(value) == Some(HomeSlotKey::new(base + 2, 0)))
    {
        return None;
    }
    let [HirStmt::If(branch)] = for_.body.stmts.as_slice() else {
        return None;
    };
    if branch.else_block.is_some() {
        return None;
    }
    let HirExpr::TableAccess(lookup) = &branch.cond else {
        return None;
    };
    if lookup.base != HirExpr::LocalRef(argument)
        || lookup.key != HirExpr::LocalRef(for_.binding)
        || facts.table_read_result_home(lookup) != Some(HomeSlotKey::new(base + 5, 0))
        || !facts
            .native_table_read_layout(lookup)
            .is_some_and(|layout| {
                layout.base == argument_home && layout.key == Some(HomeSlotKey::new(base + 4, 0))
            })
    {
        return None;
    }
    let (HirStmt::Break, hit_body) = branch.then_block.stmts.split_last()? else {
        return None;
    };
    let (flag_write, hit_body) = hit_body.split_last()?;
    if !matches!(scalar_local(flag_write), Some((target, HirExpr::Boolean(true))) if target == flag)
    {
        return None;
    }
    let (hit, hit_result) = hit_body.split_first()?;
    let (miss, miss_result) = tail.then_block.stmts.split_first()?;
    let (capture, hit) = event(hit, base + 5, facts)?;
    let (other_capture, miss) = event(miss, base + 2, facts)?;
    if capture != other_capture {
        return None;
    }
    let result = literal_result(hit_result, &HirExpr::Nil, facts)?;
    if literal_result(miss_result, &HirExpr::Boolean(false), facts)? != result
        || facts.trusted_temp_home_slot(result) != Some(HomeSlotKey::new(base, 0))
    {
        return None;
    }
    let template = templates
        .get(&(capture, NumericExitTemplate { hit, miss }))?
        .as_ref()?;
    if template.declaration >= index {
        return None;
    }
    let crate::hir::common::HirOperationSources::Single(source) = table.sources else {
        return None;
    };
    Some(Candidate {
        argument: index,
        flag: flag_index,
        result,
        home: HomeSlotKey::new(base, 0),
        source,
        value: HirExpr::TableConstructor(table.clone()),
        template: template.clone(),
    })
}

pub(super) fn restore(module: &mut HirModule, promotion: &mut [ProtoPromotionFacts]) {
    let templates = module
        .protos
        .iter()
        .map(numeric_exit_template)
        .collect::<Vec<_>>();
    if templates.iter().all(Option::is_none) {
        return;
    }
    let entry = module.entry.index();
    let Some(original_facts) = promotion.get(entry) else {
        return;
    };
    if !module.protos[entry].params.is_empty() {
        return;
    }
    let mut facts = original_facts.clone();
    let Some((mut proto, _)) = prepare_source_frames(
        module.protos[entry].clone(),
        &mut facts,
        DecompileDialect::Luau,
    ) else {
        return;
    };
    let mut writes = BTreeMap::<HirBinding, usize>::new();
    let mut reads = BTreeMap::<HirBinding, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut BindingWriteCollector(|binding| *writes.entry(binding).or_default() += 1),
    );
    visit_stmts(
        &proto.body.stmts,
        &mut BindingReadCollector(|binding| *reads.entry(binding).or_default() += 1),
    );
    let mut available = BTreeMap::new();
    let mut flags = BTreeMap::new();
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        let Some((local, value)) = scalar_local(stmt) else {
            continue;
        };
        if matches!(value, HirExpr::Boolean(false))
            && facts.local_has_no_physical_home(local)
            && proto.local_debug_hints[local.index()].is_none()
            && proto.local_debug_scopes[local.index()].is_none()
        {
            flags.insert(local, index);
        }
        let HirExpr::Closure(closure) = value else {
            continue;
        };
        let Some(body) = templates
            .get(closure.proto.index())
            .and_then(Option::as_ref)
        else {
            continue;
        };
        let [capture] = closure.captures.as_slice() else {
            continue;
        };
        let HirBinding::Local(capture_local) = capture.binding else {
            continue;
        };
        if capture.mode != HirCaptureMode::ByValue
            || writes.get(&HirBinding::Local(capture_local)) != Some(&1)
            || writes.get(&HirBinding::Local(local)) != Some(&1)
            || reads.contains_key(&HirBinding::Local(local))
        {
            continue;
        }
        // 每个模板/捕获键只保留唯一闭包，不逐循环枚举全部函数体。
        let key = (capture_local, body.clone());
        let template = Template {
            callee: local,
            child: closure.proto,
            declaration: index,
            capture: capture_local,
        };
        available
            .entry(key)
            .and_modify(|known| *known = None)
            .or_insert(Some(template));
    }
    if available.is_empty() {
        return;
    }
    let candidates = (0..proto.body.stmts.len())
        .filter_map(|index| candidate(&proto, &facts, index, &flags, &available))
        .collect::<Vec<_>>();
    if candidates.is_empty() {
        return;
    }
    let mut removed = BTreeSet::new();
    let mut results = BTreeMap::new();
    for candidate in &candidates {
        if results
            .insert(candidate.result, candidate.argument)
            .is_some()
        {
            return;
        }
        for index in [
            candidate.flag,
            candidate.argument,
            candidate.argument + 1,
            candidate.argument + 2,
        ] {
            if !removed.insert(index) {
                return;
            }
        }
    }
    let mut retired = BTreeSet::new();
    for &index in &removed {
        visit_stmts(
            std::slice::from_ref(&proto.body.stmts[index]),
            &mut BindingWriteCollector(|binding| {
                if !matches!(binding, HirBinding::Temp(temp) if results.contains_key(&temp)) {
                    retired.insert(binding);
                }
            }),
        );
    }
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        if removed.contains(&index) {
            continue;
        }
        let mut invalid = false;
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingReadCollector(|binding| {
                invalid |= retired.contains(&binding)
                    || matches!(binding, HirBinding::Temp(temp) if results.get(&temp).is_some_and(|start| index < *start));
            }),
        );
        visit_stmts(
            std::slice::from_ref(stmt),
            &mut BindingWriteCollector(|binding| {
                invalid |= retired.contains(&binding)
                    || matches!(binding, HirBinding::Temp(temp) if results.contains_key(&temp));
            }),
        );
        if invalid {
            return;
        }
    }
    let mut substitutions = BTreeMap::new();
    let mut replacements = BTreeMap::new();
    let mut certificates = BTreeMap::<LocalId, HirRequiredLuauInlining>::new();
    for candidate in candidates {
        let local = LocalId(proto.local_count);
        proto.local_count += 1;
        proto
            .local_debug_hints
            .push(proto.temp_debug_locals[candidate.result.index()].clone());
        proto
            .local_debug_scopes
            .push(proto.temp_debug_scopes[candidate.result.index()]);
        facts.record_local_home_slot(local, candidate.home);
        facts.record_temp_to_local_merge(candidate.result, local);
        proto
            .inline_dispositions
            .promote_temp_to_local(candidate.result, local);
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        substitutions.insert(candidate.result, HirExpr::LocalRef(local));
        replacements.insert(
            candidate.argument,
            HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: vec![factories::factory_call(
                    candidate.template.callee,
                    Some(candidate.source),
                    vec![candidate.value].into(),
                )]
                .into(),
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
            })),
        );
        let certificate = certificates
            .entry(candidate.template.callee)
            .or_insert_with(|| HirRequiredLuauInlining {
                owner: proto.id,
                callee: candidate.template.callee,
                child: candidate.template.child,
                body: HirLuauInliningBody::NumericForExit {
                    template: candidate.template.child.index(),
                },
                field: "".into(),
                capture: Some(candidate.template.capture),
                occurrences: Vec::new(),
                result_frame_slots: BTreeMap::new(),
            });
        certificate.occurrences.push(candidate.source);
        certificate
            .result_frame_slots
            .insert(candidate.source, candidate.home.slot());
    }
    proto.body.stmts = std::mem::take(&mut proto.body.stmts)
        .into_iter()
        .enumerate()
        .filter_map(|(index, stmt)| {
            replacements
                .remove(&index)
                .or_else(|| (!removed.contains(&index)).then_some(stmt))
        })
        .collect();
    for stmt in &mut proto.body.stmts {
        crate::hir::rewrite::replace_temps_in_stmt(stmt, &substitutions);
    }
    let Some((mut proto, _)) = prepare_source_frames(proto, &mut facts, DecompileDialect::Luau)
    else {
        return;
    };
    let mut requests = BTreeMap::new();
    let mut count = 0;
    let mut valid = true;
    prefix::coordinates::visit(&proto.body, &mut count, &mut |index, kind, stmt| {
        if kind != PointKind::Statement {
            return;
        }
        let home = match stmt {
            HirStmt::LocalDecl(decl) if decl.bindings.len() == 1 => {
                facts.trusted_local_home_slot(decl.bindings[0])
            }
            HirStmt::CallStmt(call) => facts
                .native_call_frame(&call.call)
                .or_else(|| facts.native_fastcall_frame(&call.call))
                .map(|frame| frame.home),
            HirStmt::Return(ret)
                if ret.values.is_empty() && ret.pending_cleanup_source.is_none() =>
            {
                return;
            }
            _ => None,
        };
        if let Some(home) = home {
            requests.insert(
                index,
                prefix::PrefixRequest {
                    home,
                    required: BTreeSet::new(),
                },
            );
        } else {
            valid = false;
        }
    });
    if !valid {
        return;
    }
    let Ok(preserved) = prefix::validate_prefixes(
        &proto,
        &facts,
        DecompileDialect::Luau,
        true,
        &vec![false; count],
        &requests,
        false,
    ) else {
        return;
    };
    for local in preserved.into_iter().chain(certificates.keys().copied()) {
        proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    module.protos[entry] = proto;
    promotion[entry] = facts;
    module
        .required_luau_inlining
        .extend(certificates.into_values());
}
