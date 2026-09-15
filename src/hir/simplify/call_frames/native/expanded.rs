//! 恢复已在 caller 中展开的高输入、低结果构造帧。
//!
//! 原 allocation/字段/调用事实仍由共享 FrameBuilder 消费；本模块仅组织参数的临时
//! 绑定区及整批后缀。先在 B+1 计算 input，再在 B 分配结果，开放缓冲从 B+2 开始。
//! 例如已展开的 `build({values={1,2}})` 不能改成先分配结果的普通构造器，也不能
//! 提前声明 B。只有现存闭包的封闭函数体逐节点相等时才选择它作为源码表达；该调用
//! 必须消失的义务传给 Generate，不假称原字节码保留了被优化掉的 CALL 身份。

use super::*;
use crate::hir::common::{HirModule, HirRequiredLuauInlining, HirTableConstructor};
use crate::hir::simplify::table_constructors::{ConstructorWrite, constructor_write};

struct Callee {
    local: LocalId,
    child: crate::hir::HirProtoRef,
    declaration: usize,
    field: crate::LuaString,
}

pub(in crate::hir::simplify) fn restore(
    module: &mut HirModule,
    promotion: &[ProtoPromotionFacts],
    dialect: DecompileDialect,
) {
    if dialect != DecompileDialect::Luau {
        return;
    }
    // 每个 proto 的 body 形状只读一次；参数替换不比较或复制整个模块。
    let bodies = module.protos.iter().map(body_key).collect::<Vec<_>>();
    for proto in &mut module.protos {
        // 当前后缀证书采用根直线坐标，不把 DFS 序号当作路径或词法区间。
        if proto.id != module.entry
            || !proto.params.is_empty()
            || proto.body.stmts.iter().any(|stmt| {
                !matches!(
                    stmt,
                    HirStmt::LocalDecl(_)
                        | HirStmt::Assign(_)
                        | HirStmt::CallStmt(_)
                        | HirStmt::TableSetList(_)
                        | HirStmt::Return(_)
                )
            })
        {
            continue;
        }
        let Some(facts) = promotion.get(proto.id.index()) else {
            continue;
        };
        let callees = callees(proto, &bodies);
        if callees.is_empty() {
            continue;
        }
        let restrictions = frame_restrictions(proto, facts);
        let context = NativeFrameContext {
            proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            constants_fit_rk: tables::constants_fit_rk(proto),
        };
        let mut expanded = Vec::new();
        let mut certificates = BTreeMap::<LocalId, HirRequiredLuauInlining>::new();
        let mut start = 0;
        for (sink, stmt) in proto.body.stmts.iter().enumerate() {
            let Some(ConstructorWrite::Batch { batch, .. }) = constructor_write(stmt) else {
                if scalar_local(stmt).is_none() && constructor_write(stmt).is_none() {
                    start = sink + 1;
                }
                continue;
            };
            let run = proto.body.stmts[start..=sink].iter().collect::<Vec<_>>();
            if let Some((mut plan, callee)) =
                candidate(context, facts, &run, &callees, start, batch)
            {
                plan.start += start;
                plan.sink = sink;
                plan.removed = (plan.start..sink).collect();
                let certificate =
                    certificates
                        .entry(callee.local)
                        .or_insert_with(|| HirRequiredLuauInlining {
                            owner: proto.id,
                            callee: callee.local,
                            child: callee.child,
                            field: callee.field.clone(),
                            results: Vec::new(),
                        });
                certificate.results.extend(&plan.result_locals);
                expanded.push(plan);
            }
            // 每个批次至多消费一个直线窗口，不对窗口内的 seed 逐个重试。
            start = sink + 1;
        }
        if expanded.is_empty() {
            continue;
        }
        let first = expanded[0].start;
        let occupied = expanded
            .iter()
            .flat_map(|plan| plan.start..=plan.sink)
            .collect::<BTreeSet<_>>();
        let (mut plans, count) = collect_native_plans(context, facts, dialect);
        plans.retain(|plan| {
            !occupied.contains(&plan.sink)
                && plan.removed.iter().all(|index| !occupied.contains(index))
        });
        plans.extend(expanded);
        plans.sort_unstable_by_key(|plan| plan.sink);
        let Ok(mut preview) = build_preview(proto, &plans, count) else {
            continue;
        };
        // 高输入留下的原根不在调用末端释放。保守地要求整个剩余直线后缀都由原帧
        // 重发直到原 RETURN；不把同槽的新值或 FASTCALL fallback 当作提前退休证明。
        if !suffix_replayed(&preview, &plans, first, facts) {
            continue;
        }
        let Ok(mut preserved) = validate_plan_batch(
            &mut preview,
            &plans,
            facts,
            dialect,
            proto.id == module.entry,
        ) else {
            continue;
        };
        preserved.extend(
            plans
                .iter()
                .flat_map(|plan| plan.result_locals.iter().copied()),
        );
        preserved.extend(certificates.keys().copied());
        compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
        for local in preserved {
            preview
                .proto
                .inline_dispositions
                .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        }
        *proto = preview.proto;
        module
            .required_luau_inlining
            .extend(certificates.into_values());
    }
}

fn callees(
    proto: &HirProto,
    bodies: &[Option<crate::LuaString>],
) -> BTreeMap<crate::LuaString, Callee> {
    let mut reads = BTreeSet::new();
    let mut writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
            BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    reads.insert(local);
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *writes.entry(local).or_default() += 1;
                }
            }),
        ),
    );
    let mut candidates = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            continue;
        };
        if !matches!(stmt, HirStmt::LocalDecl(_))
            || !closure.captures.is_empty()
            || reads.contains(&local)
            || writes.get(&local) != Some(&1)
        {
            continue;
        }
        let Some(Some(key)) = bodies.get(closure.proto.index()) else {
            continue;
        };
        if candidates
            .insert(
                key.clone(),
                Callee {
                    local,
                    child: closure.proto,
                    declaration: index,
                    field: key.clone(),
                },
            )
            .is_some()
        {
            ambiguous.insert(key.clone());
        }
    }
    candidates.retain(|key, _| !ambiguous.contains(key));
    candidates
}

fn body_key(proto: &HirProto) -> Option<crate::LuaString> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let table = match proto.body.stmts.as_slice() {
        [HirStmt::Return(ret)] => single_table(&ret.values)?,
        [decl, HirStmt::Return(ret)] => {
            let (local, HirExpr::TableConstructor(table)) = scalar_local(decl)? else {
                return None;
            };
            if ret.values.tail.is_some() || ret.values.fixed != [HirExpr::LocalRef(local)] {
                return None;
            }
            table
        }
        _ => return None,
    };
    table_key(table, &HirExpr::ParamRef(proto.params[0])).cloned()
}

fn single_table(values: &HirValuePack) -> Option<&HirTableConstructor> {
    match (values.fixed.as_slice(), &values.tail) {
        ([HirExpr::TableConstructor(table)], None) => Some(table),
        _ => None,
    }
}

fn table_key<'a>(table: &'a HirTableConstructor, input: &HirExpr) -> Option<&'a crate::LuaString> {
    if !table.fields.is_empty() {
        return None;
    }
    let tail = table.trailing_multivalue.as_ref()?;
    if tail.exact_width().is_some() {
        return None;
    }
    let HirExpr::Call(call) = tail.as_expr() else {
        return None;
    };
    let HirExpr::TableAccess(callee) = &call.callee else {
        return None;
    };
    if !matches!(&callee.base, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("table"))
        || !matches!(&callee.key, HirExpr::String(key) if key.as_utf8() == Some("unpack"))
        || call.is_method()
        || call.args.tail.is_some()
    {
        return None;
    }
    let [HirExpr::LogicalOr(logical)] = call.args.fixed.as_slice() else {
        return None;
    };
    let (HirExpr::TableAccess(access), HirExpr::TableConstructor(empty)) =
        (&logical.lhs, &logical.rhs)
    else {
        return None;
    };
    if &access.base != input || !empty.fields.is_empty() || empty.trailing_multivalue.is_some() {
        return None;
    }
    let HirExpr::String(key) = &access.key else {
        return None;
    };
    key.as_utf8()
        .filter(|key| DecompileDialect::Luau.is_identifier_name(key))?;
    Some(key)
}

fn candidate<'a>(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    run: &[&HirStmt],
    callees: &'a BTreeMap<crate::LuaString, Callee>,
    offset: usize,
    batch: &crate::hir::common::HirTableSetList,
) -> Option<(Plan, &'a Callee)> {
    let HirExpr::LocalRef(result) = batch.base else {
        return None;
    };
    let layout = facts.native_table_batch_layout(batch)?;
    let base = layout.base;
    if facts.trusted_local_home_slot(result) != Some(base) {
        return None;
    }
    if layout.buffer.slot() != base.slot() + 2 || !batch.values.fixed.is_empty() {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, DecompileDialect::Luau, base.slot())?;
    let seed = builder.definition(result, run.len())?;
    let (_, HirExpr::TableConstructor(table)) = scalar_local(run[seed])? else {
        return None;
    };
    let HirExpr::Call(call) = batch.values.tail.as_ref()?.as_expr() else {
        return None;
    };
    let [arg] = call.args.fixed.as_slice() else {
        return None;
    };
    let resolve = |value: &'_ HirExpr| -> Option<HirExpr> {
        match value {
            HirExpr::LocalRef(local) => Some(
                scalar_local(run[builder.definition(*local, run.len())?])?
                    .1
                    .clone(),
            ),
            value => Some(value.clone()),
        }
    };
    let HirExpr::LogicalOr(logical) = resolve(arg)? else {
        return None;
    };
    let HirExpr::TableAccess(access) = resolve(&logical.lhs)? else {
        return None;
    };
    let HirExpr::LocalRef(input) = access.base else {
        return None;
    };
    let HirExpr::String(key) = &access.key else {
        return None;
    };
    let callee = callees.get(key)?;
    let input_seed = builder.definition(input, seed)?;
    let home = HomeSlotKey::new(base.slot() + 1, 0);
    if callee.declaration >= offset + input_seed
        || facts.trusted_local_home_slot(input) != Some(home)
        || facts.trusted_local_home_slot(callee.local)?.slot() >= base.slot()
        || !matches!(
            scalar_local(run[input_seed])?.1,
            HirExpr::TableConstructor(_)
        )
    {
        return None;
    }
    let input_value = builder.expr(
        &HirExpr::LocalRef(input),
        seed,
        home.slot(),
        None,
        false,
        true,
        None,
    )?;
    if builder.next_event != seed {
        return None;
    }
    // 这两个槽仅是已求值的参数和低结果预留区，不修改计划的源码前缀 base。
    builder.base = base.slot() + 2;
    builder.constructor_reserved_top = Some(base.slot() + 2);
    let HirExpr::TableConstructor(body) = builder.constructor(seed, table, base.slot())? else {
        return None;
    };
    if builder.next_event != run.len() || table_key(&body, &HirExpr::LocalRef(input)) != Some(key) {
        return None;
    }
    let mut call = match body.trailing_multivalue.as_ref()?.as_expr() {
        HirExpr::Call(call) => (**call).clone(),
        _ => return None,
    };
    call.source_site = None;
    call.callee = HirExpr::LocalRef(callee.local);
    call.args = vec![input_value].into();
    call.fastcall = None;
    call.method_key = None;
    call.callee_root_handoff = None;
    call.method_rewrite_transaction = None;
    call.plain_method_syntax = false;
    call.argument_roots.clear();
    call.frame_root_ends.clear();
    Some((
        Plan {
            start: builder.first_event?,
            sink: run.len() - 1,
            base,
            values: vec![HirExpr::Call(Box::new(call))].into(),
            result_locals: vec![result],
            discarded_result: None,
            assignment_targets: Vec::new(),
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            removed: Vec::new(),
        },
        callee,
    ))
}

fn suffix_replayed(
    preview: &Preview,
    plans: &[Plan],
    first: usize,
    facts: &ProtoPromotionFacts,
) -> bool {
    let sinks = plans.iter().map(|plan| plan.sink).collect::<BTreeSet<_>>();
    let mut returned = false;
    for (index, stmt) in preview.proto.body.stmts.iter().enumerate().skip(first) {
        if preview.removed[index] || sinks.contains(&index) {
            continue;
        }
        if let HirStmt::Return(ret) = stmt {
            if !ret.values.is_empty() || facts.native_return_frame(ret).is_none() {
                return false;
            }
            returned = true;
        } else {
            return false;
        }
    }
    returned
}
