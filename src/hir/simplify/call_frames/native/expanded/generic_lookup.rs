//! 配对被常量 guard 专化的遍历、查表退出和固定字符串返回。
//! 原准备槽与完整后缀一同验证；显式比较通过必须内联的调用保持原求值。

use super::*;
use crate::hir::common::{HirBinaryOpKind, HirOperationSources, ParamId};
use crate::hir::luau_inlining::small_integer;

fn iteration(
    for_: &crate::hir::common::HirGenericFor,
    input: &HirExpr,
    facts: &ProtoPromotionFacts,
    base: usize,
) -> bool {
    let Some(frame) = facts.generic_for_body_frame(for_) else {
        return false;
    };
    for_.iterator.fixed.as_slice() == std::slice::from_ref(input)
        && for_.iterator.tail.is_none()
        && for_.bindings.len() == 1
        && for_.body.stmts.is_empty()
        && frame
            .initializers
            .iter()
            .copied()
            .eq((base..base + 3).map(|slot| HomeSlotKey::new(slot, 0)))
        && frame.controls == frame.initializers
        && frame.bindings.as_slice() == [HomeSlotKey::new(base + 3, 0)]
        && frame.binding_padding == 1
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.params.len() != 2
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::While(loop_), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let (condition, negated) = synthetic_not_subject(&loop_.cond);
    let [HirStmt::GenericFor(for_), HirStmt::If(exit)] = loop_.body.stmts.as_slice() else {
        return None;
    };
    let HirExpr::TableAccess(lookup) = &exit.cond else {
        return None;
    };
    let ([HirExpr::String(result)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    if condition != &HirExpr::ParamRef(ParamId(0))
        || negated != 1
        || !iteration(for_, &HirExpr::ParamRef(ParamId(1)), facts, 2)
        || lookup.base != HirExpr::ParamRef(ParamId(1))
        || !matches!(exit.then_block.stmts.as_slice(), [HirStmt::Break])
        || exit.else_block.is_some()
        || ret.pending_cleanup_source.is_some()
    {
        return None;
    }

    Some((
        HirLuauInliningBody::GenericLookupWhile {
            template: proto.id.index(),
            key: small_integer(&lookup.key)?,
        },
        result.clone(),
    ))
}

fn leading_comparison(value: &HirExpr) -> Option<&crate::hir::common::HirBinaryExpr> {
    let HirExpr::LogicalAnd(and) = value else {
        return None;
    };
    let HirExpr::Binary(compare) = &and.lhs else {
        return None;
    };
    (compare.op == HirBinaryOpKind::Eq).then_some(compare)
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut templates = BTreeMap::new();
    for callee in context
        .expanded_callees
        .into_iter()
        .flat_map(|items| items.values())
    {
        if matches!(callee.body, HirLuauInliningBody::GenericLookupWhile { .. }) {
            templates
                .entry(callee.field.clone())
                .and_modify(|old| *old = None)
                .or_insert(Some(callee));
        }
    }

    if templates.is_empty() {
        return Vec::new();
    }

    let mut writes = BTreeMap::new();
    visit_stmts(
        &context.proto.body.stmts,
        &mut BindingWriteCollector(|binding| *writes.entry(binding).or_insert(0) += 1),
    );
    let mut plans = Vec::new();
    let mut definitions = BTreeMap::new();
    for (sink, stmt) in context.proto.body.stmts.iter().enumerate() {
        if let Some((binding, _)) = scalar_binding(stmt) {
            definitions.insert(binding, sink);
        }
        let initializer = (|| {
            let (result, HirExpr::String(value)) = scalar_local(stmt)? else {
                return None;
            };
            let start = sink.checked_sub(1)?;
            let (input, table @ HirExpr::TableConstructor(constructor)) =
                scalar_local(&context.proto.body.stmts[start])?
            else {
                return None;
            };
            let callee = *templates.get(value)?.as_ref()?;
            let base = facts.trusted_local_home_slot(result)?;
            let input_home = HomeSlotKey::new(base.slot() + 1, 0);
            let HirOperationSources::Single(site) = constructor.sources else {
                return None;
            };
            if start <= callee.declaration
                || !matches!(stmt, HirStmt::LocalDecl(_))
                || facts.trusted_local_home_slot(input) != Some(input_home)
                || facts.allocation_result_home(constructor) != Some(input_home)
                || !facts.allocation_result_reference_unaliased(constructor)
                || [input, result].iter().any(|local| {
                    context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some()
                })
                || [base, input_home]
                    .iter()
                    .any(|home| context.barred.contains(home) || context.closed.contains(home))
            {
                return None;
            }
            let mut builder =
                frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
            let argument = builder.expr(table, 0, input_home.slot(), None, false, true, None)?;
            let mut plan = factories::invocation(callee, site, base, result, start, sink);
            plan.values = vec![factories::factory_call(
                callee.local,
                Some(site),
                vec![HirExpr::Boolean(true), argument].into(),
            )]
            .into();
            Some(plan)
        })();
        plans.extend(initializer);
        let comparison = (|| {
            let HirStmt::CallStmt(statement) = stmt else {
                return None;
            };
            let call = &statement.call;
            let [value] = call.args.fixed.as_slice() else {
                return None;
            };
            let value = match value {
                HirExpr::LocalRef(local) => {
                    scalar_local(
                        &context.proto.body.stmts[*definitions.get(&HirBinding::Local(*local))?],
                    )?
                    .1
                }
                value => value,
            };
            let compare = leading_comparison(value)?;
            let HirExpr::String(returned) = &compare.lhs else {
                return None;
            };
            let callee = *templates.get(returned)?.as_ref()?;
            let HirLuauInliningBody::GenericLookupWhile { key, .. } = callee.body else {
                return None;
            };

            let prewrite = facts.boolean_argument_prewrite(call, 0)?;
            let initial_binding = facts
                .promoted_local_for_temp(prewrite.initial)
                .map(HirBinding::Local)
                .unwrap_or(HirBinding::Temp(prewrite.initial));
            let start = definitions.get(&initial_binding).copied().filter(|&index|
                matches!(scalar_binding(&context.proto.body.stmts[index]), Some((_, HirExpr::Boolean(value))) if *value == prewrite.initial_value)).unwrap_or(sink);
            // 只接受预写、可选循环、结果准备及 callee 的相邻固定窗口，
            // 不为每个候选重新扫描任意长的前缀。
            if sink - start > 4 {
                return None;
            }
            let frame = facts.native_fastcall_frame(call)?;
            let (producer, result_home) =
                facts.binary_operand_preparation(compare, 0, &compare.lhs)?;
            if start <= callee.declaration
                || call.args.tail.is_some()
                || !call
                    .fastcall
                    .is_some_and(|f| f.builtin() == 1 && f.fixed_is_direct(0))
                || frame.results != Some(ResultPack::Ignore)
                || !frame.arguments_unaliased
                || prewrite.initial_value
                || !prewrite.reference_uncaptured
                || prewrite.home != HomeSlotKey::new(frame.home.slot() + 1, 0)
                || result_home != HomeSlotKey::new(frame.home.slot() + 2, 0)
                || facts.native_binary_layout(compare)?.rhs.is_some()
                || !facts.temp_definition_reference_unaliased(producer)
            {
                return None;
            }
            let loop_index = start + 1;

            let (active, argument) = if loop_index < sink
                && let Some(HirStmt::Repeat(loop_)) = context.proto.body.stmts.get(loop_index)
            {
                let [HirStmt::GenericFor(for_)] = loop_.body.stmts.as_slice() else {
                    return None;
                };
                let HirExpr::TableAccess(lookup) = &loop_.cond else {
                    return None;
                };
                let HirExpr::LocalRef(input) = lookup.base else {
                    return None;
                };
                let home = facts.trusted_local_home_slot(input)?;
                let layout = facts.native_table_read_layout(lookup)?;
                // 候选拒绝[ProofIncomplete:Frame]：只读参数、空遍历及末端查表必须来自同一原槽，不能把循环外更新藏进调用。
                if small_integer(&lookup.key) != Some(key)
                    || layout.base != home
                    || layout.key.is_some()
                    || facts.table_read_result_home(lookup)
                        != Some(HomeSlotKey::new(frame.home.slot() + 3, 0))
                    || !iteration(for_, &lookup.base, facts, frame.home.slot() + 3)
                    || writes.get(&HirBinding::Local(input)) != Some(&1)
                    || !facts.local_definitions_reference_unaliased(input)
                    || home.slot() >= frame.home.slot()
                    || context.closed.contains(&home)
                {
                    return None;
                }
                (true, lookup.base.clone())
            } else {
                (false, HirExpr::Nil)
            };
            // 循环已逐项配对，完整参数 builder 消费其余原准备；循环在恢复调用中
            // 仍位于 Boolean 预写之后、返回常量 LOAD 与比较之前。
            let run = context.proto.body.stmts[start..sink]
                .iter()
                .enumerate()
                .filter(|(index, _)| !(active && *index == 1))
                .map(|(_, stmt)| stmt)
                .collect::<Vec<_>>();
            let mut builder = frame_builder(
                context,
                &run,
                facts,
                DecompileDialect::Luau,
                frame.home.slot(),
            )?;

            let mut restored =
                builder.call(call, run.len(), frame.home.slot(), false, CallWidth::Ignore)?;
            if builder.first_event != (!run.is_empty()).then_some(0)
                || builder.next_event != run.len()
            {
                return None;
            }
            let HirExpr::LogicalAnd(and) = &mut restored.args.fixed[0] else {
                return None;
            };
            let HirExpr::Binary(compare) = &mut and.lhs else {
                return None;
            };
            let site = compare.source_site?;
            compare.lhs = factories::factory_call(
                callee.local,
                Some(site),
                vec![HirExpr::Boolean(!active), argument].into(),
            );
            let mut plan = Plan {
                prefix_at_sink: false,
                luau_function_declaration: false,
                start,
                sink,
                base: frame.home,
                values: vec![HirExpr::Call(Box::new(restored))].into(),
                result_locals: Vec::new(),
                assignment_targets: Vec::new(),
                luau_compound_global: false,
                indexed_target: None,
                continuing_root: None,
                retained_copies: Vec::new(),
                replayed_effects: Vec::new(),
                removed: (start..sink).collect(),
            };
            if active {
                plan.replayed_effects.push(loop_index);
            }
            Some(plan)
        })();
        plans.extend(comparison);
    }
    plans
}
