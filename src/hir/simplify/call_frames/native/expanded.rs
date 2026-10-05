//! 恢复已在 caller 中展开的高输入、低结果帧。
//!
//! 原 allocation/字段/调用事实仍由共享 FrameBuilder 消费；本模块仅组织参数的临时
//! 绑定区及整批后缀。构造和索引结果均保留原输入分配、调用与低槽写回次序。
//! 只有现存闭包的封闭函数体逐节点相等时才选择它作为源码表达；该调用
//! 必须消失的义务传给 Generate，不假称原字节码保留了被优化掉的 CALL 身份。

use super::*;
use crate::hir::common::{
    HirLuauInliningBody, HirModule, HirRequiredLuauInlining, HirTableConstructor,
};
use crate::hir::simplify::table_constructors::{ConstructorWrite, constructor_write};

mod branch_arguments;
mod calling_values;
mod value_uses;
pub(in crate::hir::simplify::call_frames) use calling_values::Frames as CallingValueFrames;
mod captured;
mod captured_transfers;
pub(in crate::hir::simplify::call_frames) use captured_transfers::Frames as CapturedTransferFrames;
mod captured_predicates;
mod conditional_methods;
mod constant_control;
pub(in crate::hir::simplify::call_frames) use constant_control::Frames as ConstantControlFrames;
mod control;
mod counter_repeat;
mod counter_while;
mod expression_loops;
mod factories;
mod generic_break;
mod generic_counter;
mod generic_lookup;
mod literal_choices;
pub(in crate::hir::simplify::call_frames) use literal_choices::ComparedCallees;
mod parameter_writebacks;
mod seeded_predicates;
pub(in crate::hir::simplify::call_frames) use seeded_predicates::Prepared as SeededPredicateFrames;
pub(in crate::hir::simplify) use seeded_predicates::preserve_outputs as preserve_seeded_predicate_outputs;
mod value_expressions;
pub(in crate::hir::simplify::call_frames) use value_expressions::Frames as ValueExpressionFrames;
mod array_fold;
mod guarded_counter;
mod nested_search;
mod numeric_exit;
mod numeric_repeat;
mod published_tables;
mod repeat_lookup;
mod repeat_prefix;
mod reset_counter;
mod returned_calls;
mod stateful_generic;
pub(super) fn is_expanded_table_write(context: NativeFrameContext<'_>, stmt: &HirStmt) -> bool {
    published_tables::is_publication(context, stmt) || captured_transfers::is_append(context, stmt)
}
mod scalar;
mod snapshots;

pub(in crate::hir::simplify::call_frames) struct Callee {
    local: LocalId,
    child: crate::hir::HirProtoRef,
    declaration: usize,
    creation: crate::hir::HirSourceSite,
    field: crate::LuaString,
    body: HirLuauInliningBody,
    capture: Option<LocalId>,
    parameter_name: Option<String>,
    result_name: Option<String>,
    factory: Option<factories::Factory>,
    returned_call: Option<returned_calls::Body>,
    conditional_method: Option<conditional_methods::Body>,
    repeat_prefix: Option<repeat_prefix::Body>,
    literal_choice: Option<literal_choices::Body>,
    value_expression: Option<value_expressions::Body>,
    capture_locals: Vec<LocalId>,
}

pub(in crate::hir::simplify::call_frames) type Callees =
    BTreeMap<(HirLuauInliningBody, crate::LuaString), Callee>;

pub(super) fn scalar_result_copy(
    facts: &ProtoPromotionFacts,
    call: &HirCallExpr,
    target: &HirLValue,
) -> bool {
    let HirLValue::Local(local) = target else {
        return false;
    };
    let Some(producer) = call
        .source_site
        .and_then(|site| facts.operation_result_temp(site))
    else {
        return false;
    };
    facts
        .trusted_immediate_moves(producer)
        .is_some_and(|copies| {
            matches!(copies, [copy] if facts.promoted_local_for_temp(copy.target) == Some(*local)
            && scalar::result_home(facts, call) == Some(copy.target_home))
        })
}

pub(in crate::hir::simplify) fn restore(
    module: &mut HirModule,
    promotion: &mut Vec<ProtoPromotionFacts>,
    dialect: DecompileDialect,
) -> bool {
    if dialect != DecompileDialect::Luau {
        return false;
    }
    let previous_certificates = module.required_luau_inlining.len();
    numeric_exit::restore(module, promotion);
    captured_predicates::restore(module, promotion);
    let published = module
        .required_luau_inlining
        .iter()
        .map(|certificate| (certificate.owner, certificate.callee))
        .collect::<BTreeSet<_>>();
    // 每个 proto 的 body 形状只读一次；参数替换不比较或复制整个模块。
    let factories = module
        .protos
        .iter()
        .map(|proto| factories::body(proto, promotion, &module.protos))
        .collect::<Vec<_>>();
    let identity_template = module.protos.iter().find(|proto| {
        body_key(proto).is_some_and(|(body, _)| body == HirLuauInliningBody::Identity)
    });
    let returned_calls = module
        .protos
        .iter()
        .map(|proto| {
            promotion
                .get(proto.id.index())
                .and_then(|facts| returned_calls::prepare_body(proto, facts, identity_template))
        })
        .collect::<Vec<_>>();
    let conditional_methods = module
        .protos
        .iter()
        .map(|proto| conditional_methods::body(proto, promotion.get(proto.id.index())?))
        .collect::<Vec<_>>();
    let repeat_prefixes = module
        .protos
        .iter()
        .map(|proto| repeat_prefix::body(proto, promotion.get(proto.id.index())?))
        .collect::<Vec<_>>();
    let literal_choices = module
        .protos
        .iter()
        .map(|proto| literal_choices::body(proto, promotion.get(proto.id.index())?))
        .collect::<Vec<_>>();
    let value_expressions = module
        .protos
        .iter()
        .map(|proto| value_expressions::body(proto, promotion.get(proto.id.index())?))
        .collect::<Vec<_>>();
    let parameter_writebacks = module
        .protos
        .iter()
        .map(|proto| parameter_writebacks::body(proto, &promotion[proto.id.index()]))
        .collect::<Vec<_>>();
    let seeded_predicates = module
        .protos
        .iter()
        .map(|proto| seeded_predicates::body(proto, &promotion[proto.id.index()]))
        .collect::<Vec<_>>();
    let constant_controls = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::constant_control::template)
        .collect::<Vec<_>>();
    let numeric_repeats: Vec<Option<crate::hir::luau_inlining::NumericRepeatTemplate>> = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::numeric_repeat_template)
        .collect();
    let guarded_counters = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::guarded_counter_template)
        .collect::<Vec<_>>();
    let reset_counters = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::reset_counter_template)
        .collect::<Vec<_>>();
    let array_folds = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::array_fold_template)
        .collect::<Vec<_>>();
    let nested_searches = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::nested_search_template)
        .collect::<Vec<_>>();
    let array_names = module
        .protos
        .iter()
        .map(crate::hir::luau_inlining::array_fold_names)
        .collect::<Vec<_>>();
    let transfer_templates = module
        .protos
        .iter()
        .map(|proto| {
            crate::hir::luau_inlining::captured_transfers::template(proto)
                .map(|(label, result)| (label.clone(), result.clone()))
        })
        .collect::<Vec<_>>();
    let calling_templates = calling_values::Templates::new(module, promotion);
    let bodies = module
        .protos
        .iter()
        .map(|proto| {
            body_key(proto)
                .or_else(|| {
                    transfer_templates[proto.id.index()]
                        .as_ref()
                        .map(|(_, result)| {
                            (
                                HirLuauInliningBody::CapturedAppendTransfer {
                                    template: proto.id.index(),
                                },
                                result.clone(),
                            )
                        })
                })
                .or_else(|| {
                    reset_counters[proto.id.index()].map(|_| {
                        (
                            HirLuauInliningBody::ResetCounter {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    nested_searches[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::NestedSearch {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    array_folds[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::ArrayFold {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    parameter_writebacks[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::ParameterWriteback {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    seeded_predicates[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::SeededPredicate {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| calling_templates.key(proto))
                .or_else(|| {
                    literal_choices[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::LiteralChoice {
                                template: proto.id.index(),
                                parameters: proto.params.len(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| repeat_lookup::body_key(proto))
                .or_else(|| {
                    value_expressions[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::ValueExpression {
                                template: proto.id.index(),
                                parameters: proto.params.len(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| generic_lookup::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| generic_counter::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| counter_repeat::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| {
                    generic_break::body_key(proto, promotion.get(proto.id.index())?, &module.protos)
                })
                .or_else(|| counter_while::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| stateful_generic::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| {
                    repeat_prefixes[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::RepeatPrefix {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    conditional_methods[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::ConditionalMethod {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| published_tables::body_key(proto, &promotion[proto.id.index()]))
                .or_else(|| {
                    factories::value_body_key(proto, &promotion[proto.id.index()], &module.protos)
                })
                .or_else(|| scalar::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| captured::body_key(proto, promotion.get(proto.id.index())?))
                .or_else(|| {
                    returned_calls[proto.id.index()].as_ref().map(|body| {
                        (
                            HirLuauInliningBody::CapturedCallablePair,
                            body.label.clone(),
                        )
                    })
                })
                .or_else(|| {
                    factories[proto.id.index()]
                        .as_ref()
                        .map(|factory| factory.key())
                })
                .or_else(|| {
                    guarded_counters[proto.id.index()].as_ref().map(|body| {
                        (
                            HirLuauInliningBody::GuardedCounter {
                                template: proto.id.index(),
                            },
                            body.label.clone(),
                        )
                    })
                })
                .or_else(|| {
                    numeric_repeats[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::NumericRepeat {
                                template: proto.id.index(),
                            },
                            "".into(),
                        )
                    })
                })
                .or_else(|| {
                    constant_controls[proto.id.index()].as_ref().map(|_| {
                        (
                            HirLuauInliningBody::ConstantControl {
                                template: proto.id.index(),
                                parameters: proto.params.len(),
                            },
                            "".into(),
                        )
                    })
                })
        })
        .collect::<Vec<_>>();

    let parameter_names = module
        .protos
        .iter()
        .map(|proto| proto.param_debug_hints.first().cloned().flatten())
        .collect::<Vec<_>>();
    let result_names = module
        .protos
        .iter()
        .map(|proto| {
            let (local, _) = scalar_local(proto.body.stmts.first()?)?;
            proto.local_debug_hints[local.index()].clone()
        })
        .collect::<Vec<_>>();
    let loop_leaves = module
        .protos
        .iter()
        .map(control::leaf_unchanged)
        .collect::<Vec<_>>();
    let mut nested_bodies = BTreeMap::new();
    let mut seeded_bodies = BTreeMap::new();
    for output in &mut module.protos {
        if !output.params.is_empty() {
            continue;
        }
        let nested_owner = output.id != module.entry;
        let Some(original_facts) = promotion.get_mut(output.id.index()) else {
            continue;
        };
        let snapshot_candidate = callees(
            output,
            original_facts,
            &bodies,
            &parameter_names,
            &result_names,
            &factories,
            &returned_calls,
            &conditional_methods,
            &repeat_prefixes,
            &literal_choices,
            &value_expressions,
        )
        .values()
        .any(|callee| {
            matches!(
                callee.body,
                HirLuauInliningBody::CapturedAppendTransfer { .. }
            ) || !nested_owner
                && matches!(
                    callee.body,
                    HirLuauInliningBody::SnapshotClosureFactory { .. }
                        | HirLuauInliningBody::CapturedCallablePair
                        | HirLuauInliningBody::RepeatPrefix { .. }
                        | HirLuauInliningBody::RepeatLookup { .. }
                        | HirLuauInliningBody::CounterRepeat { .. }
                        | HirLuauInliningBody::NumericRepeat { .. }
                        | HirLuauInliningBody::GuardedCounter { .. }
                        | HirLuauInliningBody::GenericLookupWhile { .. }
                        | HirLuauInliningBody::ResetCounter { .. }
                        | HirLuauInliningBody::ArrayFold { .. }
                        | HirLuauInliningBody::NestedSearch { .. }
                        | HirLuauInliningBody::GenericCounter { .. }
                        | HirLuauInliningBody::GenericBreak { .. }
                        | HirLuauInliningBody::CounterWhile { .. }
                )
        });
        let mut prepared_facts = snapshot_candidate.then(|| original_facts.clone());
        let prepared = if let Some(facts) = &mut prepared_facts {
            let Some((mut proto, _)) = prepare_source_frames(output.clone(), facts, dialect) else {
                continue;
            };
            prefix::restore_call_result_prefix(&mut proto, facts);
            Some(proto)
        } else {
            None
        };
        let facts = prepared_facts.as_mut().unwrap_or(original_facts);
        let prepared_proto = prepared.as_ref().unwrap_or(output);
        let generic_draft = generic_break::prepare(prepared_proto, facts, &bodies);
        let prepared_proto = generic_draft.as_ref().unwrap_or(prepared_proto);
        let mut initial_callees = callees(
            prepared_proto,
            facts,
            &bodies,
            &parameter_names,
            &result_names,
            &factories,
            &returned_calls,
            &conditional_methods,
            &repeat_prefixes,
            &literal_choices,
            &value_expressions,
        );
        initial_callees.retain(|_, callee| {
            !nested_owner
                || matches!(
                    callee.body,
                    HirLuauInliningBody::CapturedValue
                        | HirLuauInliningBody::CapturedAppendTransfer { .. }
                )
        });
        let comparison_draft =
            literal_choices::debug_arguments(prepared_proto, facts, &initial_callees);
        let comparison_proto = comparison_draft
            .as_ref()
            .map_or(prepared_proto, |(proto, _)| proto);
        let expression_draft =
            value_expressions::debug_arguments(comparison_proto, facts, &initial_callees);
        let expression_proto = expression_draft
            .as_ref()
            .map_or(comparison_proto, |(proto, _)| proto);
        let scalar_draft = scalar::debug_updates(expression_proto, facts, &initial_callees);
        let scalar_proto = scalar_draft
            .as_ref()
            .map_or(expression_proto, |(proto, _)| proto);
        let writeback_draft = parameter_writebacks::debug_arguments(
            scalar_proto,
            facts,
            &initial_callees,
            &parameter_writebacks,
            &parameter_names,
        );
        let writeback_proto = writeback_draft
            .as_ref()
            .map_or(scalar_proto, |(proto, _)| proto);
        let seeded_draft = seeded_predicates::debug_arguments(
            writeback_proto,
            facts,
            &initial_callees,
            &seeded_predicates,
        );
        let seeded_proto = seeded_draft
            .as_ref()
            .map_or(writeback_proto, |(proto, _)| proto);
        let seeded_frames =
            seeded_predicates::prepare(seeded_proto, facts, &initial_callees, &seeded_predicates);
        let seeded_proto = seeded_frames
            .as_ref()
            .map_or(seeded_proto, |draft| &draft.proto);
        let calling_draft = (!nested_owner)
            .then(|| calling_values::prepare(seeded_proto, facts, &calling_templates))
            .flatten();
        let calling_proto = calling_draft
            .as_ref()
            .map_or(seeded_proto, |draft| &draft.proto);
        let draft = branch_arguments::prepare(calling_proto, facts);
        let proto = draft.as_ref().map_or(calling_proto, |(proto, _)| proto);

        // 根候选仍不跨控制边界取输入；提交与普通帧统一使用共享 DFS 坐标。
        if proto.body.stmts.iter().any(|stmt| {
            !matches!(
                stmt,
                HirStmt::LocalDecl(_)
                    | HirStmt::Assign(_)
                    | HirStmt::CallStmt(_)
                    | HirStmt::TableSetList(_)
                    | HirStmt::LocalRootRelease(_)
                    | HirStmt::Block(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::Repeat(_)
                    | HirStmt::While(_)
                    | HirStmt::If(_)
                    | HirStmt::GenericFor(_)
                    | HirStmt::Return(_)
            )
        }) {
            continue;
        }
        let mut root_indices = Vec::new();
        let mut coordinate = 0;
        for stmt in &proto.body.stmts {
            root_indices.push(coordinate);
            coordinate += 1;
            crate::hir::visit::for_each_nested_block(stmt, &mut |block| {
                prefix::coordinates::visit(block, &mut coordinate, &mut |_, _, _| {});
            });
            if matches!(stmt, HirStmt::Repeat(_)) {
                coordinate += 1;
            }
        }
        let structured = proto
            .body
            .stmts
            .iter()
            .any(|stmt| matches!(stmt, HirStmt::NumericFor(_) | HirStmt::GenericFor(_)));
        let mut callees = callees(
            proto,
            facts,
            &bodies,
            &parameter_names,
            &result_names,
            &factories,
            &returned_calls,
            &conditional_methods,
            &repeat_prefixes,
            &literal_choices,
            &value_expressions,
        );
        callees.retain(|_, callee| {
            !published.contains(&(proto.id, callee.local))
                && (!nested_owner
                    || matches!(
                        callee.body,
                        HirLuauInliningBody::CapturedValue
                            | HirLuauInliningBody::CapturedAppendTransfer { .. }
                    ))
        });
        if structured {
            // 候选拒绝[ProofIncomplete:Lifetime]：结构化后缀只覆盖已证明的展开帧；其它对象根仍需完整的结构化重放证书。
            callees.retain(|(body, _), _| {
                matches!(
                    body,
                    HirLuauInliningBody::ValueClosureFactory { .. }
                        | HirLuauInliningBody::ConditionalMethod { .. }
                        | HirLuauInliningBody::LiteralChoice { .. }
                        | HirLuauInliningBody::ValueExpression { .. }
                        | HirLuauInliningBody::ParameterWriteback { .. }
                        | HirLuauInliningBody::SeededPredicate { .. }
                        | HirLuauInliningBody::ConstantControl { .. }
                        | HirLuauInliningBody::NumericRepeat { .. }
                        | HirLuauInliningBody::GuardedCounter { .. }
                        | HirLuauInliningBody::ResetCounter { .. }
                        | HirLuauInliningBody::ArrayFold { .. }
                        | HirLuauInliningBody::NestedSearch { .. }
                        | HirLuauInliningBody::CallingValue { .. }
                        | HirLuauInliningBody::CallingSharedValue { .. }
                        | HirLuauInliningBody::CallingObservedValue { .. }
                        | HirLuauInliningBody::CallingReadPair { .. }
                        | HirLuauInliningBody::GenericCounter { .. }
                )
            });
        }
        if callees.is_empty() {
            continue;
        }
        let transfer_frames = captured_transfers::frames(&callees, &transfer_templates);
        let compared_choices = literal_choices::compared_callees(&callees, facts);
        let expression_frames = value_expressions::frames(proto, &callees, facts);
        let control_frames = constant_control::frames(&callees, facts, &constant_controls);
        let calling_frames = calling_draft.as_ref().map(|draft| draft.frames(facts));
        let restrictions = frame_restrictions(proto, facts);
        let context = NativeFrameContext {
            rk_literals: None,
            expanded_callees: Some(&callees),
            captured_transfers: Some(&transfer_frames),
            compared_choices: Some(&compared_choices),
            value_expressions: Some(&expression_frames),
            constant_controls: Some(&control_frames),
            calling_values: calling_frames.as_ref(),
            seeded_predicates: seeded_frames.as_ref(),
            retired_roots: None,
            root_seed_sources: None,
            proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            callee_aliases: &restrictions.callee_aliases,
            constants_fit_rk: tables::constants_fit_rk(proto),
        };
        let mut expanded = Vec::new();
        let array_recovery = array_fold::plans(context, facts, &array_folds, &array_names);
        let proto = array_recovery.draft.as_ref().unwrap_or(proto);
        let context = NativeFrameContext { proto, ..context };

        let search_recovery = nested_search::plans(context, facts, &nested_searches);
        let proto = search_recovery.draft.as_ref().unwrap_or(proto);
        let context = NativeFrameContext { proto, ..context };

        let mut start = 0;
        for (sink, stmt) in proto.body.stmts.iter().enumerate() {
            let indexed = scalar_local(stmt).is_some_and(|(local, value)| {
                let HirExpr::TableAccess(access) = value else {
                    return false;
                };
                matches!(access.key, HirExpr::Integer(1))
                    && facts.trusted_local_home_slot(local).is_some_and(|home| {
                        facts
                            .native_table_read_layout(access)
                            .is_some_and(|layout| {
                                layout.base == HomeSlotKey::new(home.slot() + 2, 0)
                                    && layout.key.is_none()
                            })
                    })
            });
            let batch = match constructor_write(stmt) {
                Some(ConstructorWrite::Batch { batch, .. }) => Some(batch),
                _ => None,
            };
            let complete = scalar_local(stmt).is_some_and(|(_, value)| matches!(value,
                HirExpr::TableConstructor(table) if table.fields.is_empty() && table.trailing_multivalue.is_some()));
            if batch.is_none() && !indexed && !complete {
                if scalar_local(stmt).is_none()
                    && constructor_write(stmt).is_none()
                    && !matches!(stmt, HirStmt::LocalRootRelease(_))
                {
                    start = sink + 1;
                }
                continue;
            }
            // release 只清理由源码声明额外持有的根，不是原 VM 事件。仍把它计入
            // removed，后续 preview 必须证明相应 epoch 的声明也在同批退休。
            let positions = (start..=sink)
                .filter(|&index| !matches!(proto.body.stmts[index], HirStmt::LocalRootRelease(_)))
                .collect::<Vec<_>>();
            let run = positions
                .iter()
                .map(|&index| &proto.body.stmts[index])
                .collect::<Vec<_>>();
            let candidate = match batch {
                Some(batch) => candidate(context, facts, &run, &callees, &positions, batch),
                None if complete => completed_candidate(context, facts, &run, &callees, &positions),
                None => indexed_candidate(context, facts, &run, &callees, &positions),
            };
            if let Some((mut plan, _)) = candidate {
                plan.start = positions[plan.start];
                plan.sink = sink;
                plan.removed = (plan.start..sink).collect();
                expanded.push(plan);
            }
            // 每个批次至多消费一个直线窗口，不对窗口内的 seed 逐个重试。
            start = sink + 1;
        }

        let (mut plans, count) = collect_native_plans(context, facts, dialect, false);
        expanded.extend(factories::plans(context, facts));
        expanded.extend(returned_calls::plans(context, facts));
        expanded.extend(conditional_methods::plans(context, facts));
        expanded.extend(repeat_prefix::plans(context, facts));
        expanded.extend(repeat_lookup::plans(context, facts));
        expanded.extend(counter_repeat::plans(context, facts));
        expanded.extend(reset_counter::plans(context, facts, &reset_counters));
        expanded.extend(constant_control::plans(context, facts));
        let numeric_recovery = numeric_repeat::plans(context, facts, &numeric_repeats);
        expanded.extend(numeric_recovery.plans);
        let guarded_recovery = guarded_counter::plans(context, facts, &guarded_counters);
        expanded.extend(guarded_recovery.plans);
        expanded.extend(generic_lookup::plans(context, facts));
        expanded.extend(generic_counter::plans(context, facts));
        expanded.extend(generic_break::plans(context, facts));
        expanded.extend(counter_while::plans(context, facts));
        expanded.extend(stateful_generic::plans(context, facts));

        expanded.extend(scalar::constant_comparisons(context, facts));
        let conditional_callees = callees
            .values()
            .filter(|callee| callee.conditional_method.is_some())
            .map(|callee| callee.local)
            .collect::<BTreeSet<_>>();
        for plan in &mut expanded {
            let loop_replays = plan
                .replayed_effects
                .iter()
                .filter_map(|&index| {
                    matches!(
                        proto.body.stmts[index],
                        HirStmt::Repeat(_)
                            | HirStmt::While(_)
                            | HirStmt::GenericFor(_)
                            | HirStmt::NumericFor(_)
                    )
                    .then_some(root_indices[index]..root_indices[index + 1])
                })
                .collect::<Vec<_>>();
            plan.start = root_indices[plan.start];
            plan.sink = root_indices[plan.sink];
            for index in &mut plan.removed {
                *index = root_indices[*index];
            }
            for index in &mut plan.replayed_effects {
                *index = root_indices[*index];
            }
            for range in loop_replays {
                plan.removed.extend(range.clone());
                plan.replayed_effects.extend(range);
            }
            if matches!(plan.values.fixed.as_slice(), [HirExpr::Call(call)]
                if matches!(call.callee, HirExpr::LocalRef(local) if conditional_callees.contains(&local)))
            {
                // 条件头及其唯一方法调用已逐项配对；退休必须包含分支内部的 DFS 坐标。
                plan.removed = (plan.start..plan.sink).collect();
                plan.replayed_effects = plan.removed.clone();
            }
        }
        expanded.extend(numeric_recovery.nested_plans);
        expanded.extend(array_recovery.plans);
        expanded.extend(search_recovery.plans);
        if let Some(draft) = &calling_draft {
            expanded.extend(draft.plans(context, facts));
        }
        expanded.extend(parameter_writebacks::plans(
            context,
            facts,
            &parameter_writebacks,
        ));
        if let Some(draft) = &seeded_frames {
            expanded.extend(draft.plans(context, facts, &plans));
        }
        expanded.extend(snapshots::plans(context, facts, &root_indices));
        let choices = literal_choices::plans(context, facts, &root_indices);
        expanded.extend(choices);
        let mut native_owner = vec![None; count];
        for (owner, plan) in plans.iter().enumerate() {
            for index in plan.removed.iter().copied().chain([plan.sink]) {
                native_owner[index] = Some(owner);
            }
        }
        // 同一展开结果已被完整外层参数帧消费时，不能优先冻结独立 initializer
        // 并截断它的 Boolean 预写；只有完整覆盖的外层计划才取代内层计划。
        expanded.retain(|plan| {
            plan.start == plan.sink && !plan.only_preserves_call_prefix()
                || !native_owner[plan.sink].is_some_and(|owner| {
                    plan.removed
                        .iter()
                        .all(|&index| native_owner[index] == Some(owner))
                })
        });
        let occupied = expanded
            .iter()
            .flat_map(|plan| plan.start..=plan.sink)
            .collect::<BTreeSet<_>>();
        plans.retain(|plan| {
            !occupied.contains(&plan.sink)
                && plan.removed.iter().all(|index| !occupied.contains(index))
        });
        plans.extend(expanded);
        let by_local = callees
            .values()
            .map(|callee| (callee.local, callee))
            .collect::<BTreeMap<_, _>>();
        let mut certificates = BTreeMap::<LocalId, HirRequiredLuauInlining>::new();
        let choice_homes = facts
            .literal_choices()
            .filter_map(|choice| {
                choice
                    .tests
                    .iter()
                    .any(|test| *test != crate::hir::promotion::LiteralChoiceTest::Truthy)
                    .then(|| Some((choice.source, facts.trusted_temp_home_slot(choice.result)?)))
                    .flatten()
            })
            .collect::<BTreeMap<_, _>>();
        let expression_homes = facts
            .value_programs()
            .filter(|region| region.initial.is_some())
            .filter_map(|region| {
                Some((region.source, facts.trusted_temp_home_slot(region.result)?))
            })
            .collect::<BTreeMap<_, _>>();
        let operand_copy_homes = facts
            .operand_copy_frames()
            .map(|(site, copy)| (site, copy.target_home.slot()))
            .collect::<BTreeMap<_, _>>();
        let mut first = None;
        for plan in &mut plans {
            let mut captured_updates = BTreeSet::new();
            let mut captured_transfers = BTreeSet::new();
            for value in plan
                .values
                .fixed
                .iter()
                .chain(plan.values.tail.iter().map(|tail| tail.as_expr()))
            {
                crate::hir::visit::any_expr(value, &mut |expr| {
                    if let HirExpr::Call(call) = expr
                        && let Some(site) = call.required_luau_inlining
                        && let HirExpr::LocalRef(local) = call.callee
                    {
                        let callee = by_local[&local];
                        if matches!(
                            callee.body,
                            HirLuauInliningBody::CapturedAppendTransfer { .. }
                        ) {
                            captured_transfers.insert(site);
                        }
                        if callee.capture.is_some()
                            && callee.body != HirLuauInliningBody::CapturedValue
                        {
                            captured_updates.insert(site);
                        }
                        first = Some(
                            first.map_or(plan.start, |previous: usize| previous.min(plan.start)),
                        );
                        certificates
                            .entry(local)
                            .or_insert_with(|| HirRequiredLuauInlining {
                                owner: proto.id,
                                callee: local,
                                child: callee.child,
                                field: callee.field.clone(),
                                body: callee.body,
                                capture: callee.capture,
                                occurrences: Vec::new(),
                                result_frame_slots: BTreeMap::new(),
                                callable_arguments: Default::default(),
                                nil_guards: Default::default(),
                            })
                            .occurrences
                            .push(site);
                        if let Some(dependency) = calling_frames
                            .as_ref()
                            .and_then(|frames| frames.dependency(site))
                        {
                            certificates
                                .get_mut(&local)
                                .unwrap()
                                .callable_arguments
                                .insert(site, dependency);
                        }
                        if calling_frames
                            .as_ref()
                            .is_some_and(|frames| frames.nil_guard(site))
                        {
                            certificates
                                .get_mut(&local)
                                .unwrap()
                                .nil_guards
                                .insert(site);
                        }
                        if matches!(
                            callee.body,
                            HirLuauInliningBody::CapturedValue
                                | HirLuauInliningBody::CapturedAppendTransfer { .. }
                                | HirLuauInliningBody::SnapshotClosureFactory { .. }
                                | HirLuauInliningBody::CapturedCallablePair
                                | HirLuauInliningBody::LiteralChoice { .. }
                                | HirLuauInliningBody::ValueExpression { .. }
                                | HirLuauInliningBody::ParameterWriteback { .. }
                                | HirLuauInliningBody::SeededPredicate { .. }
                                | HirLuauInliningBody::ConstantControl { .. }
                                | HirLuauInliningBody::NumericRepeat { .. }
                                | HirLuauInliningBody::GuardedCounter { .. }
                                | HirLuauInliningBody::ResetCounter { .. }
                                | HirLuauInliningBody::ArrayFold { .. }
                                | HirLuauInliningBody::NestedSearch { .. }
                                | HirLuauInliningBody::CallingValue { .. }
                                | HirLuauInliningBody::CallingSharedValue { .. }
                                | HirLuauInliningBody::CallingObservedValue { .. }
                                | HirLuauInliningBody::CallingReadPair { .. }
                                | HirLuauInliningBody::ConditionalMethod { .. }
                                | HirLuauInliningBody::RepeatPrefix { .. }
                                | HirLuauInliningBody::RepeatLookup { .. }
                                | HirLuauInliningBody::CounterRepeat { .. }
                                | HirLuauInliningBody::GenericLookupWhile { .. }
                                | HirLuauInliningBody::GenericCounter { .. }
                                | HirLuauInliningBody::GenericBreak { .. }
                                | HirLuauInliningBody::CounterWhile { .. }
                                | HirLuauInliningBody::StatefulGenericWhile { .. }
                        ) {
                            // 使用已证明的原返回槽；比较型展开帧还预留 callee/Boolean。
                            certificates
                                .get_mut(&local)
                                .unwrap()
                                .result_frame_slots
                                .insert(
                                    site,
                                    if matches!(
                                        callee.body,
                                        HirLuauInliningBody::CapturedAppendTransfer { .. }
                                    ) {
                                        facts
                                            .operation_result_home(site)
                                            .expect("validated captured transfer result")
                                            .slot()
                                    } else if callee.body == HirLuauInliningBody::CapturedValue {
                                        operand_copy_homes[&site]
                                    } else if let Some(home) = seeded_frames
                                        .as_ref()
                                        .and_then(|frames| frames.result_home(site))
                                    {
                                        home
                                    } else if let Some(home) = numeric_recovery
                                        .result_slots
                                        .get(&site)
                                        .or_else(|| guarded_recovery.result_slots.get(&site))
                                        .or_else(|| array_recovery.result_slots.get(&site))
                                        .or_else(|| search_recovery.result_slots.get(&site))
                                    {
                                        *home
                                    } else if let Some(result) = calling_frames
                                        .as_ref()
                                        .and_then(|frames| frames.result(site))
                                    {
                                        facts
                                            .trusted_temp_home_slot(result)
                                            .expect("validated calling value result")
                                            .slot()
                                    } else if let Some(home) = expression_homes.get(&site.instr)
                                        && matches!(
                                            callee.body,
                                            HirLuauInliningBody::ValueExpression { .. }
                                        )
                                    {
                                        home.slot()
                                    } else if let Some(home) = choice_homes
                                        .get(&site.instr)
                                        .copied()
                                        .or_else(|| facts.operation_result_home(site))
                                        && matches!(
                                            callee.body,
                                            HirLuauInliningBody::LiteralChoice { .. }
                                        )
                                    {
                                        home.slot()
                                    } else if matches!(
                                        callee.body,
                                        HirLuauInliningBody::ConstantControl { .. }
                                    ) {
                                        facts
                                            .operation_result_home(site)
                                            .expect("validated constant-control allocation")
                                            .slot()
                                            - 1
                                    } else if matches!(
                                        callee.body,
                                        HirLuauInliningBody::GenericCounter { .. }
                                    ) {
                                        // 计数状态在返回槽之上两格，候选已核对原更新端点。
                                        facts
                                            .operation_writeback(site)
                                            .expect("validated counter writeback")
                                            .1
                                            .slot()
                                            - 2
                                    } else {
                                        plan.base.slot()
                                            + if matches!(
                                                callee.body,
                                                HirLuauInliningBody::CounterWhile { .. }
                                            ) || matches!(
                                                callee.body,
                                                HirLuauInliningBody::GenericLookupWhile { .. }
                                            ) && plan.result_locals.is_empty()
                                            {
                                                2
                                            } else {
                                                0
                                            }
                                    },
                                );
                        }
                    }
                    false
                });
            }
            let effects =
                captured_transfers::replayed(proto, &root_indices, plan, &captured_transfers);
            plan.replayed_effects.extend(effects);
            plan.replayed_effects
                .extend(plan.removed.iter().copied().filter(|index| {
                matches!(root_indices.binary_search(index).ok().and_then(|root| scalar_local(&proto.body.stmts[root])), Some((_, HirExpr::Binary(binary)))
                    if binary.source_site.is_some_and(|site| captured_updates.contains(&site)))
            }));
        }

        let Some(first) = first else {
            continue;
        };
        // debug 更新只在同一 child 的强制内联证书实际消费原 CALL 时退休；
        // 任何局部候选失败都撤销整份投影，不能留下被树化的 debug 声明。
        let certified_sites = certificates
            .iter()
            .flat_map(|(local, certificate)| {
                certificate
                    .occurrences
                    .iter()
                    .map(move |site| (*site, *local))
            })
            .collect::<BTreeSet<_>>();
        if comparison_draft
            .iter()
            .chain(expression_draft.iter())
            .chain(scalar_draft.iter())
            .chain(writeback_draft.iter())
            .chain(seeded_draft.iter())
            .any(|(_, obligations)| {
                obligations
                    .iter()
                    .any(|obligation| !certified_sites.contains(obligation))
            })
        {
            continue;
        }
        if array_recovery
            .obligations
            .iter()
            .chain(search_recovery.obligations.iter())
            .any(|obligation| !certified_sites.contains(obligation))
        {
            continue;
        }
        if calling_draft
            .as_ref()
            .is_some_and(|draft| !draft.certified(&certified_sites))
        {
            continue;
        }
        if seeded_frames
            .as_ref()
            .is_some_and(|draft| !draft.certified(&certified_sites))
        {
            continue;
        }
        let replayed = plans
            .iter()
            .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
            .collect::<BTreeSet<_>>();
        prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
            if kind == PointKind::Statement
                && index >= first
                && !replayed.contains(&index)
                && let Some(plan) = standalone_initializer_frame(context, facts, stmt, index)
            {
                plans.push(plan);
            }
        });
        plans.sort_unstable_by_key(|plan| plan.sink);
        let mut preview = match build_preview(proto, facts, dialect, &plans, count) {
            Ok(preview) => preview,
            Err(_) => continue,
        };
        // 展开体退休旧 epoch 后，同槽 CALL/CLOSURE 等写入才能成为后继声明。
        // 初始化没有再次改写，但必须在最终预览上补齐原槽前缀请求。
        let sinks = plans.iter().map(|plan| plan.sink).collect::<BTreeSet<_>>();
        let preview_context = NativeFrameContext {
            proto: &preview.proto,
            ..context
        };
        prefix::coordinates::visit(&preview.proto.body, &mut 0, &mut |index, kind, stmt| {
            if kind == PointKind::Statement
                && index >= first
                && !preview.removed[index]
                && !sinks.contains(&index)
                && matches!(stmt, HirStmt::LocalDecl(_))
                && let Some(plan) =
                    standalone_initializer_frame(preview_context, facts, stmt, index)
            {
                plans.push(plan);
            }
        });
        plans.sort_unstable_by_key(|plan| plan.sink);
        // 分支表达式只存在于未提交预览中；外层 CALL 必须整帧消费原 Boolean
        // 预写，不能在局部计划失败后把候选短路树单独写回。
        let consumed = plans
            .iter()
            .flat_map(|plan| plan.removed.iter().map(move |&index| (index, plan.sink)))
            .collect::<BTreeSet<_>>();
        if draft.as_ref().is_some_and(|(_, obligations)| {
            obligations.iter().any(|&(initial, call)| {
                !preview.removed[initial] || !consumed.contains(&(initial, call))
            })
        }) {
            continue;
        }
        // 逐坐标重放后缀。结构化边界只能留下无 scratch 比较和原 local COPY，
        // 原控制槽、各分支声明及新闭包结果仍由完整 prefix 事务核对。
        if !suffix_replayed(&preview, &plans, first, facts, structured) {
            continue;
        }
        let Ok(mut preserved) = validate_plan_batch(
            &mut preview,
            proto,
            &plans,
            facts,
            dialect,
            proto.id == module.entry,
            true,
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
        let expression_loops = certificates.values().any(|certificate| {
            matches!(
                certificate.body,
                HirLuauInliningBody::ValueExpression { .. }
                    | HirLuauInliningBody::ParameterWriteback { .. }
                    | HirLuauInliningBody::SeededPredicate { .. }
                    | HirLuauInliningBody::ConstantControl { .. }
                    | HirLuauInliningBody::NumericRepeat { .. }
                    | HirLuauInliningBody::GuardedCounter { .. }
                    | HirLuauInliningBody::ResetCounter { .. }
                    | HirLuauInliningBody::ArrayFold { .. }
                    | HirLuauInliningBody::NestedSearch { .. }
                    | HirLuauInliningBody::CallingValue { .. }
                    | HirLuauInliningBody::CallingSharedValue { .. }
                    | HirLuauInliningBody::CallingObservedValue { .. }
                    | HirLuauInliningBody::CallingReadPair { .. }
            )
        });
        if structured
            && !(if expression_loops {
                expression_loops::unchanged(&preview.proto)
            } else {
                control::loops_unchanged(&preview.proto, &loop_leaves)
            })
        {
            // 候选拒绝[TargetConstraint]：不能在恢复工厂时顺带触发 O2 循环展开或其它函数内联。
            continue;
        }
        for local in preserved {
            preview
                .proto
                .inline_dispositions
                .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
        }
        publish_recovered_declarations(&mut preview, facts);
        for certificate in certificates.values() {
            if let Some(inner) = by_local[&certificate.callee]
                .factory
                .as_ref()
                .and_then(factories::Factory::nested_inner)
            {
                nested_bodies.insert(certificate.child, inner);
            }
        }
        if let Some(draft) = seeded_frames {
            seeded_bodies.extend(draft.bodies);
        }
        *output = preview.proto;
        if let Some(facts) = prepared_facts {
            *original_facts = facts;
        }
        module
            .required_luau_inlining
            .extend(certificates.into_values());
    }
    for certificate in &module.required_luau_inlining {
        if let Some(Some(body)) = literal_choices.get(certificate.child.index()) {
            literal_choices::publish(body, &mut module.protos[certificate.child.index()]);
        }
    }
    for (child, branch) in seeded_bodies {
        if let Some(body) = &seeded_predicates[child.index()] {
            seeded_predicates::publish(body, branch, &mut module.protos[child.index()]);
        }
    }
    for (child, inner) in nested_bodies {
        factories::restore_nested_body(&mut module.protos[child.index()], inner);
    }
    let pair_children = module
        .required_luau_inlining
        .iter()
        .filter(|certificate| certificate.body == HirLuauInliningBody::CapturedCallablePair)
        .map(|certificate| certificate.child)
        .collect::<BTreeSet<_>>();
    for child in pair_children {
        if let Some(Some(body)) = returned_calls.get(child.index()) {
            let id = crate::hir::HirProtoRef(module.protos.len());
            if let Some(wrapper) =
                returned_calls::publish(body, &mut module.protos[child.index()], id)
            {
                module.protos.push(wrapper);
                promotion.push(ProtoPromotionFacts::default());
            }
        }
    }
    for requirement in &module.required_luau_inlining {
        if matches!(requirement.body, HirLuauInliningBody::ScalarNotCall { .. }) {
            scalar::preserve_updates(
                &mut module.protos[requirement.child.index()],
                &mut promotion[requirement.child.index()],
            );
        }
    }
    module.required_luau_inlining.len() != previous_certificates
}

/// 后缀中已完整恢复的调用及独立初始化仍承担原 home 的前缀义务，
/// 证明按原位置覆盖展开调用留下的根；调用重放必须与当前树完全相同。
fn standalone_initializer_frame(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    stmt: &HirStmt,
    index: usize,
) -> Option<Plan> {
    if let HirStmt::If(branch) = stmt {
        let base =
            completed_condition_prefix(context, facts, DecompileDialect::Luau, &branch.cond)?;
        // 条件本身不改写；原常量准备仍占用 scratch，不能只把已树化的条件当作低槽读取。
        // 与其它帧共用当前预览的声明栈及后继验证，分支正文继续逐坐标重放。
        return Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base,
            values: vec![branch.cond.clone()].into(),
            result_locals: Vec::new(),
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    }
    if let HirStmt::LocalDecl(decl) = stmt
        && decl.bindings.len() > 1
        && decl.values.fixed.is_empty()
        && let Some(tail) = &decl.values.tail
        && tail.exact_width() == Some(decl.bindings.len())
        && let HirExpr::Call(call) = tail.as_expr()
    {
        let frame = facts.native_call_frame(call)?;
        // 原固定结果 Def 逐项连接当前 binding；连续槽并不意味着 CLOSE epoch 为零。
        for (offset, &local) in decl.bindings.iter().enumerate() {
            let result = facts.fixed_call_result(call, offset)?;
            if facts.promoted_local_for_temp(result) != Some(local)
                || facts.trusted_temp_home_slot(result) != facts.trusted_local_home_slot(local)
            {
                return None;
            }
        }
        let mut builder = frame_builder(
            context,
            &[],
            facts,
            DecompileDialect::Luau,
            frame.home.slot(),
        )?;
        if builder.call(
            call,
            0,
            frame.home.slot(),
            true,
            CallWidth::Fixed(decl.bindings.len()),
        )? != **call
        {
            return None;
        }
        return Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base: frame.home,
            values: decl.values.clone(),
            result_locals: decl.bindings.clone(),
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    }
    if let HirStmt::CallStmt(stmt) = stmt {
        let call = &stmt.call;
        let home = if call.fastcall.is_some() {
            facts.native_fastcall_frame(call)?.home
        } else {
            facts.native_call_layout(call)?.home
        };
        let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, home.slot())?;
        let rebuilt = builder.call(call, 0, home.slot(), false, CallWidth::Ignore)?;
        if rebuilt != *call {
            return None;
        }
        return Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base: home,
            values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
            result_locals: Vec::new(),
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    }
    if let HirStmt::Assign(assign) = stmt
        && let ([HirLValue::TableAccess(access)], [value], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        )
        && let Some(base) = facts.luau_literal_table_write_frame(access, value)
    {
        // 原常量准备与字段写入已由 Promotion 配对；这里只补齐保持原位的前缀义务。
        return Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base,
            values: vec![value.clone()].into(),
            result_locals: Vec::new(),
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: Some((**access).clone()),
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    }
    if let HirStmt::Assign(assign) = stmt
        && let ([target @ HirLValue::Global(global)], [value @ HirExpr::Closure(closure)], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        )
    {
        let base = facts.global_write_value_home(global, DecompileDialect::Luau)?;
        let source = closure.source_site?;
        let producer = facts.operation_result_temp(source)?;
        let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())?;
        if facts.operation_result_home(source) != Some(base)
            || builder.expr(value, 0, base.slot(), None, false, true, Some(producer))? != *value
        {
            return None;
        }
        // 闭包已直接发布到全局；只登记原创建/写回的前缀，不改动捕获和安装时点。
        return Some(Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: index,
            sink: index,
            base,
            values: vec![value.clone()].into(),
            result_locals: Vec::new(),
            assignment_targets: vec![target.clone()],
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        });
    }
    let (local, value) = scalar_local(stmt)?;
    let base = facts.trusted_local_home_slot(local)?;
    if context.closed.contains(&base) {
        return None;
    }
    match value {
        HirExpr::LocalRef(source)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && facts.trusted_local_home_slot(*source)
                    .is_some_and(|home| home.slot() < base.slot()) => {}
        HirExpr::GlobalRef(global)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && facts.global_read_frame(global, DecompileDialect::Luau) == Some(base)
                && frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())
                    .and_then(|mut builder| builder.expr(value, 0, base.slot(), None, false, true, None))
                    .is_some_and(|rebuilt| rebuilt == *value) => {}
        HirExpr::Call(call)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && facts
                    .native_call_frame(call)
                    .or_else(|| facts.native_fastcall_frame(call))
                    .is_some_and(|frame| frame.home == base)
                && frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())
                    .and_then(|mut builder| {
                        builder.call(call, 0, base.slot(), true, CallWidth::Single)
                    })
                    .is_some_and(|rebuilt| rebuilt == **call) => {}
        HirExpr::TableConstructor(table)
            if frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())
                .and_then(|builder| builder.completed_luau_constructor(table, base.slot())).is_some()
                && facts.allocation_result_reference_unaliased(table) => {}
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && frame_builder(context, &[], facts, DecompileDialect::Luau, base.slot())
                    .and_then(|mut builder| builder.luau_logical_value(value, 0, base, None))
                    .is_some_and(|rebuilt| rebuilt == *value) => {}
        HirExpr::Binary(_) | HirExpr::Unary(_)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && control::direct_boolean_result(local, value, facts) => {}
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
            if matches!(stmt, HirStmt::LocalDecl(_)) => {}
        HirExpr::Closure(closure)
            if matches!(stmt, HirStmt::LocalDecl(_))
                && closure.captures.iter().all(|capture|
                    matches!(capture.binding, HirBinding::Local(local)
                            if facts.trusted_local_home_slot(local).is_some_and(|home| home.slot() < base.slot())))
                && closure.source_site.is_some_and(|source| {
                    facts.operation_result_home(source) == Some(base)
                        && facts.operation_result_reference_unaliased(source)
                        && facts.operation_result_temp(source).is_some_and(|temp| {
                            facts
                                .complete_temp_definition_write_homes(temp)
                                .iter()
                                .copied()
                                .eq([base])
                        })
                }) => {}
        _ => return None,
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: index,
        sink: index,
        base,
        values: vec![value.clone()].into(),
        result_locals: vec![local],
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "父级原始值身份与各 child 的已缓存函数体事实共同筛选候选，不重复构建分析"
)]
fn callees(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    bodies: &[Option<(HirLuauInliningBody, crate::LuaString)>],
    parameter_names: &[Option<String>],
    result_names: &[Option<String>],
    factories: &[Option<factories::Factory>],
    returned_calls: &[Option<returned_calls::Body>],
    conditional_methods: &[Option<conditional_methods::Body>],
    repeat_prefixes: &[Option<repeat_prefix::Body>],
    literal_choices: &[Option<literal_choices::Body>],
    value_expressions: &[Option<value_expressions::Body>],
) -> BTreeMap<(HirLuauInliningBody, crate::LuaString), Callee> {
    struct PcallInputs<'a> {
        facts: &'a ProtoPromotionFacts,
        globals: BTreeSet<TempId>,
        calls: Vec<(TempId, LocalId)>,
        inputs: BTreeMap<LocalId, usize>,
    }
    impl crate::hir::visit::HirVisitor<'_> for PcallInputs<'_> {
        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::GlobalRef(global) = expr
                && global.key.as_utf8() == Some("pcall")
                && let crate::hir::common::HirOperationSources::Single(source) = global.sources
                && let Some(producer) = self.facts.operation_result_temp(source)
            {
                self.globals.insert(producer);
            }
        }
        fn visit_call(&mut self, call: &HirCallExpr) {
            // pcall 的首实参是函数值，不是编译器可额外内联的直接调用；
            // 分离的全局读取按 CALL 的原 Def 连接，展示 Local 的复用不改变身份。
            if !call.is_method()
                && let Some(HirExpr::LocalRef(local)) = call.args.fixed.first()
            {
                if matches!(&call.callee, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("pcall"))
                {
                    *self.inputs.entry(*local).or_default() += 1;
                } else if let HirExpr::LocalRef(callee) = call.callee
                    && let Some(frame) = self.facts.native_call_frame(call)
                    && self.facts.promoted_local_for_temp(frame.callee) == Some(callee)
                {
                    self.calls.push((frame.callee, *local));
                }
            }
        }
    }
    let mut reads = BTreeMap::<LocalId, usize>::new();
    let mut writes = BTreeMap::<LocalId, usize>::new();
    let mut collectors = (
        PcallInputs {
            facts,
            globals: BTreeSet::new(),
            calls: Vec::new(),
            inputs: BTreeMap::new(),
        },
        (
            BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *reads.entry(local).or_default() += 1;
                }
            }),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *writes.entry(local).or_default() += 1;
                }
            }),
        ),
    );
    visit_stmts(&proto.body.stmts, &mut collectors);
    let (mut pcall_inputs, _) = collectors;
    for (producer, local) in &pcall_inputs.calls {
        if pcall_inputs.globals.contains(producer) {
            *pcall_inputs.inputs.entry(*local).or_default() += 1;
        }
    }
    let mut candidates = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    for (index, stmt) in proto.body.stmts.iter().enumerate() {
        let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt) else {
            continue;
        };
        let Some(Some(key)) = bodies.get(closure.proto.index()) else {
            continue;
        };
        if !matches!(stmt, HirStmt::LocalDecl(_))
            || (reads.get(&local) != pcall_inputs.inputs.get(&local)
                && !matches!(
                    key.0,
                    HirLuauInliningBody::ClosureFactory { .. }
                        | HirLuauInliningBody::SeededPredicate { .. }
                        | HirLuauInliningBody::ConstantControl { .. }
                        | HirLuauInliningBody::NumericRepeat { .. }
                        | HirLuauInliningBody::GuardedCounter { .. }
                        | HirLuauInliningBody::ResetCounter { .. }
                        | HirLuauInliningBody::ArrayFold { .. }
                        | HirLuauInliningBody::NestedSearch { .. }
                        | HirLuauInliningBody::CallingValue { .. }
                        | HirLuauInliningBody::CallingSharedValue { .. }
                        | HirLuauInliningBody::CallingObservedValue { .. }
                        | HirLuauInliningBody::CallingReadPair { .. }
                        | HirLuauInliningBody::ConditionalMethod { .. }
                        | HirLuauInliningBody::RepeatPrefix { .. }
                        | HirLuauInliningBody::RepeatLookup { .. }
                        | HirLuauInliningBody::CounterRepeat { .. }
                        | HirLuauInliningBody::GenericLookupWhile { .. }
                        | HirLuauInliningBody::GenericCounter { .. }
                        | HirLuauInliningBody::GenericBreak { .. }
                        | HirLuauInliningBody::CounterWhile { .. }
                        | HirLuauInliningBody::StatefulGenericWhile { .. }
                ))
            || writes.get(&local) != Some(&1)
        {
            continue;
        }
        let capture = match (key.0, closure.captures.as_slice()) {
            (HirLuauInliningBody::CapturedValue | HirLuauInliningBody::PublishedTableFactory { .. }, [capture])
                if capture.mode == HirCaptureMode::ByValue =>
            {
                match capture.binding {
                    HirBinding::Local(local) if writes.get(&local) == Some(&1) => Some(local),
                    _ => continue,
                }
            }
            (HirLuauInliningBody::CapturedValue | HirLuauInliningBody::PublishedTableFactory { .. }, _) => continue,
            (HirLuauInliningBody::ClosureFactory { .. }, [capture])
                if capture.mode == HirCaptureMode::ByValue
                    && capture.binding == HirBinding::Local(local) =>
            {
                Some(local)
            }
            (HirLuauInliningBody::ClosureFactory { .. }, _) => continue,
            (
                HirLuauInliningBody::CapturedConcatSum | HirLuauInliningBody::CapturedAddIdentity,
                [capture],
            ) if capture.mode == HirCaptureMode::ByReference => match capture.binding {
                HirBinding::Local(local) => Some(local),
                _ => continue,
            },
            (
                HirLuauInliningBody::CapturedConcatSum | HirLuauInliningBody::CapturedAddIdentity,
                _,
            ) => continue,
            (HirLuauInliningBody::CapturedCallablePair, captures)
                if !captures.is_empty() && captures.iter().all(|capture|
                    capture.mode == HirCaptureMode::ByValue
                        && matches!(capture.binding, HirBinding::Local(local) if writes.get(&local) == Some(&1))) => None,
            (HirLuauInliningBody::CapturedAppendTransfer { .. }, [trace, target, source])
                if trace.mode == HirCaptureMode::ByValue && source.mode == HirCaptureMode::ByValue
                    && target.mode == HirCaptureMode::ByReference
                    && [trace, source].iter().all(|capture| matches!(capture.binding,
                        HirBinding::Local(local) if writes.get(&local) == Some(&1)))
                    && matches!(target.binding, HirBinding::Local(_)) => None,
            (_, []) => None,
            _ => continue,
        };
        let Some(creation) = closure.source_site else {
            continue;
        };
        if candidates
            .insert(
                key.clone(),
                Callee {
                    local,
                    child: closure.proto,
                    declaration: index,
                    creation,
                    field: key.1.clone(),
                    body: key.0,
                    capture,
                    parameter_name: parameter_names[closure.proto.index()].clone(),
                    result_name: result_names[closure.proto.index()].clone(),
                    factory: factories[closure.proto.index()].clone(),
                    returned_call: returned_calls[closure.proto.index()].clone(),
                    conditional_method: conditional_methods[closure.proto.index()].clone(),
                    repeat_prefix: repeat_prefixes[closure.proto.index()].clone(),
                    literal_choice: literal_choices[closure.proto.index()].clone(),
                    value_expression: value_expressions[closure.proto.index()].clone(),
                    capture_locals: closure
                        .captures
                        .iter()
                        .filter_map(|capture| match capture.binding {
                            HirBinding::Local(local) => Some(local),
                            _ => None,
                        })
                        .collect(),
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

fn body_key(proto: &HirProto) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    if let [HirStmt::Return(ret)] = proto.body.stmts.as_slice()
        && ret.values.fixed == [HirExpr::ParamRef(proto.params[0])]
        && ret.values.tail.is_none()
        && proto.upvalues.is_empty()
    {
        return Some((HirLuauInliningBody::Identity, "".into()));
    }
    if let [HirStmt::Return(ret)] = proto.body.stmts.as_slice()
        && let ([value], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
        && let Some(field) = frozen_index_key(value, &HirExpr::ParamRef(proto.params[0]))
    {
        return Some((HirLuauInliningBody::FrozenTableIndex, field.clone()));
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
    table_key(table, &HirExpr::ParamRef(proto.params[0]))
        .cloned()
        .map(|field| (HirLuauInliningBody::UnpackedTable, field))
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

fn library_call<'a>(expr: &'a HirExpr, name: &str) -> Option<&'a crate::hir::common::HirCallExpr> {
    let HirExpr::Call(call) = expr else {
        return None;
    };
    let HirExpr::TableAccess(access) = &call.callee else {
        return None;
    };
    (!call.is_method()
        && matches!(&access.base, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("table"))
        && matches!(&access.key, HirExpr::String(key) if key.as_utf8() == Some(name)))
    .then_some(call)
}

fn frozen_index_key<'a>(value: &'a HirExpr, input: &HirExpr) -> Option<&'a crate::LuaString> {
    let HirExpr::TableAccess(index) = value else {
        return None;
    };
    if !matches!(index.key, HirExpr::Integer(1)) {
        return None;
    }
    let pack = library_call(&index.base, "pack")?;
    if !pack.args.fixed.is_empty() {
        return None;
    }
    let tail = pack.args.tail.as_ref()?;
    if tail.exact_width().is_some() {
        return None;
    }
    let freeze = library_call(tail.as_expr(), "freeze")?;
    let ([HirExpr::LogicalOr(logical)], None) = (freeze.args.fixed.as_slice(), &freeze.args.tail)
    else {
        return None;
    };
    let (HirExpr::TableAccess(access), HirExpr::TableConstructor(empty)) =
        (&logical.lhs, &logical.rhs)
    else {
        return None;
    };
    let HirExpr::String(field) = &access.key else {
        return None;
    };
    (&access.base == input
        && empty.fields.is_empty()
        && empty.trailing_multivalue.is_none()
        && field
            .as_utf8()
            .is_some_and(|name| DecompileDialect::Luau.is_identifier_name(name)))
    .then_some(field)
}

fn indexed_candidate<'a>(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    run: &[&HirStmt],
    callees: &'a BTreeMap<(HirLuauInliningBody, crate::LuaString), Callee>,
    positions: &[usize],
) -> Option<(Plan, &'a Callee)> {
    let sink = run.len().checked_sub(1)?;
    let (result, HirExpr::TableAccess(access)) = scalar_local(run[sink])? else {
        return None;
    };
    let base = facts.trusted_local_home_slot(result)?;
    let mut builder = frame_builder(context, run, facts, DecompileDialect::Luau, base.slot())?;
    let (call, field) = builder.expanded_index(access, sink, base.slot())?;
    let callee = callees.get(&(HirLuauInliningBody::FrozenTableIndex, field))?;
    let seed = builder.first_event?;
    if callee.declaration >= positions[seed] {
        return None;
    }
    builder.finish_event(sink)?;
    Some((
        Plan {
            prefix_at_sink: false,
            luau_function_declaration: false,
            start: seed,
            sink,
            base,
            values: vec![HirExpr::Call(Box::new(call))].into(),
            result_locals: vec![result],
            assignment_targets: Vec::new(),
            luau_compound_global: false,
            indexed_target: None,
            continuing_root: None,
            retained_copies: Vec::new(),
            replayed_effects: Vec::new(),
            removed: Vec::new(),
        },
        callee,
    ))
}

impl FrameBuilder<'_> {
    /// 原 B+1 参数分配和 B+2 body 准备属于同一个展开调用；消费后恢复外层
    /// frame 语境，事件游标继续前进，GETTABLEN 的语句终点由外层消费。
    pub(in crate::hir::simplify::call_frames) fn expanded_index(
        &mut self,
        access: &crate::hir::common::HirTableAccess,
        before: usize,
        slot: usize,
    ) -> Option<(HirCallExpr, crate::LuaString)> {
        let context = self.native?;
        let callees = context.expanded_callees?;
        let base = HomeSlotKey::new(slot, 0);
        let layout = self.facts.native_table_read_layout(access)?;
        let crate::hir::common::HirOperationSources::Single(result_site) = access.sources else {
            return None;
        };
        // 后面的闭包可能复用同一物理槽；是否存在别名须按原结果产生时点证明。
        // closed 仍代表跨词法退出的约束，不能由这份瞬时别名事实解除。
        if self.dialect != DecompileDialect::Luau
            || self.facts.table_read_result_home(access) != Some(base)
            || layout.base != HomeSlotKey::new(slot + 2, 0)
            || layout.key.is_some()
            || !matches!(access.key, HirExpr::Integer(1))
            || (context.barred.contains(&base)
                && !self.facts.operation_result_reference_unaliased(result_site))
            || context.closed.contains(&base)
        {
            return None;
        }
        let input_home = HomeSlotKey::new(slot + 1, 0);
        let candidates = self.expanded_inputs.get(&input_home)?;
        let boundary = candidates.partition_point(|&(index, _)| index < before);
        let &(seed, input) = candidates.get(boundary.checked_sub(1)?)?;
        if seed < self.next_event {
            return None;
        }
        let (_, HirExpr::TableConstructor(input_table)) = scalar_local(self.run[seed])? else {
            return None;
        };
        let crate::hir::common::HirOperationSources::Single(input_site) = input_table.sources
        else {
            return None;
        };
        let (input_value, parameter_name) =
            expanded_argument(self, input, seed, before, input_home, result_site.instr)?;
        let previous_base = std::mem::replace(&mut self.base, slot + 2);
        let previous_top = self.declaration_reserved_top.replace(slot + 2);
        let packed = self.expr(&access.base, before, slot + 2, None, false, true, None);
        self.base = previous_base;
        self.declaration_reserved_top = previous_top;
        let body = HirExpr::TableAccess(Box::new(crate::hir::common::HirTableAccess {
            base: packed?,
            ..access.clone()
        }));
        let field = frozen_index_key(&body, &HirExpr::LocalRef(input))?.clone();
        let callee = callees.get(&(HirLuauInliningBody::FrozenTableIndex, field.clone()))?;
        if callee.creation.proto != input_site.proto
            || callee.creation.instr.index() >= input_site.instr.index()
            || self.facts.trusted_local_home_slot(callee.local)?.slot() >= slot
            || parameter_name.is_some() && parameter_name != callee.parameter_name
        {
            return None;
        }
        let HirExpr::TableAccess(body) = body else {
            unreachable!()
        };
        let HirExpr::Call(call) = body.base else {
            return None;
        };
        let mut call = *call;
        call.required_luau_inlining = Some(result_site);
        prepare_invocation(callee, &mut call, input_value);
        Some((call, field))
    }
}

/// 构造器 owner 已吸收 SETLIST 时，仍消费同一 allocation/batch 来源；不因
/// debug initializer 提前完成树化而另造一个缺少原缓冲区身份的展开协议。
fn completed_candidate<'a>(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    run: &[&HirStmt],
    callees: &'a BTreeMap<(HirLuauInliningBody, crate::LuaString), Callee>,
    positions: &[usize],
) -> Option<(Plan, &'a Callee)> {
    let sink = run.len().checked_sub(1)?;
    let (result, HirExpr::TableConstructor(table)) = scalar_local(run[sink])? else {
        return None;
    };
    let base = facts.trusted_local_home_slot(result)?;
    let batch = facts.native_allocation_batch_layout(table)?;
    let end = facts.native_allocation_batch_site(table)?;
    if facts.allocation_result_home(table) != Some(base)
        || batch.base != base
        || batch.buffer != HomeSlotKey::new(base.slot() + 2, 0)
        || batch.fixed_width.is_some()
        || batch.start_index != 1
        || !table.fields.is_empty()
        || !table.matches_allocation_capacity(0)
        || context.closed.contains(&base)
        || context.barred.contains(&base)
    {
        return None;
    }
    let input_home = HomeSlotKey::new(base.slot() + 1, 0);
    let (seed, input) = run.iter().enumerate().find_map(|(index, stmt)| {
        let (local, HirExpr::TableConstructor(input)) = scalar_local(stmt)? else {
            return None;
        };
        (facts.trusted_local_home_slot(local) == Some(input_home)
            && facts.allocation_result_home(input) == Some(input_home))
        .then_some((index, local))
    })?;
    let key = table_key(table, &HirExpr::LocalRef(input))?;
    let callee = callees.get(&(HirLuauInliningBody::UnpackedTable, key.clone()))?;
    if callee.declaration >= positions[seed]
        || facts.trusted_local_home_slot(callee.local)?.slot() >= base.slot()
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, DecompileDialect::Luau, base.slot())?;
    let (input_value, parameter_name) =
        expanded_argument(&mut builder, input, seed, sink, input_home, end.instr)?;
    if parameter_name.is_some() && parameter_name != callee.parameter_name {
        return None;
    }
    builder.base = batch.buffer.slot();
    builder.declaration_reserved_top = Some(batch.buffer.slot());
    let HirExpr::Call(call) = table.trailing_multivalue.as_ref()?.as_expr() else {
        return None;
    };
    let mut call = builder.call(call, sink, batch.buffer.slot(), false, CallWidth::Open)?;
    call.required_luau_inlining = Some(end);
    builder.finish_event(sink)?;
    Some((
        invocation_plan(
            callee,
            call,
            input_value,
            base,
            builder.first_event?,
            sink,
            result,
        ),
        callee,
    ))
}

fn invocation_plan(
    callee: &Callee,
    mut call: HirCallExpr,
    input: HirExpr,
    base: HomeSlotKey,
    start: usize,
    sink: usize,
    result: LocalId,
) -> Plan {
    prepare_invocation(callee, &mut call, input);
    Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink,
        base,
        values: vec![HirExpr::Call(Box::new(call))].into(),
        result_locals: vec![result],
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    }
}

fn prepare_invocation(callee: &Callee, call: &mut HirCallExpr, input: HirExpr) {
    call.source_site = None;
    call.callee = HirExpr::LocalRef(callee.local);
    call.args = vec![input].into();
    call.fastcall = None;
    call.method_key = None;
    call.callee_root_handoff = None;
    call.method_rewrite_transaction = None;
    call.plain_method_syntax = false;
    call.argument_roots.clear();
    call.frame_root_ends.clear();
}

/// 原内联参数的 debug 身份由同一 child 的形参承接；这里只准许精确覆盖整个
/// 展开体的区间。普通 local 即使同名或同槽，也不能借此移除其声明。
fn expanded_argument(
    builder: &mut FrameBuilder<'_>,
    input: LocalId,
    seed: usize,
    before: usize,
    home: HomeSlotKey,
    end: crate::transformer::InstrRef,
) -> Option<(HirExpr, Option<String>)> {
    use crate::hir::common::{HirInlineDisposition, HirOperationSources};
    let context = builder.native?;
    let name = context.proto.local_debug_hints.get(input.index())?.clone();
    let scope_id = *context.proto.local_debug_scopes.get(input.index())?;
    if name.is_none() && scope_id.is_none() {
        let value = builder.expr(
            &HirExpr::LocalRef(input),
            before,
            home.slot(),
            None,
            false,
            true,
            None,
        )?;
        return Some((value, None));
    }
    let name = name?;
    let scope = context.proto.debug_scopes.get(scope_id?)?.as_ref()?;
    let (_, value @ HirExpr::TableConstructor(table)) = scalar_local(builder.run[seed])? else {
        return None;
    };
    let HirOperationSources::Single(allocation) = table.sources else {
        return None;
    };
    if scope.end_instr?.index() != end.index() + 1
        || scope.initializer_temp != builder.facts.operation_result_temp(allocation)
        || scope.initializer_temp.is_none()
        || builder.definitions.get(&input)?.as_slice() != [seed]
        || !builder
            .facts
            .complete_local_definition_write_homes(input)
            .iter()
            .copied()
            .eq([home])
        || context.closed.contains(&home)
        || !builder.facts.allocation_result_reference_unaliased(table)
        || matches!(context.proto.inline_dispositions.local(input), HirInlineDisposition::Preserve(reasons)
            if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    {
        return None;
    }
    // FrameBuilder 仍消费全部原构造事件；仅把已证明的参数绑定交给后续内联合同。
    let rebuilt = if builder.constructors.contains_key(&seed) {
        builder.constructor(seed, table, home.slot())?
    } else {
        let rebuilt = builder.expr(value, seed, home.slot(), None, false, true, None)?;
        builder.finish_event(seed)?;
        rebuilt
    };
    let HirExpr::TableConstructor(table) = &rebuilt else {
        return None;
    };
    let mut last = allocation.instr;
    if table.trailing_multivalue.is_some() {
        return None;
    }
    for field in &table.fields {
        let HirTableField::Record(record) = field else {
            return None;
        };
        match record.write_sources {
            HirOperationSources::Single(site) if site.proto == allocation.proto => {
                last = last.max(site.instr);
            }
            // 模板预置字段没有 SETTABLE；其值必须由原 DUPTABLE 一次初始化。
            HirOperationSources::Unknown
                if matches!(table.allocation, HirTableAllocation::LuauTemplate { .. })
                    && tables::literal_rk(&record.value) => {}
            _ => return None,
        }
    }
    (scope.initializer_end_instr == Some(last)).then_some((rebuilt, Some(name)))
}

fn candidate<'a>(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    run: &[&HirStmt],
    callees: &'a BTreeMap<(HirLuauInliningBody, crate::LuaString), Callee>,
    positions: &[usize],
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
    let callee = callees.get(&(HirLuauInliningBody::UnpackedTable, key.clone()))?;
    let input_seed = builder.definition(input, seed)?;
    let home = HomeSlotKey::new(base.slot() + 1, 0);
    if callee.declaration >= positions[input_seed]
        || facts.trusted_local_home_slot(input) != Some(home)
        || facts.trusted_local_home_slot(callee.local)?.slot() >= base.slot()
        || !matches!(
            scalar_local(run[input_seed])?.1,
            HirExpr::TableConstructor(_)
        )
    {
        return None;
    }
    let (input_value, parameter_name) = expanded_argument(
        &mut builder,
        input,
        input_seed,
        seed,
        home,
        batch.source_site?.instr,
    )?;
    if builder.next_event != seed
        || parameter_name.is_some() && parameter_name != callee.parameter_name
    {
        return None;
    }
    // 这两个槽仅是已求值的参数和低结果预留区，不修改计划的源码前缀 base。
    builder.base = base.slot() + 2;
    builder.declaration_reserved_top = Some(base.slot() + 2);
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
    call.required_luau_inlining = batch.source_site;
    Some((
        invocation_plan(
            callee,
            call,
            input_value,
            base,
            builder.first_event?,
            run.len() - 1,
            result,
        ),
        callee,
    ))
}

fn suffix_replayed(
    preview: &Preview,
    plans: &[Plan],
    first: usize,
    facts: &ProtoPromotionFacts,
    structured: bool,
) -> bool {
    let sinks = plans.iter().map(|plan| plan.sink).collect::<BTreeSet<_>>();
    let floor = plans
        .iter()
        .filter(|plan| plan.sink >= first)
        .map(|plan| plan.base.slot())
        .min();
    let mut returned = false;
    let mut valid = true;
    prefix::coordinates::visit(&preview.proto.body, &mut 0, &mut |index, kind, stmt| {
        if kind != PointKind::Statement
            || index < first
            || preview.removed[index]
            || sinks.contains(&index)
        {
            return;
        }
        // 词法包装自身没有 VM 事件；其内部调用、声明及出口仍按相同 DFS 坐标
        // 逐项重放并验证前缀。不能因 root_scopes 恢复了旧结果域而丢掉展开帧能力。
        if matches!(stmt, HirStmt::Block(_)) {
            return;
        }
        if structured {
            match stmt {
                HirStmt::If(branch) if control::direct_test(branch, facts) => return,
                HirStmt::NumericFor(loop_) if facts.numeric_for_body_frame(loop_).is_some() => {
                    return;
                }
                HirStmt::GenericFor(loop_) if facts.generic_for_body_frame(loop_).is_some() => {
                    return;
                }
                HirStmt::Assign(assign) if control::direct_boolean_write(assign, facts) => return,
                HirStmt::Assign(assign) if control::direct_increment(assign, facts) => return,
                HirStmt::Assign(assign)
                    if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                    ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None)
                    if facts.trusted_local_home_slot(*target).is_some() && facts.trusted_local_home_slot(*source).is_some()) =>
                {
                    return;
                }
                _ => {}
            }
        }
        // 原低槽 COPY 不使用 scratch；常量直接写入已有 binding，也不占 freereg。
        // 后者可以高于最早帧入口，声明身份与后继帧前缀仍由同批 prefix 验证。
        let below_frame = |local| {
            facts
                .trusted_local_home_slot(local)
                .is_some_and(|home| floor.is_some_and(|floor| home.slot() < floor))
        };
        if matches!(stmt, HirStmt::Assign(assign)
            if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
            && scalar_local(stmt).is_some_and(|(local, value)| {
                facts.trusted_local_home_slot(local).is_some()
                    && match value {
                        HirExpr::LocalRef(source) => below_frame(local) && below_frame(*source),
                        HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_) => true,
                        _ => false,
                    }
            })
        {
            return;
        }
        if matches!(stmt, HirStmt::Assign(assign)
            if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none()
                && matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                    ([HirLValue::Global(global)], [HirExpr::LocalRef(local)], None)
                        if facts.trusted_local_home_slot(*local).is_some()
                            && facts.global_write_value_home(global, DecompileDialect::Luau) == facts.trusted_local_home_slot(*local)))
        {
            // 既有 local 直接写原环境槽不分配 scratch，身份仍由整批后缀验证。
            return;
        }
        if let HirStmt::Return(ret) = stmt {
            valid &= ret.values.is_empty() && facts.native_return_frame(ret).is_some();
            returned = true;
        } else if matches!(stmt, HirStmt::Assign(assign)
        if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
            ([HirLValue::TableAccess(access)], [HirExpr::LocalRef(value)], None)
            if facts.native_table_write_layout(access).is_some_and(|layout|
                facts.direct_table_write_input_home(access, 0) == Some(layout.base)
                    && layout.value.is_some()
                    && facts.trusted_local_home_slot(*value) == layout.value
                    && match layout.key {
                        Some(key) => facts.direct_table_write_input_home(access, 1) == Some(key),
                        None => matches!(access.key, HirExpr::String(_) | HirExpr::Integer(1..=256)),
                    })))
        {
            // 已声明的表、key 和值直接执行原 SETTABLE，不创建准备槽。
            // 当前词法声明仍由完整 prefix scan 核对，字段写也仍在原位置。
        } else {
            valid = false;
        }
    });
    valid && returned
}

impl FrameBuilder<'_> {
    /// 已证明展开调用的固定结果身份，供各外层参数、索引和运算帧共同消费。
    pub(in crate::hir::simplify::call_frames) fn expanded_call_result(
        &self,
        call: &HirCallExpr,
    ) -> Option<TempId> {
        self.native?
            .seeded_predicates
            .and_then(|frames| frames.result(call))
            .or_else(|| self.calling_value_result(call))
    }
}
