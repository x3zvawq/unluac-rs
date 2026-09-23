//! 这个子模块负责把构造器生产者内联进字段值。
//!
//! 它依赖 `bindings` 已经识别好的同一绑定和 pending producer 列表，只尝试安全内联字段/
//! callee/access-base 值，不会在这里决定整段 region 的分段边界。
//! producer 只有一个消费 owner；内联同时记录其求值事件，region builder 证明事件顺序
//! 未变后才提交。例如：`local v = f(); t.x = v` 只在 `f()` 仍位于同一事件位置时折叠。

use crate::hir::common::{
    HirBinaryExpr, HirBlock, HirCallExpr, HirDecisionExpr, HirDecisionTarget, HirExpr,
    HirLogicalExpr, HirRecordField, HirTableConstructor, HirTableField, HirUnaryExpr, HirValuePack,
};
use crate::hir::expr_safety::expr_requires_ordered_snapshot;

use super::bindings::{BindingIndex, BindingUseSummary, binding_from_expr};
use super::{ConstructorEvalEvent, PendingProducer, ProducerSourcePreservation};

pub(super) struct InlineContext<'a> {
    block: &'a HirBlock,
    binding_index: &'a BindingIndex,
    pending_producers: &'a [PendingProducer],
    producer_index_by_binding: &'a [Option<usize>],
    consumed_bindings: &'a mut [bool],
    eval_events: &'a mut Vec<ConstructorEvalEvent>,
    inside_producer_value: bool,
    remaining_uses: BindingUseSummary<'a>,
}

pub(super) struct InlineRewriteState<'a> {
    pub(super) consumed_bindings: &'a mut [bool],
    pub(super) eval_events: &'a mut Vec<ConstructorEvalEvent>,
}

impl<'a> InlineContext<'a> {
    pub(super) fn new(
        block: &'a HirBlock,
        binding_index: &'a BindingIndex,
        pending_producers: &'a [PendingProducer],
        producer_index_by_binding: &'a [Option<usize>],
        state: InlineRewriteState<'a>,
        remaining_uses: BindingUseSummary<'a>,
    ) -> Self {
        Self {
            block,
            binding_index,
            pending_producers,
            producer_index_by_binding,
            consumed_bindings: state.consumed_bindings,
            eval_events: state.eval_events,
            inside_producer_value: false,
            remaining_uses,
        }
    }
}

pub(super) fn inline_constructor_value(
    context: &mut InlineContext<'_>,
    value: &HirExpr,
) -> Option<HirExpr> {
    inline_constructor_value_inner(context, value)
}

fn inline_constructor_value_inner(
    context: &mut InlineContext<'_>,
    value: &HirExpr,
) -> Option<HirExpr> {
    if let Some(binding) = binding_from_expr(value)
        && let Some(binding_id) = context.binding_index.id_of(binding)
        && let Some(producer_index) = context
            .producer_index_by_binding
            .get(binding_id)
            .and_then(|producer_index| *producer_index)
    {
        let producer = &context.pending_producers[producer_index];
        if producer.source_preservation == ProducerSourcePreservation::UnsupportedShape {
            // 候选拒绝[PolicyBoundary]：scanner 已把逐槽 primitive/vararg、snapshot 与
            // allocation 分流；这里只剩 permissive 输出必须原样保留的 Unresolved 失败证据。
            return None;
        }
        if context.remaining_uses.contains(producer.binding_id) {
            match producer.source_preservation {
                ProducerSourcePreservation::Safe => {}
                ProducerSourcePreservation::InertWholeStatement => {}
                ProducerSourcePreservation::PreservedIdentity => {
                    // 候选拒绝[SemanticBarrier:BindingIdentity]：debug 声明或调用帧前缀
                    // 的保留要求不允许把物化值提前到该声明之前（regress_577）。
                    return None;
                }
                ProducerSourcePreservation::ObservableReplay => {
                    // 候选拒绝[SemanticBarrier:EvalCount]：保留声明并把 `mark()` producer
                    // 内联到 field 会执行两次；删除声明又会断开后续 use（regress_235）。
                    return None;
                }
                ProducerSourcePreservation::UnsupportedShape => {
                    unreachable!("unsupported failure evidence must keep its original producer")
                }
            }
        }
        // 候选拒绝[SemanticBarrier:EvalCount]：同一 producer 被第二次消费时再次展开会
        // 重复求值；`local v = mark(); t[v] = v` 必须只调用一次，见 regress_235。
        if context.consumed_bindings[producer.binding_id] {
            return None;
        }
        let producer_value = producer.source.value(context.block)?;
        context.consumed_bindings[producer.binding_id] = true;
        let producer_value = producer_value.clone();
        // producer 值继续递归展开；callee/access-base 的括号由 Generate 的
        // `PREC_PREFIX` 规则统一承载，不需要在 HIR 限制表达式形状。
        let was_inside_producer_value = context.inside_producer_value;
        context.inside_producer_value = true;
        let inlined = inline_constructor_value_inner(context, &producer_value);
        context.inside_producer_value = was_inside_producer_value;
        let inlined = inlined?;
        if expr_requires_ordered_snapshot(&producer_value) {
            context
                .eval_events
                .push(ConstructorEvalEvent::Producer(producer_index));
        }
        return Some(inlined);
    }

    let records_barrier = !context.inside_producer_value && expr_requires_ordered_snapshot(value);
    let inlined = match value {
        HirExpr::Unary(unary) => HirExpr::Unary(Box::new(HirUnaryExpr {
            source_site: unary.source_site,
            op: unary.op,
            expr: inline_constructor_value_inner(context, &unary.expr)?,
        })),
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(HirBinaryExpr {
            source_site: binary.source_site,
            op: binary.op,
            lhs: inline_constructor_value_inner(context, &binary.lhs)?,
            rhs: inline_constructor_value_inner(context, &binary.rhs)?,
        })),
        HirExpr::TableAccess(access) => {
            HirExpr::TableAccess(Box::new(crate::hir::common::HirTableAccess {
                sources: access.sources.clone(),
                metamethod_free: access.metamethod_free,
                base: inline_constructor_value_inner(context, &access.base)?,
                key: inline_constructor_value_inner(context, &access.key)?,
                method_setup_protocol: access.method_setup_protocol,
            }))
        }
        HirExpr::Call(call) => HirExpr::Call(Box::new(inline_constructor_call(context, call)?)),
        HirExpr::LogicalAnd(logical) => {
            inline_short_circuit_expr(context, logical, HirExpr::LogicalAnd)?
        }
        HirExpr::LogicalOr(logical) => {
            inline_short_circuit_expr(context, logical, HirExpr::LogicalOr)?
        }
        HirExpr::TableConstructor(table) => {
            HirExpr::TableConstructor(Box::new(inline_nested_constructor(context, table)?))
        }
        HirExpr::Decision(decision) => {
            HirExpr::Decision(Box::new(inline_decision_entry(context, decision)?))
        }
        HirExpr::Closure(_)
            if expr_mentions_any_pending_binding(
                value,
                context.binding_index,
                context.producer_index_by_binding,
            ) =>
        {
            // 候选拒绝[SemanticBarrier:Capture]：closure capture 是 upvalue 绑定元数据，
            // AST lowering 只读取 capture 的 binding/name，不会求值任意替换表达式；把
            // producer 塞进 capture 会既删除原求值又无法在源码中重放，并破坏
            // `local v = mark(); t.x = function() return v end` 的 ByReference 身份。
            return None;
        }
        _ => value.clone(),
    };
    if records_barrier {
        context.eval_events.push(ConstructorEvalEvent::Barrier);
    }
    Some(inlined)
}

fn inline_nested_constructor(
    context: &mut InlineContext<'_>,
    table: &HirTableConstructor,
) -> Option<HirTableConstructor> {
    // HIR/AST 都按 field 顺序求值，record 内先 key 后 value；逐槽递归可让 event proof
    // 比较 producer 与既有 call/lookup 的完整相对次序，而不是把嵌套 constructor 当黑盒。
    let fields = table
        .fields
        .iter()
        .map(|field| match field {
            HirTableField::Array(value) => Some(HirTableField::Array(
                inline_constructor_value_inner(context, value)?,
            )),
            HirTableField::Record(field) => {
                let key = inline_constructor_value_inner(context, &field.key)?;
                let value = inline_constructor_value_inner(context, &field.value)?;
                Some(HirTableField::Record(HirRecordField {
                    write_sources: field.write_sources.clone(),
                    key,
                    value,
                }))
            }
        })
        .collect::<Option<Vec<_>>>()?;
    let trailing_multivalue = match &table.trailing_multivalue {
        Some(tail) => Some(tail.clone().try_map_call(|call| {
            let mapped = inline_constructor_call(context, &call)?;
            // `try_map_call` 绕过表达式 wrapper；尾调用自身仍是一个有序事件。
            context.eval_events.push(ConstructorEvalEvent::Barrier);
            Some(mapped)
        })?),
        None => None,
    };
    Some(HirTableConstructor {
        sources: table.sources.clone(),
        allocation: table.allocation.clone(),
        implicit_template_fields: table.implicit_template_fields.clone(),
        fields,
        trailing_multivalue,
    })
}

fn inline_decision_entry(
    context: &mut InlineContext<'_>,
    decision: &HirDecisionExpr,
) -> Option<HirDecisionExpr> {
    let entry_index = decision.entry.index();
    let entry = decision.nodes.get(entry_index)?;
    for (index, node) in decision.nodes.iter().enumerate() {
        let conditional_test_mentions = index != entry_index
            && expr_mentions_any_pending_binding(
                &node.test,
                context.binding_index,
                context.producer_index_by_binding,
            );
        let conditional_target_mentions = [&node.truthy, &node.falsy].iter().any(|target| {
            matches!(
                target,
                HirDecisionTarget::Expr(expr)
                    if expr_mentions_any_pending_binding(
                        expr,
                        context.binding_index,
                        context.producer_index_by_binding,
                    )
            )
        });
        if conditional_test_mentions || conditional_target_mentions {
            // 候选拒绝[SemanticBarrier:EvalCount]：只有 entry test 必达；把
            // `local v = mark(); result = cond and v or false` 的 producer 移进后继
            // test/target 会把一次无条件求值变为条件求值。共享 DAG 不改变该路径事实。
            return None;
        }
    }

    let mut nodes = decision.nodes.clone();
    nodes[entry_index].test = inline_constructor_value_inner(context, &entry.test)?;
    Some(HirDecisionExpr {
        emit_as_luau_if: false,
        entry: decision.entry,
        nodes,
    })
}

pub(super) fn inline_constructor_call(
    context: &mut InlineContext<'_>,
    call: &HirCallExpr,
) -> Option<HirCallExpr> {
    let inline_args = |context: &mut InlineContext<'_>, args: &HirValuePack| {
        let fixed = args
            .fixed
            .iter()
            .map(|arg| inline_constructor_value_inner(context, arg))
            .collect::<Option<Vec<_>>>()?;
        let tail = match &args.tail {
            Some(tail) => Some(tail.clone().try_map_call(|nested| {
                let mapped = inline_constructor_call(context, &nested)?;
                // `try_map_call` bypasses the normal expression wrapper, so account for the
                // nested tail call explicitly in the eval-order proof.
                context.eval_events.push(ConstructorEvalEvent::Barrier);
                Some(mapped)
            })?),
            None => None,
        };
        Some(HirValuePack { fixed, tail })
    };

    // Luau FASTCALL materializes direct arguments before fallback callee setup.  The metadata
    // is part of HIR's evaluation-order contract even though AST still prints a normal call.
    let (callee, args) = if call.fastcall.is_some() {
        let args = inline_args(context, &call.args)?;
        let callee = inline_constructor_value_inner(context, &call.callee)?;
        (callee, args)
    } else {
        let callee = inline_constructor_value_inner(context, &call.callee)?;
        let args = inline_args(context, &call.args)?;
        (callee, args)
    };
    Some(HirCallExpr {
        required_luau_inlining: call.required_luau_inlining,
        source_site: call.source_site,
        argument_roots: call.argument_roots.clone(),
        frame_root_ends: call.frame_root_ends.clone(),
        callee,
        args,
        method: call.method,
        fastcall: call.fastcall,
        method_key: call.method_key.clone(),
        callee_root_handoff: call.callee_root_handoff,
        method_rewrite_transaction: call.method_rewrite_transaction,
        plain_method_syntax: false,
        boolean_prewrite_arguments: call.boolean_prewrite_arguments.clone(),
    })
}

fn inline_short_circuit_expr(
    context: &mut InlineContext<'_>,
    logical: &HirLogicalExpr,
    ctor: fn(Box<HirLogicalExpr>) -> HirExpr,
) -> Option<HirExpr> {
    // 短路右侧不是无条件求值位置；如果它引用 pending producer，
    // 把 producer 折进去会把原本已执行的求值变成条件执行，或留下未定义引用。
    if expr_mentions_any_pending_binding(
        &logical.rhs,
        context.binding_index,
        context.producer_index_by_binding,
    ) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：producer 原本无条件先求值；搬入短路右臂会
        // 变成条件求值，例如 `v = mark(); t.x = false and v` 不能内联为一次表达式。
        return None;
    }

    Some(ctor(Box::new(HirLogicalExpr {
        preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
        lhs: inline_constructor_value_inner(context, &logical.lhs)?,
        rhs: logical.rhs.clone(),
    })))
}

pub(super) fn expr_mentions_any_pending_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producer_index_by_binding: &[Option<usize>],
) -> bool {
    crate::hir::visit::any_expr(expr, &mut |expr| {
        binding_from_expr(expr)
            .and_then(|binding| binding_index.id_of(binding))
            .is_some_and(|binding_id| {
                producer_index_by_binding
                    .get(binding_id)
                    .is_some_and(Option::is_some)
            })
    })
}
