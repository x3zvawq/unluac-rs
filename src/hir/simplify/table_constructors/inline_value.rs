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
use super::{
    BindingId, ConstructorEvalEvent, PendingProducer, PendingProducerSource,
    ProducerSourcePreservation,
};

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
                ProducerSourcePreservation::DebugIdentity => {
                    // 候选拒绝[PolicyBoundary]：producer 声明虽可保留，但把 table field 提前
                    // 到 source-visible 声明之前会改变 hook 在该行观察到的 table 内容。
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
        let producer_value = pending_producer_value(context.block, producer)?;
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
            op: unary.op,
            expr: inline_constructor_value_inner(context, &unary.expr)?,
        })),
        HirExpr::Binary(binary) => HirExpr::Binary(Box::new(HirBinaryExpr {
            op: binary.op,
            lhs: inline_constructor_value_inner(context, &binary.lhs)?,
            rhs: inline_constructor_value_inner(context, &binary.rhs)?,
        })),
        HirExpr::TableAccess(access) => {
            HirExpr::TableAccess(Box::new(crate::hir::common::HirTableAccess {
                base: inline_constructor_value_inner(context, &access.base)?,
                key: inline_constructor_value_inner(context, &access.key)?,
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
                Some(HirTableField::Record(HirRecordField { key, value }))
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
        callee,
        args,
        method: call.method,
        fastcall: call.fastcall,
        method_key: call.method_key.clone(),
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
        lhs: inline_constructor_value_inner(context, &logical.lhs)?,
        rhs: logical.rhs.clone(),
    })))
}

pub(super) fn expr_mentions_any_pending_binding(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    producer_index_by_binding: &[Option<usize>],
) -> bool {
    expr_mentions_binding_where(expr, binding_index, |binding_id| {
        producer_index_by_binding
            .get(binding_id)
            .is_some_and(Option::is_some)
    })
}

fn expr_mentions_binding_where(
    expr: &HirExpr,
    binding_index: &BindingIndex,
    predicate: impl Fn(BindingId) -> bool + Copy,
) -> bool {
    if binding_from_expr(expr)
        .and_then(|binding| binding_index.id_of(binding))
        .is_some_and(predicate)
    {
        return true;
    }

    match expr {
        HirExpr::TableAccess(access) => {
            expr_mentions_binding_where(&access.base, binding_index, predicate)
                || expr_mentions_binding_where(&access.key, binding_index, predicate)
        }
        HirExpr::Unary(unary) => expr_mentions_binding_where(&unary.expr, binding_index, predicate),
        HirExpr::Binary(binary) => {
            expr_mentions_binding_where(&binary.lhs, binding_index, predicate)
                || expr_mentions_binding_where(&binary.rhs, binding_index, predicate)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_mentions_binding_where(&logical.lhs, binding_index, predicate)
                || expr_mentions_binding_where(&logical.rhs, binding_index, predicate)
        }
        HirExpr::Call(call) => {
            expr_mentions_binding_where(&call.callee, binding_index, predicate)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_mentions_binding_where(arg, binding_index, predicate))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(value) => {
                    expr_mentions_binding_where(value, binding_index, predicate)
                }
                HirTableField::Record(field) => {
                    expr_mentions_binding_where(&field.value, binding_index, predicate)
                        || expr_mentions_binding_where(&field.key, binding_index, predicate)
                }
            }) || table.trailing_multivalue.as_ref().is_some_and(|tail| {
                expr_mentions_binding_where(tail.as_expr(), binding_index, predicate)
            })
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_mentions_binding_where(&node.test, binding_index, predicate)
                || decision_target_mentions_binding_where(&node.truthy, binding_index, predicate)
                || decision_target_mentions_binding_where(&node.falsy, binding_index, predicate)
        }),
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_mentions_binding_where(&capture.value, binding_index, predicate)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
        HirExpr::TempRef(_) | HirExpr::LocalRef(_) => false,
    }
}

fn decision_target_mentions_binding_where(
    target: &HirDecisionTarget,
    binding_index: &BindingIndex,
    predicate: impl Fn(BindingId) -> bool + Copy,
) -> bool {
    match target {
        HirDecisionTarget::Expr(expr) => {
            expr_mentions_binding_where(expr, binding_index, predicate)
        }
        HirDecisionTarget::Node(_) | HirDecisionTarget::CurrentValue => false,
    }
}

fn pending_producer_value<'a>(
    block: &'a HirBlock,
    producer: &PendingProducer,
) -> Option<&'a HirExpr> {
    match producer.source {
        PendingProducerSource::Value {
            stmt_index,
            value_index,
        } => producer_source_value(block, stmt_index, value_index),
        PendingProducerSource::ImplicitNil { .. } => Some(&HirExpr::Nil),
    }
}

fn producer_source_value(
    block: &HirBlock,
    stmt_index: usize,
    value_index: usize,
) -> Option<&HirExpr> {
    let stmt = block.stmts.get(stmt_index)?;
    match stmt {
        crate::hir::common::HirStmt::LocalDecl(local_decl) => {
            local_decl.values.fixed.get(value_index)
        }
        crate::hir::common::HirStmt::Assign(assign) => assign.values.fixed.get(value_index),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::hir::common::{
        HirBlock, HirCapture, HirCaptureMode, HirClosureExpr, HirDecisionExpr, HirDecisionNode,
        HirDecisionNodeRef, HirDecisionTarget, HirExpr, HirLocalDecl, HirProtoRef, HirStmt,
        HirTableConstructor, HirTableField, HirUnresolvedExpr, HirValuePack, LocalId,
    };
    use crate::hir::promotion::ProtoPromotionFacts;

    use super::super::bindings::{
        BindingIndex, BindingOccurrenceIndex, BindingSlots, collect_stmt_binding_summary,
    };
    use super::super::{
        ConstructorEvalEvent, PendingProducer, PendingProducerSource, ProducerSourcePreservation,
        TableBinding,
    };
    use super::{InlineContext, InlineRewriteState, inline_constructor_value};

    fn inline_context_fixture() -> (
        HirBlock,
        BindingIndex,
        BindingOccurrenceIndex,
        Vec<PendingProducer>,
        Vec<Option<usize>>,
    ) {
        let local = LocalId(0);
        let block = HirBlock {
            stmts: vec![HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: HirValuePack::fixed(vec![HirExpr::String("value".into())]),
                initializer_merge_transaction: None,
            }))],
        };
        let mut binding_index = BindingIndex::new(0, 1);
        let summary = collect_stmt_binding_summary(&block.stmts[0], &mut binding_index);
        let occurrence_index = BindingOccurrenceIndex::new(
            &binding_index,
            &[summary],
            &BindingSlots::from_debug_hints(&[], &[None]),
            &BTreeSet::new(),
            &BindingSlots::from_debug_hints(&[], &[None]),
            &ProtoPromotionFacts::default(),
        );
        let binding = TableBinding::Local(local);
        let binding_id = binding_index
            .id_of(binding)
            .expect("producer binding must be interned");
        (
            block,
            binding_index,
            occurrence_index,
            vec![PendingProducer {
                binding,
                binding_id,
                source: PendingProducerSource::Value {
                    stmt_index: 0,
                    value_index: 0,
                },
                source_preservation: ProducerSourcePreservation::Safe,
            }],
            vec![Some(0)],
        )
    }

    #[test]
    fn pending_value_is_rewritten_inside_nested_constructor() {
        // Decision elimination can leave extracted scalar producers before a populated table
        // expression; the next fixed-point table pass must consume those references recursively.
        let (block, binding_index, occurrence_index, producers, producer_map) =
            inline_context_fixture();
        let mut consumed = vec![false];
        let mut events = Vec::new();
        let mut context = InlineContext::new(
            &block,
            &binding_index,
            &producers,
            &producer_map,
            InlineRewriteState {
                consumed_bindings: &mut consumed,
                eval_events: &mut events,
            },
            occurrence_index.remaining_uses_after(0),
        );
        let value = HirExpr::TableConstructor(Box::new(HirTableConstructor {
            fields: vec![HirTableField::Array(HirExpr::LocalRef(LocalId(0)))],
            trailing_multivalue: None,
        }));

        let rewritten = inline_constructor_value(&mut context, &value);

        assert_eq!(
            rewritten,
            Some(HirExpr::TableConstructor(Box::new(HirTableConstructor {
                fields: vec![HirTableField::Array(HirExpr::String("value".into()))],
                trailing_multivalue: None,
            })))
        );
        assert_eq!(consumed, vec![true]);
        assert_eq!(events, vec![ConstructorEvalEvent::Barrier]);
    }

    #[test]
    fn pending_value_is_not_moved_into_closure_capture_metadata() {
        let (block, binding_index, occurrence_index, producers, producer_map) =
            inline_context_fixture();
        let mut consumed = vec![false];
        let mut events = Vec::new();
        let mut context = InlineContext::new(
            &block,
            &binding_index,
            &producers,
            &producer_map,
            InlineRewriteState {
                consumed_bindings: &mut consumed,
                eval_events: &mut events,
            },
            occurrence_index.remaining_uses_after(0),
        );
        let value = HirExpr::Closure(Box::new(HirClosureExpr {
            proto: HirProtoRef(1),
            captures: vec![HirCapture {
                mode: HirCaptureMode::ByReference,
                value: HirExpr::LocalRef(LocalId(0)),
            }],
        }));

        assert_eq!(inline_constructor_value(&mut context, &value), None);
        assert_eq!(consumed, vec![false]);
        assert!(events.is_empty());
    }

    #[test]
    fn pending_value_is_rewritten_in_unconditional_decision_entry_test() {
        let (block, binding_index, occurrence_index, producers, producer_map) =
            inline_context_fixture();
        let mut consumed = vec![false];
        let mut events = Vec::new();
        let mut context = InlineContext::new(
            &block,
            &binding_index,
            &producers,
            &producer_map,
            InlineRewriteState {
                consumed_bindings: &mut consumed,
                eval_events: &mut events,
            },
            occurrence_index.remaining_uses_after(0),
        );
        let value = HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: HirExpr::LocalRef(LocalId(0)),
                truthy: HirDecisionTarget::CurrentValue,
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        }));

        let rewritten = inline_constructor_value(&mut context, &value);
        let Some(HirExpr::Decision(decision)) = rewritten else {
            panic!("unconditional decision entry must remain a decision")
        };
        assert_eq!(decision.nodes[0].test, HirExpr::String("value".into()));
        assert_eq!(consumed, vec![true]);
        assert_eq!(events, vec![ConstructorEvalEvent::Barrier]);
    }

    #[test]
    fn pending_value_is_not_moved_into_conditional_decision_target() {
        let (block, binding_index, occurrence_index, producers, producer_map) =
            inline_context_fixture();
        let mut consumed = vec![false];
        let mut events = Vec::new();
        let mut context = InlineContext::new(
            &block,
            &binding_index,
            &producers,
            &producer_map,
            InlineRewriteState {
                consumed_bindings: &mut consumed,
                eval_events: &mut events,
            },
            occurrence_index.remaining_uses_after(0),
        );
        let value = HirExpr::Decision(Box::new(HirDecisionExpr {
            entry: HirDecisionNodeRef(0),
            nodes: vec![HirDecisionNode {
                id: HirDecisionNodeRef(0),
                test: HirExpr::Boolean(true),
                truthy: HirDecisionTarget::Expr(HirExpr::LocalRef(LocalId(0))),
                falsy: HirDecisionTarget::Expr(HirExpr::Boolean(false)),
            }],
        }));

        assert_eq!(inline_constructor_value(&mut context, &value), None);
        assert_eq!(consumed, vec![false]);
        assert!(events.is_empty());
    }

    #[test]
    fn unresolved_producer_stays_as_independent_failure_evidence() {
        let (mut block, binding_index, occurrence_index, mut producers, producer_map) =
            inline_context_fixture();
        let HirStmt::LocalDecl(decl) = &mut block.stmts[0] else {
            unreachable!("fixture producer must be a local declaration")
        };
        decl.values.fixed[0] = HirExpr::Unresolved(Box::new(HirUnresolvedExpr {
            summary: "residual".into(),
        }));
        producers[0].source_preservation = ProducerSourcePreservation::UnsupportedShape;
        let mut consumed = vec![false];
        let mut events = Vec::new();
        let mut context = InlineContext::new(
            &block,
            &binding_index,
            &producers,
            &producer_map,
            InlineRewriteState {
                consumed_bindings: &mut consumed,
                eval_events: &mut events,
            },
            occurrence_index.remaining_uses_after(0),
        );

        assert_eq!(
            inline_constructor_value(&mut context, &HirExpr::LocalRef(LocalId(0))),
            None
        );
        assert_eq!(consumed, vec![false]);
        assert!(events.is_empty());
    }
}
