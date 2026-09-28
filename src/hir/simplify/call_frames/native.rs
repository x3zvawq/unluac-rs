//! 组织普通调用、构造器和控制头的完整源码帧恢复。
//!
//! 共享 builder 与 prefix owner 提供证明，本模块原子提交准备写、结果与后继声明事务。

use super::*;
use crate::hir::common::{HirBinding, HirInlineRetentionReason, HirLocalDecl, TempId};
use crate::hir::simplify::mention::{BindingReadCollector, BindingWriteCollector};
use crate::hir::visit::visit_stmts;
use prefix::coordinates::{PointKind, compact as compact_scope, visit_mut as visit_scope_mut};

mod assignments;
mod conditional;
mod declarations;
pub(super) mod expanded;
mod indexed;
mod retained_inputs;
mod tbc_initializers;

pub(in crate::hir::simplify) use expanded::restore as restore_expanded_frames;
pub(in crate::hir::simplify) use tbc_initializers::restore as restore_tbc_initializer_frames;

struct Plan {
    prefix_at_sink: bool,
    luau_function_declaration: bool,
    start: usize,
    sink: usize,
    base: HomeSlotKey,
    values: HirValuePack,
    result_locals: Vec<LocalId>,
    discarded_result: Option<LocalId>,
    assignment_targets: Vec<HirLValue>,
    luau_compound_global: bool,
    indexed_target: Option<crate::hir::common::HirTableAccess>,
    /// 完整表达式仍在原高槽留下的输入根；后缀必须继续保持该槽的观察与覆盖。
    continuing_root: Option<crate::hir::promotion::NativeConditionalValueResult>,
    retained_copies: Vec<(usize, RetainedCopy)>,
    /// 已由候选证明在 sink 内重发的写回或调用；它们不退休旧 binding 的输入值。
    replayed_effects: Vec<usize>,
    removed: Vec<usize>,
}

#[derive(Clone, Copy)]
enum RetainedCopy {
    Local { target: LocalId, source: LocalId },
    MethodReceiver { result: TempId, source: LocalId },
}

impl RetainedCopy {
    fn required(self) -> [Option<LocalId>; 2] {
        match self {
            Self::Local { target, source } => [Some(target), Some(source)],
            Self::MethodReceiver { source, .. } => [Some(source), None],
        }
    }

    fn matches(self, stmt: &HirStmt, facts: &ProtoPromotionFacts) -> bool {
        match self {
            Self::Local { target, source } => matches!(stmt, HirStmt::Assign(assign)
                if assign.targets.as_slice() == [HirLValue::Local(target)]
                    && assign.values.fixed.as_slice() == [HirExpr::LocalRef(source)]
                    && assign.values.tail.is_none()),
            Self::MethodReceiver { result, source } => {
                let HirStmt::CallStmt(stmt) = stmt else {
                    return false;
                };
                let call = &stmt.call;
                let HirExpr::TableAccess(access) = &call.callee else {
                    return false;
                };
                super::super::method_protocol::match_method_setup_pair(access, &call.callee, call)
                    .is_some()
                    && access.base == HirExpr::LocalRef(source)
                    && facts.call_argument_value(call, 0) == Some(result)
                    && facts.call_argument_copy(call, 0).is_some_and(|copy| {
                        facts.promoted_local_for_temp(copy.source) == Some(source)
                    })
            }
        }
    }
}

struct Preview {
    proto: HirProto,
    removed: Vec<bool>,
    recovered: Vec<RecoveredDeclaration>,
}

struct RecoveredDeclaration {
    index: usize,
    owner: usize,
    origin: usize,
    temp: TempId,
    local: LocalId,
}

// 记录消费旧 epoch 的事务起点；恢复失败须撤回该事务，不能从失败语句位置截断。
struct MissingEpoch {
    needs_declaration: bool,
    owner: usize,
    /// 消费本次值/声明的事务起点；后缀拒绝须归到该事务，不能归到读取位置。
    start: usize,
    contributors: BTreeSet<usize>,
}

impl Plan {
    fn only_preserves_call_prefix(&self) -> bool {
        self.start == self.sink
            && self.removed.is_empty()
            && self.result_locals.is_empty()
            && self.discarded_result.is_none()
            && self.assignment_targets.is_empty()
            && self.indexed_target.is_none()
            && !self.values.fixed.iter().chain(self.values.tail.iter().map(|tail| tail.as_expr()))
                .any(|value| crate::hir::visit::any_expr(value, &mut |expr|
                    matches!(expr, HirExpr::Call(call) if call.required_luau_inlining.is_some())))
            && (matches!(self.values.fixed.as_slice(), [HirExpr::Call(_)])
                || (self.values.fixed.is_empty()
                    && self
                        .values
                        .tail
                        .as_ref()
                        .is_some_and(|tail| matches!(tail.as_expr(), HirExpr::Call(_)))))
    }

    fn prefix_request(&self) -> (usize, prefix::PrefixRequest) {
        (
            if self.prefix_at_sink {
                self.sink
            } else {
                self.start
            },
            prefix::PrefixRequest {
                home: self.base,
                required: self
                    .retained_copies
                    .iter()
                    .flat_map(|(_, copy)| copy.required().into_iter().flatten())
                    .chain(
                        self.assignment_targets
                            .iter()
                            .filter_map(|target| match target {
                                HirLValue::Local(local) => Some(*local),
                                _ => None,
                            }),
                    )
                    .collect(),
            },
        )
    }
}

/// 交给作用域 owner 的未提交帧预览。只消费能由最终调用或 If/for 来源重建
/// 入口请求的计划；赋值目标从最终 Assign 恢复 required，retained-COPY 的独立端点
/// 及结果声明义务不能在跨 owner 时丢失，因此仍留给原完整计划事务。
/// 原同 home 构造器与单结果 CALL 的声明可由最终 LocalDecl 重建入口；与后继调用同批消费，
/// 避免未关闭的 nil/global scope 与未完成构造器前缀互相等待。
/// 先结束原 DFS 删除与 value-epoch 验证，再让作用域 owner 重新编号并验证完整后缀。
/// 返回的变化标记只表示确实应用了帧计划，供整个预览事务提交后重启消费者。
pub(in crate::hir::simplify) fn prepare_source_frames(
    proto: HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<(HirProto, bool)> {
    let restrictions = frame_restrictions(&proto, facts);
    let (mut plans, count) = collect_native_plans(
        NativeFrameContext {
            rk_literals: None,
            expanded_callees: None,
            retired_roots: None,
            proto: &proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            callee_aliases: &restrictions.callee_aliases,
            constants_fit_rk: tables::constants_fit_rk(&proto),
        },
        facts,
        dialect,
    );

    plans.retain(|plan| {
        !plan.only_preserves_call_prefix()
            && plan.retained_copies.is_empty()
            && (plan.result_locals.is_empty()
                || (plan.values.tail.is_none()
                    && plan.result_locals.len() == plan.values.fixed.len()
                    && plan.result_locals.iter().zip(&plan.values.fixed).enumerate().all(
                        |(offset, (&local, value))| {
                            let Some(home) = facts.trusted_local_home_slot(local) else {
                                return false;
                            };
                            // 声明帧按物理槽连续，CLOSE 后的 cell epoch 由原结果定义确认。
                            // 不能用 epoch=0 的临时键排除后继作用域中的同槽声明。
                            home.slot() == plan.base.slot() + offset
                                && match value {
                                    HirExpr::TableConstructor(table) =>
                                        facts.allocation_result_home(table) == Some(home),
                                    HirExpr::Call(call) if dialect == DecompileDialect::Luau
                                        && plan.result_locals.len() > 1 => declarations::call_result(
                                            call, local, plan.base.slot() + plan.result_locals.len(), facts,
                                        ).is_some(),
                                    HirExpr::Call(call) => facts.native_call_frame(call)
                                        .or_else(|| facts.native_fastcall_frame(call))
                                        .is_some_and(|frame| frame.home == home
                                            && matches!(frame.results, Some(crate::transformer::ResultPack::Fixed(pack))
                                                if pack.len == 1 && pack.start.index() == home.slot())),
                                    HirExpr::TableAccess(access) => facts.table_read_result_home(access) == Some(home),
                                    HirExpr::Binary(binary) => binary.source_site
                                        .and_then(|source| facts.operation_result_home(source)) == Some(home),
                                    HirExpr::Unary(unary) => unary.source_site
                                        .and_then(|source| facts.operation_result_home(source)) == Some(home),
                                    HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => true,
                                    _ => false,
                                }
                        },
                    )))
            && plan.discarded_result.is_none()
            // 计算左值也占用入口帧；只有 scope owner 能从重建后的目标恢复同一入口，
            // 才能移交预览。其余仍留给持有完整 key/base 准备的 native 事务。
            && plan.indexed_target.as_ref().is_none_or(|target|
                matches!(plan.values.fixed.as_slice(), [value]
                    if prefix::indexed_assignment_frame(target, value, facts, dialect) == Some(plan.base)))
            // Luau CONCAT 的入口还包含低于 operand 的结果预留槽；作用域 owner
            // 尚不能从 RHS 重建此语境，留给持有原 base 的完整 native 事务。
            && !(dialect == DecompileDialect::Luau
                && matches!(plan.values.fixed.as_slice(), [HirExpr::Binary(binary)]
                    if binary.op == crate::hir::common::HirBinaryOpKind::Concat))
    });
    if plans.is_empty() {
        return Some((proto, false));
    }
    let mut preview = match build_preview(&proto, facts, &plans, count) {
        Ok(preview) => preview,
        Err(failures) => {
            plans.retain(|plan| !failures.contains(&plan.start));
            if plans.is_empty() {
                return Some((proto, false));
            }
            build_preview(&proto, facts, &plans, count).ok()?
        }
    };
    publish_recovered_declarations(&mut preview, facts);
    recover_assignment_prefixes(&preview.proto, &plans, facts, dialect, &mut BTreeMap::new())
        .ok()?;
    retained_inputs::require_suffix_frames(
        &mut preview.proto,
        &preview.removed,
        &plans,
        facts,
        &mut BTreeMap::new(),
    )
    .ok()?;
    compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
    Some((preview.proto, true))
}

pub(super) struct PreparedFrames {
    plans: Vec<Plan>,
    stmt_count: usize,
}

impl PreparedFrames {
    pub(super) fn commit(
        self,
        proto: &mut HirProto,
        facts: &mut ProtoPromotionFacts,
        dialect: DecompileDialect,
        is_chunk_entry: bool,
    ) -> bool {
        commit_plans(
            proto,
            facts,
            dialect,
            is_chunk_entry,
            self.plans,
            self.stmt_count,
        )
    }
}

pub(super) fn prepare(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
    callee_aliases: &fastcalls::CalleeAliases,
    terminal: &TerminalClosureFacts,
) -> PreparedFrames {
    let context = NativeFrameContext {
        rk_literals: None,
        expanded_callees: None,
        retired_roots: None,
        proto,
        barred,
        closed,
        callee_aliases,
        constants_fit_rk: tables::constants_fit_rk(proto),
    };
    let (mut plans, stmt_count) = collect_native_plans(context, facts, dialect);
    if !matches!(
        dialect,
        DecompileDialect::Lua53 | DecompileDialect::Lua54 | DecompileDialect::Lua55
    ) {
        // 条件输入仍留在原高槽时，已有完整 CALL 也是后缀证明的一部分。
        // 同批核对它们的前缀，不能先提交条件恢复、再由最终 prefix owner 补救拒绝。
        if !plans.iter().any(|plan| plan.continuing_root.is_some()) {
            plans.retain(|plan| !plan.only_preserves_call_prefix());
        }
        return PreparedFrames { plans, stmt_count };
    }
    let occupied = plans
        .iter()
        .filter(|plan| !plan.only_preserves_call_prefix())
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    let mut flat = Vec::new();
    flatten_scope(&proto.body, &mut 0, &mut flat);
    for window in flat.windows(3) {
        if let [Some(first), Some(sink), Some(last)] = window
            && !occupied.contains(&first.id)
            && !occupied.contains(&sink.id)
            && matches!(last.stmt, HirStmt::Return(ret) if ret.values.is_empty())
            && let Some(plan) =
                terminal_closure_result(context, facts, dialect, terminal, first, sink)
        {
            plans.push(plan);
        }
    }
    // 纯前缀声明义务在 HIR 所有帧 owner 收尾后发布；提前冻结会阻止它们消费完整帧。
    plans.retain(|plan| !plan.only_preserves_call_prefix());

    plans.sort_unstable_by_key(|plan| plan.sink);
    PreparedFrames { plans, stmt_count }
}

/// 完整改写结束后，为已嵌入的 CALL 向 AST 发布前缀要求；不再改写调用或消费根协议。
pub(in crate::hir::simplify) fn preserve_existing_call_prefixes(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) {
    let restrictions = frame_restrictions(proto, facts);
    let (mut plans, count) = collect_native_plans(
        NativeFrameContext {
            rk_literals: None,
            expanded_callees: None,
            retired_roots: None,
            proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            callee_aliases: &restrictions.callee_aliases,
            constants_fit_rk: tables::constants_fit_rk(proto),
        },
        facts,
        dialect,
    );
    plans.retain(Plan::only_preserves_call_prefix);
    let starts = plans.iter().map(Plan::prefix_request).collect();
    prefix::preserve_prefix_requests(proto, facts, dialect, is_chunk_entry, count, starts);
}

/// 非 vararg 的单值 r0 RETURN 在调用者相邻槽留下相同返回值，因此后继 callee COPY
/// 不会覆盖另一份旧资源。必须消费当前 HIR Return 的原布局；原字节码尾部不可达
/// RETURN0 不能代表当前正常出口。每个 proto 只扫描一次，候选只查 exact maker 索引。
pub(super) struct TerminalClosureFacts<'a> {
    values: &'a super::super::object_flow::ReturnValueFacts,
    protos: Vec<(bool, bool)>,
}

pub(super) fn terminal_closure_facts<'a>(
    module: &crate::hir::HirModule,
    promotion: &[ProtoPromotionFacts],
    values: &'a super::super::object_flow::ReturnValueFacts,
    dialect: DecompileDialect,
) -> TerminalClosureFacts<'a> {
    struct Returns<'a> {
        facts: &'a ProtoPromotionFacts,
        seen: bool,
        valid: bool,
    }
    impl crate::hir::visit::HirVisitor<'_> for Returns<'_> {
        fn is_complete(&self) -> bool {
            !self.valid
        }

        fn visit_stmt(&mut self, stmt: &HirStmt) {
            if let HirStmt::Return(ret) = stmt {
                self.seen = true;
                self.valid = ret.values.tail.is_none()
                    && ret.values.fixed.len() == 1
                    && self.facts.native_return_frame(ret).is_some_and(|frame| {
                        frame.home == HomeSlotKey::new(0, 0)
                            && matches!(frame.values, ValuePack::Fixed(pack)
                                if pack.start.index() == 0 && pack.len == 1)
                    });
            }
        }
    }
    let protos = module
        .protos
        .iter()
        .map(|proto| {
            // Lua 5.2 的 precall 在进入新帧后检查 GC，空正文也可能观察高槽；
            // 5.3+ 的栈增长检查发生在进入新帧前，原 r0 返回已覆盖额外 callee 槽。
            if !matches!(dialect, DecompileDialect::Lua53 | DecompileDialect::Lua54 | DecompileDialect::Lua55)
                || proto.signature.is_vararg {
                return (false, false);
            }
            let Some(facts) = promotion.get(proto.id.index()) else {
                return (false, false);
            };
            let returns = Returns {
                facts,
                seen: false,
                valid: true,
            };
            let effects = crate::hir::expr_safety::HirEvalEffects::new(
                crate::hir::expr_safety::HirExprSafety::for_dialect(dialect),
                |stmt| matches!(stmt, HirStmt::TableSetList(_) | HirStmt::ErrNil(_)
                    | HirStmt::ToBeClosed(_) | HirStmt::NumericFor(_) | HirStmt::GenericFor(_))
                    || matches!(stmt, HirStmt::Return(ret) if ret.pending_cleanup_source.is_some()),
            );
            let mut collectors = (returns, effects);
            visit_stmts(&proto.body.stmts, &mut collectors);
            let (returns, effects) = collectors;
            (
                returns.seen && returns.valid,
                facts.empty_call_preserves_frame() && !effects.found(),
            )
        })
        .collect();
    TerminalClosureFacts { values, protos }
}

/// 终端普通 CALL 的值必为 Lua closure，且 maker 在原 r0 返回相同值时，额外
/// callee COPY 才不承担旧 scratch 资源的覆盖责任；闭包还须没有入口调整与原槽写入。
/// 即使本体无观察，下移的写入也会改变返回后下一次 lookup 看到的旧根（results_06）。
/// 两槽写域、当前 lexical epoch 与整个源码前缀仍由原 owner 签证；未知 callable、
/// 参数准备及非终端后缀不领此许可。
fn terminal_closure_result(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    terminal: &TerminalClosureFacts,
    first: &FlatStmt<'_>,
    sink: &FlatStmt<'_>,
) -> Option<Plan> {
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let ([local], [HirExpr::Call(inner)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let HirStmt::CallStmt(outer) = sink.stmt else {
        return None;
    };
    let outer = &outer.call;
    if outer.callee != HirExpr::LocalRef(*local)
        || !outer.args.is_empty()
        || outer.is_method()
        || inner.is_method()
        || outer.fastcall.is_some()
        || !terminal.protos[terminal.values.call_target(inner)?.index()].0
        || !terminal.protos[terminal.values.call_result_callee(inner, 0)?.index()].1
        || context.proto.local_debug_hints[local.index()].is_some()
        || context.proto.local_debug_scopes[local.index()].is_some()
        || matches!(context.proto.inline_dispositions.local(*local),
            crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    {
        return None;
    }
    let base = facts.call_result_statement_home(*local, inner, outer)?;
    if facts
        .complete_local_definition_write_homes(*local)
        .iter()
        .any(|home| context.barred.contains(home) || context.closed.contains(home))
    {
        return None;
    }
    let mut builder = frame_builder(context, &[], facts, dialect, base.slot())?;
    let inner = builder.call(inner, 0, base.slot(), false, CallWidth::Single)?;
    let mut call = outer.clone();
    call.callee = HirExpr::Call(Box::new(inner));
    // 原外层 CALL/COPY 的物理布局已整体消费。新调用复用内层结果 home，不能让
    // 后续 query 再把原 source site 的高槽参数/根协议当作当前重发帧。
    call.source_site = None;
    call.argument_roots.clear();
    call.frame_root_ends.clear();
    call.callee_root_handoff = None;
    call.method_rewrite_transaction = None;
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: sink.id,
        base,
        values: vec![HirExpr::Call(Box::new(call))].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: vec![first.id],
    })
}

/// 普通帧和独立构造器共用同一坐标/占用索引；未提交的 scope preview 与直接提交
/// 不各自重建一套候选协议，所有重叠筛选都发生在删除任何语句之前。
fn collect_native_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> (Vec<Plan>, usize) {
    let rk_literals =
        (!context.constants_fit_rk).then(|| tables::RkLiterals::new(context.proto, facts, dialect));
    let context = NativeFrameContext {
        rk_literals: rk_literals.as_ref(),
        ..context
    };
    let mut plans = Vec::new();
    let mut stmt_count = 0;
    collect_plans(
        context,
        &context.proto.body,
        facts,
        dialect,
        &mut stmt_count,
        &mut plans,
    );
    let mut constructors = Vec::new();
    let mut constructor_stmt_count = 0;
    collect_constructor_plans(
        context,
        facts,
        dialect,
        &mut constructor_stmt_count,
        &mut constructors,
    );
    // 构造器释放的 callee 身份可能被下一次 CALL 的准备区复用，两者必须共同退休。
    // 并列 CALL 不能先提交其中一个 RHS；声明组优先于与其重叠的单调用候选。
    let grouped = constructors
        .iter()
        .filter(|plan| plan.result_locals.len() > 1)
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    plans.retain(|plan| {
        !grouped.contains(&plan.sink) && plan.removed.iter().all(|index| !grouped.contains(index))
    });
    // 已由外层调用消费的构造器不再建立第二个事务；其余候选在同一源码帧预览中验证。
    let occupied = plans
        .iter()
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    plans.extend(constructors.into_iter().filter(|plan| {
        !occupied.contains(&plan.sink) && plan.removed.iter().all(|index| !occupied.contains(index))
    }));
    {
        let conditionals = conditional::collect(context, facts, dialect);
        let occupied = conditionals
            .iter()
            .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
            .collect::<BTreeSet<_>>();
        plans.retain(|plan| {
            !occupied.contains(&plan.sink)
                && plan.removed.iter().all(|index| !occupied.contains(index))
        });
        plans.extend(conditionals);
    }
    // ProofIncomplete：正向 preview 的 missing 检查不证明下一轮写前读取。
    // repeat 内既有 binding 的赋值不能退休；每轮新建的 LocalDecl 仍走原身份/帧证明。
    // 已签证的交换写回只在本轮同一事务中重发，不退休状态 binding，可保留回边语义。
    // 普通帧与构造器统一过滤，避免新增的 body 候选绕过同一回边限制。
    let mut repeat_assignments = vec![false; stmt_count];
    let mut repeat_depth = 0;
    prefix::coordinates::visit(
        &context.proto.body,
        &mut 0,
        &mut |index, kind, stmt| match (kind, stmt) {
            (PointKind::Statement, HirStmt::Repeat(_)) => repeat_depth += 1,
            (PointKind::RepeatCondition, _) => repeat_depth -= 1,
            (PointKind::Statement, HirStmt::Assign(_))
                if repeat_depth > 0 && scalar_binding(stmt).is_some() =>
            {
                repeat_assignments[index] = true;
            }
            _ => {}
        },
    );
    plans.retain(|plan| {
        plan.removed
            .iter()
            .all(|index| !repeat_assignments[*index] || plan.replayed_effects.contains(index))
    });

    plans.sort_unstable_by_key(|plan| plan.sink);
    (plans, stmt_count)
}

fn commit_plans(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    mut plans: Vec<Plan>,
    stmt_count: usize,
) -> bool {
    // 较早事务借用的后缀 COPY 是其覆盖证明的一部分；同批后来的候选不能再次消费它。
    let mut retained_statements = BTreeSet::new();
    plans.retain(|plan| {
        if retained_statements.contains(&plan.sink)
            || plan
                .removed
                .iter()
                .any(|index| retained_statements.contains(index))
        {
            return false;
        }
        retained_statements.extend(plan.retained_copies.iter().map(|(index, _)| *index));
        true
    });
    if plans.is_empty() {
        return false;
    }
    // 声明恢复报告消费了仍被读取身份的事务起点；撤销该候选后重新验证整批，
    // 不能把一个条件帧的拒绝传播给后续独立构造器。若仍有依赖冲突则整批拒绝；
    // 不循环逐个试探候选，预览仍只有常数次扫描/克隆。
    let mut preview = match build_preview(proto, facts, &plans, stmt_count) {
        Ok(preview) => preview,
        Err(index) => {
            plans.retain(|plan| !index.contains(&plan.start));
            if plans.is_empty() {
                return false;
            }
            let Ok(preview) = build_preview(proto, facts, &plans, stmt_count) else {
                return false;
            };
            preview
        }
    };
    let preserved =
        match validate_plan_batch(&mut preview, &plans, facts, dialect, is_chunk_entry, false) {
            Ok(preserved) => preserved,
            Err(failures) => {
                if commit_inert_terminal_frame(
                    proto,
                    facts,
                    dialect,
                    is_chunk_entry,
                    &plans,
                    stmt_count,
                ) {
                    return true;
                }
                plans.retain(|plan| !failures.rejects(plan.start));
                if plans.is_empty() {
                    return false;
                }
                let Ok(revised) = build_preview(proto, facts, &plans, stmt_count) else {
                    return false;
                };
                preview = revised;
                let Ok(preserved) = validate_plan_batch(
                    &mut preview,
                    &plans,
                    facts,
                    dialect,
                    is_chunk_entry,
                    false,
                ) else {
                    return false;
                };
                preserved
            }
        };
    let mut preserved = preserved;
    preserved.extend(
        plans
            .iter()
            .flat_map(|plan| plan.result_locals.iter().copied()),
    );
    compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
    let mut changed = plans.iter().any(|plan| !plan.only_preserves_call_prefix());
    for local in preserved {
        changed |= preview
            .proto
            .inline_dispositions
            .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
    }
    publish_recovered_declarations(&mut preview, facts);
    *proto = preview.proto;
    changed
}

fn commit_inert_terminal_frame(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    plans: &[Plan],
    stmt_count: usize,
) -> bool {
    let Some(plan) = plans.last() else {
        return false;
    };
    let terminal = match proto.body.stmts.as_slice() {
        [.., terminal, HirStmt::Return(ret)]
            if ret.values.is_empty() && ret.pending_cleanup_source.is_none() =>
        {
            terminal
        }
        [.., terminal] => terminal,
        _ => return false,
    };
    let mut owns_terminal = false;
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        owns_terminal |= index == plan.sink
            && kind == PointKind::Statement
            && std::ptr::eq(stmt, terminal)
            && matches!(stmt, HirStmt::CallStmt(_));
    });
    if !owns_terminal
        || plan.only_preserves_call_prefix()
        || !plan.result_locals.is_empty()
        || plan.discarded_result.is_some()
        || !plan.assignment_targets.is_empty()
        || plan.indexed_target.is_some()
        || plan.continuing_root.is_some()
        || !plan.retained_copies.is_empty()
        || !plan.replayed_effects.is_empty()
        || !matches!(plan.values.fixed.as_slice(), [HirExpr::Call(_)])
        || plan.values.tail.is_some()
    {
        return false;
    }
    // 单独预览末次调用：此前的计算、调用及声明不从一个已被前缀拒绝的批次继承改写。
    let Ok(mut preview) = build_preview(proto, facts, std::slice::from_ref(plan), stmt_count)
    else {
        return false;
    };
    if !preview.recovered.is_empty() {
        return false;
    }
    compact_scope(&mut preview.proto.body, &preview.removed, &mut 0);
    if !prefix::close_gc_inert_terminal_prefix(&mut preview.proto, facts, dialect, is_chunk_entry) {
        return false;
    }
    *proto = preview.proto;
    true
}

fn recover_assignment_prefixes(
    proto: &HirProto,
    plans: &[Plan],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    candidates: &mut BTreeMap<usize, prefix::PrefixRequest>,
) -> Result<(), prefix::PrefixFailures> {
    // 前序帧消费旧声明后，后继赋值可成为新 initializer。重新用完整表达式
    // 证明预留结果槽后的布局，再改其前缀请求；不能直接沿用赋值的 freereg。
    let assignments = plans
        .iter()
        .filter(|plan| !plan.assignment_targets.is_empty())
        .map(|plan| (plan.sink, plan))
        .collect::<BTreeMap<_, _>>();
    let restrictions = frame_restrictions(proto, facts);
    let context = NativeFrameContext {
        rk_literals: None,
        expanded_callees: None,
        retired_roots: None,
        proto,
        barred: &restrictions.barred,
        closed: &restrictions.closed,
        callee_aliases: &restrictions.callee_aliases,
        constants_fit_rk: tables::constants_fit_rk(proto),
    };
    let mut invalid = None;
    prefix::coordinates::visit(&proto.body, &mut 0, &mut |index, kind, stmt| {
        if kind != PointKind::Statement {
            return;
        }
        let Some(plan) = assignments.get(&index) else {
            return;
        };
        let HirStmt::LocalDecl(decl) = stmt else {
            return;
        };
        let valid = (|| {
            let ([local], [value], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                return None;
            };
            if plan.assignment_targets.as_slice() != [HirLValue::Local(*local)] {
                return None;
            }
            let home = facts.trusted_local_home_slot(*local)?;
            if home == plan.base {
                // 已证明的 RHS 仍在同一空闲槽开始，只把本次结果认作声明；
                // 不再次用空准备区重建已被完整帧消费的来源事件。
                return Some(home);
            }
            let mut builder = frame_builder(context, &[], facts, dialect, home.slot())?;
            let rebuilt = builder.expr(value, 0, home.slot(), None, false, true, None)?;
            if rebuilt != *value {
                return None;
            }
            Some(home)
        })();
        if let Some(home) = valid {
            candidates.insert(
                plan.start,
                prefix::PrefixRequest {
                    home,
                    required: BTreeSet::new(),
                },
            );
        } else {
            invalid = Some(invalid.map_or(plan.start, |old: usize| old.min(plan.start)));
        }
    });
    if let Some(start) = invalid {
        return Err(prefix::PrefixFailures::invalid_from(start));
    }
    Ok(())
}

/// 前缀拒绝按词法后缀返回，声明/退休依赖失败保持其未知后缀；撤回后统一重建验证。
fn validate_plan_batch(
    preview: &mut Preview,
    plans: &[Plan],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
    complete_suffix: bool,
) -> Result<BTreeSet<LocalId>, prefix::PrefixFailures> {
    let Preview {
        proto,
        removed,
        recovered,
    } = preview;
    let mut candidates = plans
        .iter()
        .filter(|plan| complete_suffix || !plan.only_preserves_call_prefix())
        .map(Plan::prefix_request)
        .collect::<BTreeMap<_, _>>();
    recover_assignment_prefixes(proto, plans, facts, dialect, &mut candidates)?;
    let dependent =
        retained_inputs::require_suffix_frames(proto, removed, plans, facts, &mut candidates)
            .map_err(prefix::PrefixFailures::invalid_from)?;
    let mut restored_owners = BTreeMap::new();
    let mut request_scopes = BTreeMap::new();
    for declaration in recovered {
        candidates.insert(
            declaration.index,
            prefix::PrefixRequest {
                home: facts.trusted_local_home_slot(declaration.local).unwrap(),
                required: BTreeSet::new(),
            },
        );
        let scope = restored_owners
            .entry(declaration.owner)
            .or_insert_with(|| (declaration.index, BTreeSet::new()));
        scope.0 = scope.0.min(declaration.index);
        scope.1.insert(declaration.origin);
        request_scopes.insert(declaration.index, declaration.owner);
    }
    if !restored_owners.is_empty() {
        visit_scope_mut(&mut proto.body, &mut 0, &mut |index, owner, stmt| {
            if !removed[index]
                && restored_owners
                    .get(&owner)
                    .is_some_and(|(first, _)| index > *first)
                && let HirStmt::CallStmt(call) = stmt
                && let Some(frame) = facts.native_call_layout(&call.call)
            {
                candidates.entry(index).or_insert(prefix::PrefixRequest {
                    home: frame.home,
                    required: BTreeSet::new(),
                });
                request_scopes.insert(index, owner);
            }
            Some(())
        });
    }
    let preserved = prefix::validate_prefixes(
        proto,
        facts,
        dialect,
        is_chunk_entry,
        removed,
        &candidates,
        false,
    )
    .map_err(|failed| {
        let scopes = request_scopes
            .iter()
            .filter(|(request, _)| failed.rejects(**request))
            .map(|(_, scope)| *scope)
            .collect::<BTreeSet<_>>();
        let owners = plans
            .iter()
            .filter(|plan| failed.rejects(plan.sink))
            .map(|plan| plan.start)
            .chain(
                scopes
                    .iter()
                    .flat_map(|scope| restored_owners[scope].1.iter().copied()),
            )
            .collect::<BTreeSet<_>>();
        failed
            .with_dependent_owners(owners)
            .with_dependent_suffix(dependent)
    })?;
    let retained = plans
        .iter()
        .flat_map(|plan| {
            plan.retained_copies
                .iter()
                .map(move |&(index, copy)| (index, (copy, plan.start)))
        })
        .collect::<BTreeMap<_, _>>();
    let mut failed = 0;
    if !retained.is_empty() {
        visit_scope_mut(&mut proto.body, &mut 0, &mut |index, _, stmt| {
            let Some(&(copy, owner)) = retained.get(&index) else {
                return Some(());
            };
            if removed[index] || !copy.matches(stmt, facts) {
                failed = owner;
                return None;
            }
            Some(())
        })
        .ok_or_else(|| prefix::PrefixFailures::invalid_from(failed))?;
    }
    Ok(preserved)
}

fn collect_plans(
    context: NativeFrameContext<'_>,
    block: &HirBlock,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt_count: &mut usize,
    plans: &mut Vec<Plan>,
) {
    let NativeFrameContext {
        proto,
        barred,
        closed,
        constants_fit_rk,
        ..
    } = context;
    let rk_prefix_end = tables::rk_prefix_end(proto);
    let first_plan = plans.len();
    let mut collected = first_plan;
    let mut prefix_assumption = false;
    let mut prefix_assumed_sinks = BTreeSet::new();
    let mut boolean_prewrites = BTreeMap::new();
    for (initial, result, home, initial_value) in facts.boolean_value_prewrites() {
        for local in facts.promoted_local_for_temp(result).into_iter().chain(
            facts
                .value_result_copy(result)
                .and_then(|copy| facts.promoted_local_for_temp(copy.target))
                .filter(|local| Some(*local) != facts.promoted_local_for_temp(result)),
        ) {
            // 多个值版本落入同一 Local 时，不按遍历次序任选原结果身份。
            boolean_prewrites
                .entry(local)
                .and_modify(|entry| *entry = None)
                .or_insert(Some((initial, result, home, initial_value)));
        }
    }
    let mut copy_prewrites = BTreeMap::new();
    for (initial, result, home) in facts.copy_value_prewrites() {
        for local in facts.promoted_local_for_temp(result).into_iter().chain(
            facts
                .value_result_copy(result)
                .and_then(|copy| facts.promoted_local_for_temp(copy.target))
                .filter(|local| Some(*local) != facts.promoted_local_for_temp(result)),
        ) {
            copy_prewrites
                .entry(local)
                .and_modify(|entry| *entry = None)
                .or_insert(Some((initial, result, home)));
        }
    }
    let mut read_locals = BTreeSet::new();
    let mut collectors = (
        (
            CaptureCollector::new(HirCaptureMode::ByReference),
            CaptureCollector::new(HirCaptureMode::ByValue),
        ),
        super::super::mention::BindingReadCollector(|binding| {
            if let HirBinding::Local(local) = binding {
                read_locals.insert(local);
            }
        }),
    );
    visit_stmts(&proto.body.stmts, &mut collectors);
    let ((mut captures, value_captures), _) = collectors;
    captures
        .bindings
        .locals
        .extend(value_captures.bindings.locals);
    let mut flat = Vec::new();
    flatten_scope(block, stmt_count, &mut flat);
    plans.extend(declarations::collect_upvalue_literals(
        context, facts, dialect, &flat,
    ));
    let nested = tables::nested_initializers(
        flat.iter().map(|entry| entry.map(|entry| entry.stmt)),
        facts,
    );
    let following_frame_floor = following_frame_floors(&flat, facts, dialect);
    let live_indexed_results = live_indexed_results(&flat);
    // 后继 SETTABLE 直接读取的低槽表是已需存在的前缀身份。唯一 base 准备仍由
    // indexed 事务整体消费，不提前声明；这里仅为跨写表存活的索引结果提供锚点。
    let mut following_table_base = vec![None; flat.len()];
    let mut table_base = None;
    for (index, entry) in flat.iter().enumerate().rev() {
        following_table_base[index] = table_base;
        let Some(entry) = entry else {
            table_base = None;
            continue;
        };
        if scalar_local(entry.stmt).is_some() {
            continue;
        }
        table_base = match entry.stmt {
            HirStmt::Assign(assign) => match assign.targets.as_slice() {
                [HirLValue::TableAccess(access)] => match access.base {
                    HirExpr::LocalRef(local) => facts
                        .native_table_write_layout(access)
                        .filter(|layout| {
                            facts.trusted_local_home_slot(local) == Some(layout.base)
                                && layout
                                    .value
                                    .is_some_and(|value| layout.base.slot() < value.slot())
                        })
                        .map(|layout| (local, layout.base, access.as_ref())),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
    }
    let mut start = 0;
    let mut lookup_attempt_start = None;
    let mut conditional_attempt_start = None;
    let mut operation_attempt_start = None;
    let mut external_operation_attempt_start = None;
    let mut right_operation_attempt_start = None;
    let mut comparison_attempt_start = None;
    let mut logical_attempt_start = None;
    let mut scalar_assignment_attempt_start = None;
    let mut concat_assignment_attempt_start = None;
    let mut swap_frames = BTreeMap::new();
    for (snapshot, left, right, home) in facts.local_swap_frames() {
        swap_frames
            .entry(snapshot)
            .and_modify(|entry| *entry = None)
            .or_insert(Some((left, right, home)));
    }
    let mut scalar_pairs = BTreeMap::new();
    for ([snapshot, second, first], copied_input, tail, frame) in facts.local_scalar_pair_frames() {
        scalar_pairs
            .entry(snapshot)
            .and_modify(|entry| *entry = None)
            .or_insert(Some(assignments::ScalarPair {
                left: first,
                right: second,
                copied_input,
                base: frame.homes[0],
                literal_input: frame.literal_input.as_ref(),
                tail,
            }));
    }
    let mut constructor_high = None::<usize>;
    let mut literal_globals = assignments::literal_globals::plans(context, facts, dialect, &flat);
    let statements = flat
        .iter()
        .flatten()
        .map(|entry| (entry.id, entry.stmt))
        .collect::<BTreeMap<_, _>>();
    let mut retired_roots = BTreeSet::new();
    let mut retirements_collected = plans.len();
    for (index, entry) in flat.iter().enumerate() {
        // 每个计划的删除域只访问一次；后继 CALL 可同批消费旧根的 release，
        // 不必为“构造器退休 → release 消失 → CALL 恢复”反复重扫整个 proto。
        for plan in &plans[retirements_collected..] {
            for removed in &plan.removed {
                if let Some(stmt) = statements.get(removed)
                    && let Some((local, _)) = scalar_local(stmt)
                {
                    retired_roots.insert(local);
                }
            }
            for local in &plan.result_locals {
                retired_roots.remove(local);
            }
        }
        retirements_collected = plans.len();
        if prefix_assumption {
            prefix_assumed_sinks.extend(plans[collected..].iter().map(|plan| plan.sink));
        }
        collected = plans.len();
        prefix_assumption = false;
        if index < start {
            continue;
        }
        if let Some((plan, end)) = literal_globals.remove(&index) {
            plans.push(plan);
            start = end + 1;
            constructor_high = None;
            continue;
        }
        let Some(FlatStmt { id: stmt_id, stmt }) = *entry else {
            retired_roots.clear();
            start = index + 1;
            constructor_high = None;
            continue;
        };
        // release 是旧源码根的终点，不是新值定义；已退休的 release 仍须由后继
        // 完整帧一起消费。只有真实写入才使同一 Local 的退休事实失效。
        if !matches!(stmt, HirStmt::LocalRootRelease(_)) {
            crate::hir::visit::visit_stmt_header(
                stmt,
                &mut BindingWriteCollector(|binding| {
                    if let HirBinding::Local(local) = binding {
                        retired_roots.remove(&local);
                    }
                }),
            );
        }
        prefix_assumption = !constants_fit_rk && stmt_id < rk_prefix_end;
        let constants_fit_rk = constants_fit_rk || prefix_assumption;
        let context = NativeFrameContext {
            retired_roots: Some(&retired_roots),
            constants_fit_rk,
            ..context
        };
        if let Some((_, HirExpr::Call(call))) = scalar_local(stmt)
            && let Some((plan, end)) =
                assignments::parallel(context, facts, dialect, &flat, start, index, call)
        {
            plans.push(plan);
            start = end + 1;
            constructor_high = None;
            continue;
        }
        if let Some((_, HirExpr::TableAccess(access))) = scalar_local(stmt)
            && let Some((plan, end)) =
                assignments::lookup_pack(context, facts, dialect, &flat, index, access)
        {
            plans.push(plan);
            start = end + 1;
            constructor_high = None;
            continue;
        }
        if let (Some(Some(second)), Some(Some(last))) = (flat.get(index + 1), flat.get(index + 2))
            && let Some(plan) = assignments::scalar_pair(
                context,
                dialect,
                &scalar_pairs,
                FlatStmt { id: stmt_id, stmt },
                *second,
                *last,
            )
        {
            plans.push(plan);
            start = index + 3;
            constructor_high = None;
            continue;
        }
        if let (Some(Some(second)), Some(Some(last))) = (flat.get(index + 1), flat.get(index + 2))
            && let Some(plan) = swap_assignment_plan(
                context,
                facts,
                &swap_frames,
                FlatStmt { id: stmt_id, stmt },
                *second,
                *last,
            )
        {
            plans.push(plan);
            start = index + 3;
            constructor_high = None;
            continue;
        }
        if let (Some(Some(second)), Some(Some(last))) = (flat.get(index + 1), flat.get(index + 2))
            && let Some(plan) = parallel_upvalue_comparisons(
                context,
                facts,
                dialect,
                FlatStmt { id: stmt_id, stmt },
                *second,
                *last,
            )
        {
            plans.push(plan);
            start = index + 3;
            constructor_high = None;
            continue;
        }
        if (nil_argument_group(stmt, facts).is_some()
            || matches!(stmt, HirStmt::Assign(assign) if matches!(assign.targets.as_slice(), [HirLValue::TableAccess(_)])))
            && let Some((plan, end)) = indexed::parallel_preparations(
                context,
                facts,
                dialect,
                &flat[start..],
                index - start,
            )
        {
            plans.push(plan);
            start += end + 1;
            constructor_high = None;
            continue;
        }
        if let Some([Some(first), Some(second), Some(third), Some(last)]) =
            flat.get(index..index + 4)
            && let Some(plan) = indexed::parallel_literals(
                context,
                facts,
                dialect,
                [*first, *second, *third, *last],
            )
        {
            plans.push(plan);
            start = index + 4;
            constructor_high = None;
            continue;
        }
        if let (Some(Some(second)), Some(Some(last))) = (flat.get(index + 1), flat.get(index + 2))
            && let Some(plan) = indexed::parallel_copies(
                context,
                facts,
                dialect,
                &flat[start..index],
                FlatStmt { id: stmt_id, stmt },
                *second,
                *last,
            )
        {
            plans.push(plan);
            start = index + 3;
            constructor_high = None;
            continue;
        }
        if dialect == DecompileDialect::Lua54
            && scalar_assignment_attempt_start != Some(start)
            && let Some((_, HirExpr::Call(call))) = scalar_local(stmt)
            && facts.native_scalar_assignment(call).is_some()
            && let (Some(Some(scalar)), Some(Some(copy))) =
                (flat.get(index + 1), flat.get(index + 2))
        {
            // 一个未闭合 run 只建一次定义索引；拒绝后不对增长的前缀逐 CALL 重试。
            scalar_assignment_attempt_start = Some(start);
            let run = flat[start..=index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) =
                scalar_assignment_plan(context, &run, facts, dialect, scalar.stmt, copy.stmt)
            {
                plan.removed = flat[start + plan.start..index + 2]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = copy.id;
                plans.push(plan);
                start = index + 3;
                constructor_high = None;
                continue;
            }
        }
        if dialect == DecompileDialect::Luau
            && index > start
            && let HirStmt::Assign(assign) = stmt
            && let Some(prewrite) = facts.boolean_upvalue_prewrite(assign)
            && let Some(previous) = flat[index - 1]
            && let Some(plan) = boolean_value_initializer(
                context,
                facts,
                previous,
                FlatStmt { id: stmt_id, stmt },
                prewrite,
                &read_locals,
            )
        {
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if dialect == DecompileDialect::Luau
            && index > start
            && let Some((target, _)) = scalar_local(stmt)
            && let Some(&Some(prewrite)) = copy_prewrites.get(&target)
            && let Some(first) = flat[index - 1]
            && let Some(plan) = assignments::copy_value_initializer(
                context,
                facts,
                first,
                FlatStmt { id: stmt_id, stmt },
                prewrite,
            )
            // 新声明不能先冻结外层帧的内部 COPY；完整结果写回已有低槽则退休
            // 高槽声明，不抬高后续 freereg，交给整批 preview 验证。
            && (plan.result_locals.is_empty()
                || proto.local_debug_hints[target.index()].is_some()
                || proto.local_debug_scopes[target.index()].is_some()
                || following_frame_floor[index].all.is_none_or(|floor| prewrite.2.slot() < floor))
        {
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }

        let boolean_return = scalar_local(stmt).and_then(|(target, _)| {
            let next = flat.get(index + 1).copied().flatten()?;
            let HirStmt::Return(ret) = next.stmt else {
                return None;
            };
            (ret.values.tail.is_none()
                && ret.values.fixed.as_slice() == [HirExpr::LocalRef(target)]
                && facts
                    .native_return_frame(ret)
                    .is_some_and(|frame| facts.trusted_local_home_slot(target) == Some(frame.home)))
            .then_some(next)
        });
        if dialect == DecompileDialect::Luau
            && index > start
            && let Some((target, _)) = scalar_local(stmt)
            && let Some(&Some((initial, result, home, initial_value))) = boolean_prewrites.get(&target)
            // 高槽 Boolean 可能仍属于后续较低 CALL 的参数准备；独立 initializer
            // 不能先消费其 Boolean 预写并截断 run，否则完整调用再无入口事件可用。
            && (following_frame_floor[index]
                .all
                .is_none_or(|floor| home.slot() < floor)
                || proto.local_debug_hints[target.index()].is_some()
                || proto.local_debug_scopes[target.index()].is_some()
                || boolean_return.is_some())
            && let Some(previous) = flat[index - 1]
            && let Some(mut plan) = boolean_value_initializer(
                context,
                facts,
                previous,
                FlatStmt { id: stmt_id, stmt },
                (initial, result, home, initial_value),
                &read_locals,
        ) {
            let retired_return = boolean_return.filter(|_| {
                proto.local_debug_hints[target.index()].is_none()
                    && proto.local_debug_scopes[target.index()].is_none()
                    && !proto.inline_dispositions.local(target).must_preserve()
            });
            if let Some(ret) = retired_return {
                // 单值 RETURN 与预写、结果声明一起验证并退休，避免中间提交
                // 把结果标成独立的 PhysicalFramePrefix，永久挡住完整返回帧。
                plan.removed.push(plan.sink);
                plan.sink = ret.id;
                plan.result_locals.clear();
            }
            plans.push(plan);
            start = index + 1 + usize::from(retired_return.is_some());
            constructor_high = None;
            continue;
        }
        if conditional_attempt_start != Some(start)
            && let Some((owner, HirExpr::Call(call))) = scalar_local(stmt)
            && call
                .source_site
                .and_then(|source| facts.conditional_value_result(source))
                .is_some()
            && let Some((result_index, next)) = conditional_initializer_tail(&flat, index, owner)
            && scalar_local(next.stmt).is_some()
        {
            conditional_attempt_start = Some(start);
            let run = flat[start..=index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = conditional_value_initializer(
                context,
                &run,
                facts,
                dialect,
                index - start,
                next.stmt,
            ) {
                plan.removed = flat[start + plan.start..result_index]
                    .iter()
                    .filter_map(|entry| entry.map(|entry| entry.id))
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = next.id;
                plans.push(plan);
                start = result_index + 1;
                constructor_high = None;
                continue;
            }
        }
        // locals 可将准备值与算术结果认作同一状态，形成 Assign；原输入 Def 和完整
        // 声明预览仍能恢复 initializer，不能仅因当前语句形状而丢掉这个帧入口。
        let arithmetic_initializer = matches!(stmt, HirStmt::LocalDecl(_) | HirStmt::Assign(_))
            && scalar_local(stmt).is_some_and(|(_, value)| {
                let HirExpr::Binary(binary) = value else {
                    return false;
                };
                use crate::hir::common::HirBinaryOpKind::{Add, Div, Mod, Mul, Pow, Sub};
                matches!(binary.op, Add | Sub | Mul | Div | Mod | Pow)
                    && (matches!(binary.lhs, HirExpr::Call(_))
                        || matches!(binary.rhs, HirExpr::Call(_))
                        || (matches!(binary.lhs, HirExpr::Unary(_))
                            || matches!(binary.rhs, HirExpr::Unary(_)))
                            && binary
                                .source_site
                                .and_then(|source| facts.operation_result_home(source))
                                .zip(following_frame_floor[index].all)
                                .is_some_and(|(home, floor)| home.slot() < floor))
            });
        let unary_initializer = dialect == DecompileDialect::Luau
            && matches!(stmt, HirStmt::LocalDecl(_))
            && scalar_local(stmt).is_some_and(|(_, value)| {
                matches!(value, HirExpr::Unary(unary)
                    if unary.op == crate::hir::common::HirUnaryOpKind::Not
                        && facts.unary_result_home(unary).zip(facts.unary_operand_home(unary))
                            .is_some_and(|(result, input)| input == HomeSlotKey::new(result.slot() + 1, 0)))
            });
        let split_initializer = index.checked_sub(1).and_then(|previous| {
            flat[previous].and_then(|entry| split_expression_initializer(entry.stmt, stmt))
        });
        let comparison_initializer = (matches!(stmt, HirStmt::LocalDecl(_) | HirStmt::Assign(_))
            || split_initializer.is_some())
            && scalar_local(stmt).is_some_and(|(_, value)| {
                let HirExpr::Binary(binary) = value else {
                    return false;
                };
                let Some(result) = facts
                    .comparison_result_temp(binary)
                    .and_then(|result| facts.trusted_temp_home_slot(result))
                else {
                    return false;
                };
                // 已树化的前一个比较没有准备值可消费，不占用当前 run 的比较尝试。
                // 否则它的 CALL 子树会反复触发空候选，饿死同一 run 后续的真实输入。
                (split_initializer.is_some()
                    || crate::hir::visit::any_expr(value, &mut |expr| match expr {
                        HirExpr::LocalRef(local) => facts
                            .complete_local_home_slots(*local)
                            .iter()
                            .any(|home| home.slot() >= result.slot()),
                        HirExpr::TempRef(temp) => facts
                            .complete_temp_home_slots(*temp)
                            .iter()
                            .any(|home| home.slot() >= result.slot()),
                        // 操作数树化后，其 Boolean 预写仍可能在当前 run。
                        // 完整比较帧按内部 phi 的来源消费，不能要求旧 LocalRef 还在。
                        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
                            dialect == DecompileDialect::Luau
                        }
                        _ => false,
                    }))
                    && facts.native_binary_layout(binary).is_some_and(|layout| {
                        [layout.lhs, layout.rhs]
                            .into_iter()
                            .flatten()
                            .any(|home| home.slot() >= result.slot())
                    })
            });
        let operation_input =
            operation_target(stmt).and_then(|(_, value)| operation_call_input(value, facts));
        use crate::hir::common::HirBinaryOpKind;
        let external_operation = matches!(stmt, HirStmt::Assign(assign)
            if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                ([HirLValue::Upvalue(_) | HirLValue::Global(_)], [HirExpr::Binary(binary)], None)
                    if matches!(binary.op, HirBinaryOpKind::Add | HirBinaryOpKind::Sub
                        | HirBinaryOpKind::Mul | HirBinaryOpKind::Div | HirBinaryOpKind::Mod
                        | HirBinaryOpKind::Pow | HirBinaryOpKind::Concat)));
        let right_operation = !arithmetic_initializer
            && !unary_initializer
            && operation_input.is_some_and(|(_, _, right)| right);
        if (!nested.indexed_keys.contains(&index) || nested.shared_producers.contains(&index))
            && (!nested.producers.contains(&index) || nested.shared_producers.contains(&index))
            && (external_operation
                || arithmetic_initializer
                || unary_initializer
                || comparison_initializer
                || (dialect == DecompileDialect::Luau || matches!(stmt, HirStmt::Assign(_)))
                    && operation_input.is_some_and(|(source, _, _)| {
                        facts.operation_result_home(source).is_some()
                    }))
            && (if external_operation {
                external_operation_attempt_start
            } else if comparison_initializer {
                comparison_attempt_start
            } else if right_operation {
                right_operation_attempt_start
            } else {
                operation_attempt_start
            }) != Some(start)
        {
            // operand 自身无法独立恢复，不代表其后完整 Boolean initializer 也失败。
            // 原地累计的右输入与高槽输入写低结果也是不同入口；一次失败不能
            // 截断后者的完整表达式。每类仍按 run 建一次索引，不逐声明重扫前缀。
            if external_operation {
                external_operation_attempt_start = Some(start);
            } else if comparison_initializer {
                comparison_attempt_start = Some(start);
            } else if right_operation {
                right_operation_attempt_start = Some(start);
            } else {
                operation_attempt_start = Some(start);
            }
            let declaration = comparison_initializer
                .then_some(split_initializer)
                .flatten();
            let initializer = declaration.map(|decl| {
                let HirStmt::Assign(assign) = stmt else {
                    unreachable!()
                };
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    values: assign.values.clone(),
                    ..decl.clone()
                }))
            });
            // 空声明与原赋值属于同一 initializer；只从 builder 的事件输入排除，
            // 原坐标仍在 removed 中，声明身份由同批 preview 保留。
            let run = flat[start..index - usize::from(declaration.is_some())]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();

            let candidate = if external_operation {
                external_operation_plan(context, &run, facts, dialect, stmt)
            } else if arithmetic_initializer || unary_initializer || comparison_initializer {
                operation_initializer_plan(
                    context,
                    &run,
                    facts,
                    dialect,
                    initializer.as_ref().unwrap_or(stmt),
                    following_frame_floor[index].all,
                    declaration.is_some(),
                )
            } else {
                operation_input_frame(
                    context,
                    &run,
                    facts,
                    dialect,
                    stmt,
                    following_frame_floor[index].all,
                )
            };
            if let Some(mut plan) = candidate {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("arithmetic frame consumes its CALL input");
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if logical_attempt_start != Some(start)
            && !nested.producers.contains(&index)
            && scalar_local(stmt).is_some_and(|(target, value)| {
                matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                    // 整个短路值若属于后继 CALL/CONCAT/RETURN 的准备区，
                    // 应由外层帧消费，不能先冻结其独立声明。
                    // debug 结果必须保留声明，后继 CALL 不能将其当参数准备退休；
                    // 仍可在此声明内部恢复完整 initializer。
                    && (proto.local_debug_hints[target.index()].is_some()
                        || proto.local_debug_scopes[target.index()].is_some()
                        || following_frame_floor[index].all.is_none_or(|floor| {
                        facts.trusted_local_home_slot(target)
                            .is_some_and(|home| home.slot() < floor)
                    }))
            })
        {
            logical_attempt_start = Some(start);
            let declaration = index.checked_sub(1).and_then(|previous| {
                flat[previous].and_then(|entry| split_expression_initializer(entry.stmt, stmt))
            });
            let initializer = declaration.map(|decl| {
                let HirStmt::Assign(assign) = stmt else {
                    unreachable!()
                };
                HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    values: assign.values.clone(),
                    ..decl.clone()
                }))
            });
            let run = flat[start..index - usize::from(declaration.is_some())]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = logical_call_result_frame(
                context,
                &run,
                facts,
                dialect,
                initializer.as_ref().unwrap_or(stmt),
                scalar_local(stmt)
                    .and_then(|(target, _)| boolean_prewrites.get(&target).copied().flatten()),
                declaration.is_some(),
            )
            .or_else(|| {
                literal_selection_frame(
                    context,
                    &run,
                    facts,
                    dialect,
                    initializer.as_ref().unwrap_or(stmt),
                )
            }) {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if let HirStmt::GenericFor(for_) = stmt {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = generic_for_dispatch_plan(context, &run, facts, dialect, for_) {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("dispatch frame consumes initializer");
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if matches!(
            stmt,
            HirStmt::If(_) | HirStmt::NumericFor(_) | HirStmt::Repeat(_)
        ) {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();

            // 合流结果空声明不是原准备事件；保留声明，只把之前的操作树
            // 收入控制头。源码入口在保留的声明之后核对。
            let preparation_end = run
                .iter()
                .rposition(|stmt| {
                    !matches!(stmt, HirStmt::LocalDecl(decl)
                    if decl.values.is_empty() && decl.initializer_merge_transaction.is_none())
                })
                .map_or(0, |index| index + 1);
            let retained_declarations = preparation_end != run.len();
            let run = &run[..preparation_end];
            let condition = match stmt {
                HirStmt::If(if_) => Some(&if_.cond),
                HirStmt::Repeat(repeat) => Some(&repeat.cond),
                _ => None,
            };
            if let Some(mut plan) = condition.and_then(|condition| {
                shared_condition_initializer(context, run, facts, dialect, condition)
            }) {
                let sink = start + plan.sink;
                plan.removed = flat[start + plan.start..sink]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = flat[sink].unwrap().id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
            let candidate = match stmt {
                HirStmt::If(if_) if if_.preserves_empty_test => {
                    // 候选拒绝[LayerBoundary]：退化 TEST 与后继物化写属于完整
                    // conditional initializer；不能先抽走输入，让原 owner 失去配对边界。
                    None
                }
                HirStmt::If(if_) => condition_plan(context, run, facts, dialect, &if_.cond)
                    .filter(|plan| {
                        // 候选拒绝[SemanticBarrier:Lifetime]：臂首 CALL 仍在该结果之上，
                        // 不能将条件输入声明收进 If 后提前让分支 scratch 覆盖它。
                        !prefix::branch_entry_requires_prefix(if_, plan.base, facts)
                            || !run[plan.start..].iter().any(|stmt| {
                                matches!(scalar_local(stmt), Some((_, HirExpr::Call(call)))
                                    if call.source_site.and_then(|source| facts.operation_result_home(source))
                                        == Some(plan.base))
                            })
                    }),
                HirStmt::NumericFor(for_) => numeric_for_plan(context, run, facts, dialect, for_),
                HirStmt::Repeat(repeat) => {
                    condition_plan(context, run, facts, dialect, &repeat.cond)
                }
                _ => unreachable!(),
            };
            if let Some(mut plan) = candidate {
                plan.prefix_at_sink = retained_declarations;
                plan.removed = flat[start + plan.start..start + preparation_end]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("header frame consumes a producer");
                plan.sink = stmt_id;
                plans.push(plan);
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if let HirStmt::Assign(assign) = stmt
            && index > start
            && lookup_attempt_start != Some(start)
            && let (
                [target @ (HirLValue::Local(_) | HirLValue::Param(_))],
                [HirExpr::TableAccess(access)],
                None,
            ) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            )
            && facts
                .table_read_result_home(access)
                .zip(
                    facts
                        .native_table_read_layout(access)
                        .map(|layout| layout.base)
                        .or_else(|| facts.upvalue_table_read_key(access).map(|(_, home)| home)),
                )
                .is_some_and(|(result, base)| {
                    result.slot() < base.slot()
                        // 低于 lookup 输入不等于已有源码变量；结果仍在后继 CALL
                        // 的准备区时，整帧拥有它，不能先提交赋值截断参数窗口。
                        && (context.expanded_callees.is_none()
                            || following_frame_floor[index]
                                .original_calls
                                .is_none_or(|floor| result.slot() < floor))
                })
        {
            lookup_attempt_start = Some(start);
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) =
                assignments::lookup_result(context, facts, dialect, &run, target, access)
            {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if dialect == DecompileDialect::Luau
            && index > start
            && lookup_attempt_start != Some(start)
            && let Some((HirBinding::Temp(target), HirExpr::TableAccess(access))) =
                scalar_binding(stmt)
            && let Some(home) = facts.trusted_temp_home_slot(target)
            && following_frame_floor[index].all.is_none()
        {
            // cleanup 前的临时结果仍由原 Assign 拥有；不跨 CLOSE 合并 RETURN。
            // 同一 run 至多构建一次索引，原始布局与整批 prefix 决定是否能收回 CALL。
            lookup_attempt_start = Some(start);
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();

            if let Some(mut plan) =
                lookup_initializer(context, &run, facts, dialect, None, access, home)
            {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }

        if dialect != DecompileDialect::Luajit
            && index > start
            && lookup_attempt_start != Some(start)
            && let Some((target, value @ HirExpr::TableAccess(access))) = scalar_local(stmt)
            && let Some(home) = facts.trusted_local_home_slot(target)
            && !barred.contains(&home)
            && !closed.contains(&home)
            && [&access.base, &access.key].iter().any(|value| {
                crate::hir::visit::any_expr(value, &mut |value|
                    matches!(value, HirExpr::LocalRef(local) if facts.trusted_local_home_slot(*local)
                        .is_some_and(|input| input.slot() >= home.slot())))
            })
            && ((matches!(stmt, HirStmt::LocalDecl(_))
                    && matches!(proto.inline_dispositions.local(target),
                        crate::hir::common::HirInlineDisposition::Preserve(reasons)
                            if reasons.contains(&crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix)))
                || following_frame_floor[index]
                    .original_calls
                    .is_some_and(|floor| home.slot() < floor)
                || following_table_base[index].is_some_and(|(local, original, write)| {
                    (local, original) == (target, home)
                        && facts.table_write_base_preparation(write, value).is_none()
                }))
            && facts.table_read_result_home(access) == Some(home)
        {
            // 同一未闭合 run 只尝试一次，避免每个索引都重建增长中的定义索引。
            lookup_attempt_start = Some(start);
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();

            if let Some(mut plan) =
                lookup_initializer(context, &run, facts, dialect, Some(target), access, home)
            {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = plan.removed[0];
                plan.sink = stmt_id;
                plans.push(plan);
                start = index + 1;
                constructor_high = None;
                continue;
            }
        }
        if dialect == DecompileDialect::Luau
            && let Some(Some(previous)) = index.checked_sub(1).and_then(|i| flat.get(i))
            && let Some(mut plan) = scalar_array_lookup_plan(
                context,
                facts,
                previous.stmt,
                stmt,
                following_frame_floor[index].original_calls,
            )
        {
            plan.start = previous.id;
            plan.sink = stmt_id;
            plan.removed.push(previous.id);
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if context.constants_fit_rk
            && let HirStmt::LocalDecl(decl) = stmt
            && decl.bindings.len() > 1 && decl.values.fixed.is_empty()
            && let Some(tail) = &decl.values.tail
            && tail.exact_width() == Some(decl.bindings.len())
            && let HirExpr::Call(call) = tail.as_expr()
            && let Some(frame) = facts.native_call_layout(call)
            && let Some((end, targets)) = multi_result_assignment(
                proto, &flat, index, decl.bindings.len(), frame.home, facts, dialect, barred, closed,
            )
            && (following_frame_floor[end].all.is_none_or(|slot| slot <= frame.home.slot())
                || flat.get(end + 1).copied().flatten().is_some_and(|entry|
                    matches!(entry.stmt, HirStmt::Assign(assign)
                        if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                            ([HirLValue::Local(local)], [HirExpr::Nil], None)
                                if decl.bindings.first() == Some(local)))))
        {
            // 整包已恢复的 CALL 继续消费原逆序写回，低槽常量字段不另需 LHS 准备。
            // preview 同时退休结果声明并核对后继帧，不能仅删除逻辑无读的结果根。
            plans.push(Plan {
                prefix_at_sink: false,
                luau_function_declaration: false,
                start: stmt_id, sink: flat[end].unwrap().id, base: frame.home,
                values: decl.values.clone(), result_locals: Vec::new(),
                discarded_result: None, assignment_targets: targets,
                luau_compound_global: false, indexed_target: None, continuing_root: None,
                retained_copies: Vec::new(),
                replayed_effects: flat[index + 1..end].iter().map(|entry| entry.unwrap().id).collect(),
                removed: flat[index..end].iter().map(|entry| entry.unwrap().id).collect(),
            });
            start = end + 1;
            constructor_high = None;
            continue;
        }
        if index > start
            && let Some(Some(previous)) =
                index.checked_sub(1).and_then(|previous| flat.get(previous))
            && !matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_initializer_producer.is_some())
            && let Some((call, width)) = batched_initializer(previous.stmt, stmt, facts)
        {
            // locals 的整组空声明只是待消费的初始化事务；按原 CALL 帧重发后，
            // 声明在 RHS 后生效，不能让额外 nil/永久前缀抬高调用准备区。
            let run = flat[start..index - 1]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            let frame = facts
                .native_call_frame(call)
                .or_else(|| facts.native_fastcall_frame(call))
                .unwrap();

            if let Some(mut builder) =
                frame_builder(context, &run, facts, dialect, frame.home.slot())
                && let Some(call) = builder.call(
                    call,
                    run.len(),
                    frame.home.slot(),
                    true,
                    CallWidth::Fixed(width),
                )
                && (builder.first_event.is_none() || builder.next_event == run.len())
            {
                let first = builder.first_event.unwrap_or(run.len());
                let assignment = multi_result_assignment(
                    proto, &flat, index, width, frame.home, facts, dialect, barred, closed,
                )
                .filter(|(end, _)| {
                    // 后继更高帧仍依赖这组声明占位；同槽或更低帧无需额外结果声明。
                    // 词法块末尾没有后继请求也可形成候选，实际位置与跨块后缀读写
                    // 仍由完整 preview 验证，不能因缺少后续 CALL 而永久拒绝写回。
                    following_frame_floor[*end]
                        .all
                        .is_none_or(|slot| slot <= frame.home.slot())
                        || flat.get(*end + 1).copied().flatten().is_some_and(|entry|
                            matches!((stmt, entry.stmt), (HirStmt::Assign(results), HirStmt::Assign(next))
                                if matches!((next.targets.as_slice(), next.values.fixed.as_slice(), &next.values.tail),
                                    ([HirLValue::Local(local)], [HirExpr::Nil], None)
                                        if results.targets.first() == Some(&HirLValue::Local(*local)))))
                });
                let sink_index = assignment.as_ref().map_or(index, |(end, _)| *end);
                // 部分结果复用旧绑定时，preview 必须证明其声明也由本批早先帧消费，
                // 才能重建整组 local；否则保留旧身份并拒绝整个依赖事务。
                let removed = flat[start + first..sink_index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    prefix_at_sink: false,
                    luau_function_declaration: false,
                    start: removed[0],
                    sink: flat[sink_index].unwrap().id,
                    base: frame.home,
                    values: HirValuePack {
                        fixed: Vec::new(),
                        tail: Some(HirPackTail::exact(HirExpr::Call(Box::new(call)), width)),
                    },
                    result_locals: Vec::new(),
                    discarded_result: None,
                    assignment_targets: assignment.map_or_else(Vec::new, |(_, targets)| targets),
                    luau_compound_global: false,
                    indexed_target: None,
                    continuing_root: None,
                    retained_copies: Vec::new(),
                    replayed_effects: if sink_index > index {
                        flat[index + 1..sink_index]
                            .iter()
                            .map(|entry| entry.unwrap().id)
                            .collect()
                    } else {
                        Vec::new()
                    },
                    removed,
                });
                start = sink_index + 1;
            } else {
                start = index + 1;
            }
            constructor_high = None;
            continue;
        }
        if concat_assignment_attempt_start != Some(start)
            && !nested.producers.contains(&index)
            && !nested.writes.contains(&index)
            && let Some(assignment) = concat_assignment_source(
                stmt,
                index
                    .checked_sub(1)
                    .and_then(|previous| flat[previous])
                    .map(|previous| previous.stmt),
                facts,
            )
            // 匿名槽被先前构造器复用，不等于当前 CONCAT 是已有源码变量赋值；
            // 后继帧仍拥有该结果时，连同 callee 与其余参数一起恢复。
            && (!matches!(assignment.target, HirLValue::Local(local)
                if context.proto.local_debug_hints[local.index()].is_none()
                    && context.proto.local_debug_scopes[local.index()].is_none())
                || following_frame_floor[index].original_calls.is_none_or(|floor| {
                    assignment.target_home.slot() < floor
                }))
            && {
                concat_assignment_attempt_start = Some(start);
                true
            }
            && let Some(mut plan) = concat_assignment(
                context,
                &flat[start..=index]
                    .iter()
                    .map(|entry| entry.unwrap().stmt)
                    .collect::<Vec<_>>(),
                facts,
                dialect,
                assignment,
            )
        {
            plan.removed = flat[start + plan.start..index]
                .iter()
                .map(|entry| entry.unwrap().id)
                .collect();
            plan.start = plan.removed.first().copied().unwrap_or(stmt_id);
            plan.sink = stmt_id;
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if dialect == DecompileDialect::Luau
            && let Some(plan) = assignments::global_arithmetic(
                context,
                facts,
                FlatStmt { id: stmt_id, stmt },
                index.checked_sub(1).and_then(|previous| flat[previous]),
            )
        {
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        let assignment_window = index
            .checked_sub(1)
            .and_then(|previous| flat[previous])
            .and_then(|previous| {
                if !matches!(stmt, HirStmt::Assign(assign)
                if matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(_)]))
                {
                    return None;
                }
                let mut entries = Vec::with_capacity(3);
                if let Some(earlier) = index.checked_sub(2).and_then(|earlier| flat[earlier]) {
                    entries.push(earlier);
                }
                entries.extend([previous, FlatStmt { id: stmt_id, stmt }]);
                Some(entries)
            });
        if let Some(entries) = assignment_window
            && let Some(mut plan) = completed_value_assignment(
                context,
                &entries.iter().map(|entry| entry.stmt).collect::<Vec<_>>(),
                facts,
                dialect,
                entries.len() - 1,
                following_frame_floor[index].all,
                flat.get(index + 1).copied().flatten().and_then(|next| {
                    let (_, HirExpr::GlobalRef(global)) = scalar_binding(next.stmt)? else {
                        return None;
                    };
                    let crate::hir::common::HirOperationSources::Single(source) = global.sources
                    else {
                        return None;
                    };
                    facts.operation_result_home(source)
                }),
            )
        {
            plan.removed = entries[plan.start..plan.sink]
                .iter()
                .map(|entry| entry.id)
                .collect();
            plan.start = entries[plan.start].id;
            plan.sink = stmt_id;
            plans.push(plan);
            start = index + 1;
            constructor_high = None;
            continue;
        }
        let indexed_sink = match stmt {
            HirStmt::Assign(assign)
                if indexed::is_candidate(assign)
                    && (assign
                        .values
                        .fixed
                        .first()
                        .is_some_and(indexed::is_rhs_candidate)
                        || nested.constructor_results.contains(&index)
                        || matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(value)]
                            if index.checked_sub(1).and_then(|previous| flat.get(previous))
                                .and_then(Option::as_ref)
                                .and_then(|previous| scalar_local(previous.stmt))
                                .is_some_and(|(local, expr)| local == *value && indexed::is_rhs_candidate(expr)))
                        || matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(value)]
                            if index.checked_sub(1).and_then(|previous| flat.get(previous))
                                .and_then(Option::as_ref)
                                .is_some_and(|previous| matches!(previous.stmt, HirStmt::TableSetList(batch)
                                    if batch.base == HirExpr::LocalRef(*value))))) =>
            {
                Some((index, assign.as_ref()))
            }
            _ if scalar_local(stmt).is_some_and(|(_, value)| indexed::is_rhs_candidate(value)) => {
                flat.get(index + 1)
                    .and_then(Option::as_ref)
                    .and_then(|next| {
                        let HirStmt::Assign(assign) = next.stmt else {
                            return None;
                        };
                        (indexed::is_candidate(assign)
                            && scalar_local(stmt).is_some_and(|(local, _)|
                                matches!(assign.values.fixed.as_slice(), [HirExpr::LocalRef(value)] if local == *value)
                                    || matches!(assign.targets.as_slice(), [HirLValue::TableAccess(access)]
                                        if access.base == HirExpr::LocalRef(local))))
                        .then_some((index + 1, assign.as_ref()))
                    })
            }
            _ => None,
        };
        let indexed_sink = indexed_sink.and_then(|(end, assign)| {
            let rhs = assign.values.fixed.first().and_then(|value| match value {
                HirExpr::LocalRef(local) => end
                    .checked_sub(1)
                    .and_then(|index| flat.get(index))
                    .and_then(Option::as_ref)
                    .and_then(|entry| scalar_local(entry.stmt))
                    .filter(|(target, _)| target == local)
                    .map(|(_, value)| value),
                value => Some(value),
            });
            if !matches!(rhs, Some(HirExpr::Call(_))) {
                return Some((end, assign, false));
            }
            // 动态 key 或寄存器目标由 indexed 帧共同准备；固定 SETTABUP 没有
            // 左值准备区，继续交给原单结果赋值 owner。
            let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
                return None;
            };
            (facts.native_table_write_layout(access).is_some()
                || facts
                    .native_upvalue_table_write_layout(access)
                    .is_some_and(|layout| layout.key.is_some()))
            .then_some((end, assign, true))
        });
        if let Some((end, assign, call_rhs)) = indexed_sink
            && end > start
            // 发布新表是已知展开体的中间事件；只有完整外层 CALL 可以消费它。
            && !expanded::is_published_table_write(context, flat[end].unwrap().stmt)
            // 未完成构造器的字段准备属于原构造事务，不在这里拆走其 CONCAT 或 key。
            && !nested.writes.contains(&end)
            && !nested.producers.contains(&(end - 1))
        {
            let run = flat[start..end]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = indexed::plan(
                context,
                &run,
                facts,
                dialect,
                assign,
                live_indexed_results.contains(&end),
            )
            .filter(|plan| {
                // PUC 的独立 allocation local 可能在发布后继续保活。仅有 SETTABLE
                // use-to-Def 不足以退休它；后继原 CALL 还须从同一槽重新开始，且左值
                // 必须是已有低槽 binding，不能把 SETTABUP 的长期根当作 scratch。
                dialect == DecompileDialect::Luau
                    // RHS 已是原位分配表达式时，本事务只消费左值准备，不退休分配声明。
                    // builder 已核对它在 key 后的原结果槽，无需独立 local 的后继退休证明。
                    || matches!(assign.values.fixed.as_slice(), [HirExpr::TableConstructor(_)])
                    || (plan.indexed_target.as_ref().is_some_and(|target| {
                        facts
                            .table_write_base_preparation(target, &target.base)
                            .is_some_and(|(_, home)| home == plan.base)
                    }) && flat.get(end + 1).copied().flatten().is_some_and(|next| {
                        scalar_binding(next.stmt).is_some_and(|(_, value)| match value {
                            HirExpr::GlobalRef(global) => {
                                let crate::hir::common::HirOperationSources::Single(source) =
                                    global.sources
                                else {
                                    return false;
                                };
                                facts.operation_result_home(source) == Some(plan.base)
                            }
                            HirExpr::TableConstructor(table) => {
                                facts.allocation_result_home(table) == Some(plan.base)
                            }
                            _ => false,
                        })
                    }))
                    || !matches!(plan.values.fixed.as_slice(), [HirExpr::TableConstructor(table)]
                        if table.fields.is_empty() && table.trailing_multivalue.is_none())
                    || ((following_frame_floor[end].original_calls == Some(plan.base.slot())
                        || flat.get(end + 1).copied().flatten().is_some_and(|next| {
                            scalar_binding(next.stmt).is_some_and(|(binding, value)| {
                                matches!(
                                    value,
                                    HirExpr::Nil
                                        | HirExpr::Boolean(_)
                                        | HirExpr::Integer(_)
                                        | HirExpr::Number(_)
                                ) && match binding {
                                    HirBinding::Local(local) => {
                                        facts.trusted_local_home_slot(local) == Some(plan.base)
                                    }
                                    HirBinding::Temp(temp) => {
                                        facts.trusted_temp_home_slot(temp) == Some(plan.base)
                                    }
                                    _ => false,
                                }
                            })
                        }))
                        && matches!(assign.targets.as_slice(), [HirLValue::TableAccess(access)]
                            if matches!(access.base, HirExpr::ParamRef(_) | HirExpr::LocalRef(_))))
            }) {
                plan.removed = flat[start + plan.start..end]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("indexed frame consumes producers");
                plan.sink = flat[end].unwrap().id;
                plans.push(plan);
                start = end + 1;
                constructor_high = None;
                continue;
            }
            if end == index && !call_rhs {
                start = index + 1;
                constructor_high = None;
                continue;
            }
            // 完整字段帧尚无证据时，原独立 CONCAT 初始化仍可尝试；不因候选出现停用旧能力。
        }
        if matches!(
            dialect,
            DecompileDialect::Lua51
                | DecompileDialect::Lua52
                | DecompileDialect::Lua53
                | DecompileDialect::Lua54
                | DecompileDialect::Lua55
                | DecompileDialect::Luau
                | DecompileDialect::Luajit
        ) && index > start
            && let HirStmt::Assign(assign) = stmt
            && let ([target], [HirExpr::LocalRef(source)], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            )
            && let Some(Some(previous)) =
                index.checked_sub(1).and_then(|previous| flat.get(previous))
            && let Some((producer, HirExpr::Call(call))) = scalar_local(previous.stmt)
            && producer == *source
            && let Some(frame) = facts
                .native_call_frame(call)
                .or_else(|| facts.native_fastcall_frame(call))
            && (facts.trusted_local_home_slot(*source) == Some(frame.home)
                || facts.fixed_call_result(call, 0).is_some_and(|temp|
                    facts.promoted_local_for_temp(temp) == Some(*source)
                    && facts.trusted_temp_home_slot(temp) == Some(frame.home)))
            // 候选拒绝[LayerBoundary]：后继更高帧仍需要结果槽的声明前缀；低槽 COPY 不结束源槽根。
            && (!matches!(target, HirLValue::Local(_) | HirLValue::Param(_))
                || following_frame_floor[index].all.is_none_or(|floor| floor <= frame.home.slot()))
            && let Some(assignment_targets) = call_assignment_targets(
                target,
                frame.home,
                facts,
                dialect,
                constants_fit_rk,
                barred,
            )
            // 候选拒绝[LayerBoundary]：未结束构造器的字段 producer 仍属于整个构造/SETLIST 事务；先消费内层
            // CALL 会冻结外层 seed 的前缀，使原开放数组无法合并（regress_33）。
            && (!assignment_targets.is_empty() || !nested.producers.contains(&(index - 1)))
            // 展开帧的低 COPY 仍可能是后继比较参数；不能先按活动变量赋值
            // 截断准备区。只有整批展开 owner 可延期，最后仍须重放完整后缀。
            && !(context.expanded_callees.is_some()
                && expanded::scalar_result_copy(facts, call, target))
        {
            // 活动低槽赋值在空闲区准备单结果调用，再 MOVE 回目标。LuaJIT 的 frame gap
            // 由原 args 布局核对；FASTCALL 仍走其 direct/fallback 协议，共同保留结果写回。
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();

            let (move_homes, retained_copies) = retained_result_copies(&flat, index, call, facts)
                .unwrap_or_else(|| {
                    (
                        match target {
                            HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
                            HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
                            _ => None,
                        }
                        .into_iter()
                        .collect(),
                        Vec::new(),
                    )
                });
            if let Some(mut builder) =
                frame_builder(context, &run, facts, dialect, frame.home.slot()).map(
                    |mut builder| {
                        builder.result_move = Some((*source, run.len() - 1, move_homes));
                        builder
                    },
                )
                && let Some(value) = builder.expr(
                    &HirExpr::LocalRef(*source),
                    run.len(),
                    frame.home.slot(),
                    None,
                    false,
                    true,
                    None,
                )
                && let Some(first) = builder.first_event
                && builder.next_event == run.len()
            {
                let removed = flat[start + first..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    prefix_at_sink: false,
                    luau_function_declaration: false,
                    start: removed[0],
                    sink: stmt_id,
                    base: frame.home,
                    values: vec![value].into(),
                    result_locals: Vec::new(),
                    discarded_result: None,
                    assignment_targets: assignment_targets
                        .into_iter()
                        .map(HirLValue::Local)
                        .collect(),
                    luau_compound_global: false,
                    indexed_target: None,
                    continuing_root: None,
                    retained_copies,
                    replayed_effects: Vec::new(),
                    removed,
                });
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if let HirStmt::Return(ret) = stmt
            && (!ret.values.fixed.is_empty()
                || (dialect == DecompileDialect::Luau && ret.values.tail.is_some()))
        {
            // Luau 的 return f(...) 是普通开放 CALL 加 RETURN，没有 TAILCALL。
            // 连同原 RETURN 来源走开放返回帧，不能向 CALL 请求不存在的 Tail 协议。
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();
            if let Some(mut plan) = return_plan(context, &run, facts, dialect, ret) {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect();
                plan.start = *plan
                    .removed
                    .first()
                    .expect("return frame consumes a producer");
                plan.sink = stmt_id;
                plans.push(plan);
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        if let Some((local, HirExpr::TableConstructor(_))) = scalar_local(stmt)
            && let Some(home) = facts.trusted_local_home_slot(local)
        {
            constructor_high =
                Some(constructor_high.map_or(home.slot(), |old| old.max(home.slot())));
        }
        // 紧邻外部写回属于同一赋值帧；不能先冻结 CALL 结果，抬高后继复用槽的前缀。
        let pending_result_store = scalar_local(stmt).is_some_and(|(target, value)| {
            let HirExpr::Call(call) = value else {
                return false;
            };
            let Some(frame) = facts
                .native_call_frame(call)
                .or_else(|| facts.native_fastcall_frame(call))
            else {
                return false;
            };
            flat.get(index + 1)
                .and_then(Option::as_ref)
                .is_some_and(|next| {
                    matches!(scalar_local(next.stmt), Some((copy, HirExpr::LocalRef(source)))
                    if *source == target && facts.trusted_local_home_slot(copy)
                        .is_none_or(|home| home.slot() <= frame.home.slot()))
                        || matches!(next.stmt, HirStmt::Assign(assign)
                            if matches!((assign.targets.as_slice(), assign.values.fixed.as_slice(), &assign.values.tail),
                                ([external @ (HirLValue::Global(_) | HirLValue::Param(_) | HirLValue::Upvalue(_))], [HirExpr::LocalRef(source)], None)
                                    if *source == target && call_assignment_targets(
                                        external, frame.home, facts, dialect, constants_fit_rk, barred,
                                    ).is_some()))
                })
        });
        let initializer = source_call_initializer(proto, stmt, facts, &captures.bindings.locals, nested.shared_producers.contains(&index))
            // 独立声明的结果跨过不读取它的控制头时，不属于该条件的准备区。
            // 原 LocalDecl 保留，收回 RHS 的 callee/receiver；槽与完整后缀仍由 preview 验证。
            || (matches!(stmt, HirStmt::LocalDecl(_))
                && !nested.producers.contains(&index)
                && scalar_local(stmt).is_some_and(|(local, value)| {
                    matches!(value, HirExpr::Call(_))
                        && flat.get(index + 1).and_then(Option::as_ref).is_some_and(|next|
                            matches!(next.stmt, HirStmt::If(branch)
                                if !super::super::mention::expr_mentions_local(&branch.cond, local)))
                }))
            || (!pending_result_store
                && !nested.producers.contains(&index)
                // 多次读取或物理根保活都需要独立结果身份；即使结果随后直接被覆盖，
                // 也可合回同槽初始化。单次嵌套消费仍留给外层完整帧，不提前截断准备区。
                && (nested.shared_producers.contains(&index)
                    || (!nested.has_read(index) && scalar_local(stmt)
                        .is_some_and(|(local, _)| proto.physical_root_locals.contains(&local))))
                && index
                    .checked_sub(1)
                    .and_then(|previous| flat[previous])
                    .is_some_and(|previous| {
                        adjacent_callee_result_initializer(proto, previous.stmt, stmt, facts)
                    }))
            || fastcall_copy_initializer(
                stmt,
                flat.get(index + 1)
                    .and_then(Option::as_ref)
                    .map(|next| next.stmt),
                facts,
                following_frame_floor[index].all,
                nested.producers.contains(&index),
            )
            || (constructor_high.is_some()
                    // 参数构造器不能提前结束 CALL 与写回的事务；独立提交结果声明
                    // 会固定其物理前缀，让低槽或环境目标无法收回准备变量。
                    && !pending_result_store
                    && !nested.producers.contains(&index)
                    && scalar_local(stmt).is_some_and(|(_, value)| {
                        let HirExpr::Call(call) = value else {
                            return false;
                        };
                        // 原 SELF 还会在同槽消费此结果时，表参数不结束方法链。
                        // 多次读取仍需独立身份；整链的事件和生命周期由外层帧核对。
                        if !nested.shared_producers.contains(&index)
                            && call.source_site
                                .and_then(|site| facts.operation_result_temp(site))
                                .is_some_and(|result| nested.method_receivers.contains(&result))
                        {
                            return false;
                        }
                        // 已签证为后继 CALL 参数的结果仍属于外层准备区；
                        // 表构造器本身不能使它提前成为独立初始化。
                        if call.source_site
                            .and_then(|site| facts.operation_result_temp(site))
                            .is_some_and(|temp| facts.temp_is_transferred_call_argument(temp))
                        {
                            return false;
                        }
                        facts
                            .native_call_frame(call)
                            .or_else(|| facts.native_fastcall_frame(call))
                            .is_some_and(|frame| {
                                // 已完成的低槽对象不是当前 CALL 的构造器参数。否则 obj 后的
                                // :add():add() 会被逐个提前提交并冻结中间声明，阻止外层帧整体恢复。
                                constructor_high.is_some_and(|high| high >= frame.home.slot())
                            })
                    }))
            || scalar_local(stmt).is_some_and(|(_, value)| {
                let HirExpr::Call(call) = value else {
                    return false;
                };
                // 构造字段已经拥有这个结果版本；后一个数组元素的高槽准备
                // 不是独立声明边界，完整构造帧仍须消费中间 CALL。
                if nested.producers.contains(&index) {
                    return false;
                }
                let Some(frame) = facts
                    .native_call_frame(call)
                    .or_else(|| facts.native_fastcall_frame(call))
                else {
                    return false;
                };
                // 多次消费或后继更高帧需要原结果的独立身份；低槽 COPY 本身
                // 不结束该源槽。保留 COPY，并用后继下界核对结果声明的占位。
                if pending_result_store && !nested.shared_producers.contains(&index)
                    && following_frame_floor[index].all.is_none_or(|floor| floor <= frame.home.slot())
                {
                    return false;
                }
                following_frame_floor[index]
                        .all
                        .is_some_and(|floor| frame.home.slot() < floor)
                        // 函数末端的独立结果没有后继求值帧；空 RETURN 不应阻止
                        // 同槽 callee 与结果的完整恢复。仍有后缀消费者时沿原调度处理。
                        || (!nested.producers.contains(&index)
                            && flat.get(index + 1).and_then(Option::as_ref).is_some_and(|next|
                                matches!(next.stmt, HirStmt::Return(ret) if ret.values.is_empty())
                                    || low_slot_store_boundary(next.stmt, facts, dialect, frame.home.slot())))
            });
        // 低槽 GETTABLE 的 key CALL 与高槽 base 快照同属一个 RHS；不能先把
        // key 固定成独立声明并截断 run，再要求 lookup owner 找回已隔开的 base。
        let pending_lookup_key = !nested.shared_producers.contains(&index)
            && scalar_local(stmt).is_some_and(|(local, value)| {
                matches!(value, HirExpr::Call(_))
                    && flat.get(index + 1).copied().flatten().is_some_and(|next| {
                        let HirStmt::Assign(assign) = next.stmt else {
                            return false;
                        };
                        let [HirExpr::TableAccess(access)] = assign.values.fixed.as_slice() else {
                            return false;
                        };
                        access.key == HirExpr::LocalRef(local)
                            && facts.table_read_result_home(access).is_some_and(|result| {
                                let key = facts
                                    .native_table_read_layout(access)
                                    .and_then(|layout| layout.key)
                                    .or_else(|| {
                                        facts.upvalue_table_read_key(access).map(|(_, home)| home)
                                    });
                                key.is_some_and(|key| {
                                    result.slot() < key.slot()
                                        && facts.trusted_local_home_slot(local) == Some(key)
                                })
                            })
                    })
            });
        let initializer = initializer
            && !pending_lookup_key
            && (!nested.indexed_keys.contains(&index) || nested.shared_producers.contains(&index));
        let concat_value = scalar_local(stmt)
            .map(|(local, value)| (Some(local), value))
            .or_else(|| {
                let HirStmt::Assign(assign) = stmt else {
                    return None;
                };
                let ([target], [value], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) else {
                    return None;
                };
                (matches!(target, HirLValue::Upvalue(_))
                    || matches!(target, HirLValue::Global(_) if dialect != DecompileDialect::Luau))
                .then_some((None, value))
            });
        let concat_sink = concat_value.and_then(|(local, value)| {
            // 字段 CONCAT 与其 SETTABLE 同属构造器；独立声明会提前截断外层准备区。
            if nested.producers.contains(&index) {
                return None;
            }
            let HirExpr::Binary(binary) = value else {
                return None;
            };
            if binary.op != crate::hir::common::HirBinaryOpKind::Concat
                // 结果还要写回既有低槽时，不能先冻结独立声明并截断输入 run。
                || flat.get(index + 1).and_then(Option::as_ref).is_some_and(|next|
                    concat_assignment_source(next.stmt, Some(stmt), facts).is_some())
            {
                return None;
            }
            let home = facts.operation_result_home(binary.source_site?)?;
            // 只有当前结果入口能重发的 CONCAT 才独立结束准备区。
            // 展开体写入低槽 capture 时，buffer 属于后继整帧，不能因候选失败截断它。
            if facts.native_concat_buffer(binary)?.start.index()
                != home.slot() + usize::from(dialect == DecompileDialect::Luau)
            {
                return None;
            }
            if let HirStmt::Assign(assign) = stmt
                && let [HirLValue::Global(global)] = assign.targets.as_slice()
                && (!constants_fit_rk
                    || facts.global_write_value_home(global, dialect) != Some(home))
            {
                // 全局写没有寄存器左值准备；键须原本内嵌，写入仍消费原 CONCAT 结果槽。
                return None;
            }
            (local.is_none_or(|local| facts.trusted_local_home_slot(local) == Some(home))
                // 全局/上值写不冻结新的源码 local；只有独立 local 初始化需要低于后继帧。
                && (local.is_none()
                    || following_frame_floor[index]
                        .all
                        .is_none_or(|floor| home.slot() < floor)))
            .then_some((local, binary, home))
        });
        let discarded_result = (|| {
            let HirStmt::LocalDecl(decl) = stmt else {
                return None;
            };
            let ([local], [HirExpr::Call(call)], None) = (
                decl.bindings.as_slice(),
                decl.values.fixed.as_slice(),
                &decl.values.tail,
            ) else {
                return None;
            };
            let next = flat.get(index + 1)?.as_ref()?.stmt;
            let (target, value) = scalar_local(next)?;
            if target != *local
                || !matches!(next, HirStmt::Assign(_))
                || !matches!(
                    value,
                    HirExpr::Nil | HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                )
                || proto
                    .local_debug_hints
                    .get(local.index())
                    .is_some_and(Option::is_some)
                || proto
                    .local_debug_scopes
                    .get(local.index())
                    .is_some_and(Option::is_some)
                || matches!(proto.inline_dispositions.local(*local), crate::hir::common::HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
            {
                return None;
            }
            let frame = facts.native_call_frame(call)?;
            (facts.trusted_local_home_slot(*local) == Some(frame.home)
                && frame.results
                    == Some(ResultPack::Fixed(crate::transformer::RegRange {
                        start: crate::transformer::Reg(frame.home.slot()),
                        len: 1,
                    }))
                && !closed.contains(&frame.home)
                && !barred.contains(&frame.home))
            .then_some((*local, call, frame.home))
        })();
        if let Some((local, call, home)) = discarded_result {
            let run = flat[start..index]
                .iter()
                .map(|entry| entry.unwrap().stmt)
                .collect::<Vec<_>>();

            if let Some(mut builder) = frame_builder(context, &run, facts, dialect, home.slot())
                && let Some(call) =
                    builder.call(call, run.len(), home.slot(), true, CallWidth::Single)
                && (builder.first_event.is_none() || builder.next_event == run.len())
            {
                let first = builder.first_event.unwrap_or(run.len());
                let removed = flat[start + first..index]
                    .iter()
                    .map(|entry| entry.unwrap().id)
                    .collect::<Vec<_>>();
                plans.push(Plan {
                    prefix_at_sink: false,
                    luau_function_declaration: false,
                    start: removed.first().copied().unwrap_or(stmt_id),
                    sink: stmt_id,
                    base: home,
                    values: vec![HirExpr::Call(Box::new(call))].into(),
                    result_locals: Vec::new(),
                    discarded_result: Some(local),
                    assignment_targets: Vec::new(),
                    luau_compound_global: false,
                    indexed_target: None,
                    continuing_root: None,
                    retained_copies: Vec::new(),
                    replayed_effects: Vec::new(),
                    removed,
                });
            }
            start = index + 1;
            constructor_high = None;
            continue;
        }
        let sink = match stmt {
            HirStmt::GenericFor(for_) if for_.iterator.fixed.is_empty() => {
                for_.iterator.tail.as_ref().and_then(|tail| {
                    let HirExpr::Call(call) = tail.as_expr() else {
                        return None;
                    };

                    let frame = facts.generic_for_body_frame(for_)?;
                    if tail
                        .exact_width()
                        .is_some_and(|width| width != frame.initializers.len())
                        || facts.native_call_layout(call)?.home != *frame.initializers.first()?
                    {
                        return None;
                    }
                    Some((call.as_ref(), CallWidth::Fixed(frame.initializers.len())))
                })
            }
            HirStmt::CallStmt(sink) => Some((&sink.call, CallWidth::Ignore)),
            HirStmt::Assign(assign) if call_result_bindings(assign, facts).is_some() => {
                let tail = assign.values.tail.as_ref().unwrap();
                let HirExpr::Call(call) = tail.as_expr() else {
                    unreachable!()
                };
                Some((call.as_ref(), CallWidth::Fixed(assign.targets.len())))
            }
            HirStmt::Assign(assign)
                if let ([target], [HirExpr::Call(call)], None) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                ) && matches!(target, HirLValue::Local(_))
                    && let Some(frame) = facts
                        .native_call_frame(call)
                        .or_else(|| facts.native_fastcall_frame(call))
                    && call_assignment_targets(
                        target,
                        frame.home,
                        facts,
                        dialect,
                        constants_fit_rk,
                        barred,
                    )
                    .is_some() =>
            {
                let HirExpr::Call(call) = &assign.values.fixed[0] else {
                    unreachable!()
                };
                Some((call.as_ref(), CallWidth::Single))
            }
            HirStmt::GlobalDecl(decl) if dialect == DecompileDialect::Lua55 => {
                // 只消费 protocol owner 已恢复的完整调用 RHS，不拆分 probe/store 或补结果。
                match (decl.values.fixed.as_slice(), &decl.values.tail) {
                    ([HirExpr::Call(call)], None) if decl.names.len() == 1 => {
                        Some((call.as_ref(), CallWidth::Single))
                    }
                    ([], Some(tail)) if tail.exact_width() == Some(decl.names.len()) => {
                        match tail.as_expr() {
                            HirExpr::Call(call) => {
                                Some((call.as_ref(), CallWidth::Fixed(decl.names.len())))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            HirStmt::Return(ret) if ret.values.fixed.is_empty() => {
                ret.values.tail.as_ref().and_then(|tail| {
                    if tail.exact_width().is_some() {
                        return None;
                    }
                    let HirExpr::Call(call) = tail.as_expr() else {
                        return None;
                    };
                    Some((call.as_ref(), CallWidth::Tail))
                })
            }
            _ if initializer => scalar_local(stmt).and_then(|(target, value)| {
                let HirExpr::Call(call) = value else {
                    return None;
                };
                let frame = facts
                    .native_call_frame(call)
                    .or_else(|| facts.native_fastcall_frame(call))?;
                (facts.trusted_local_home_slot(target) == Some(frame.home))
                    .then_some((call.as_ref(), CallWidth::Single))
            }),
            _ => None,
        };
        if sink.is_some() || concat_sink.is_some() {
            // 无条件 scope 入口没有求值；只借用当前连续语句，出口 marker 切断 run。
            let stmts = flat[start..=index]
                .iter()
                .map(|entry| entry.as_ref().unwrap().stmt)
                .collect::<Vec<_>>();

            let candidate = match sink {
                Some((call, width)) => plan(
                    context,
                    &stmts,
                    facts,
                    dialect,
                    stmts.len() - 1,
                    call,
                    width,
                ),
                None => concat_sink.and_then(|(local, binary, home)| {
                    let run = &stmts[..stmts.len() - 1];
                    let mut builder = frame_builder(context, run, facts, dialect, home.slot())?;
                    let value = builder.concat(binary, run.len(), home.slot())?;
                    let start = builder.first_event?;
                    (builder.next_event == run.len()).then_some(Plan {
                        prefix_at_sink: false,
                        luau_function_declaration: false,
                        start,
                        sink: run.len(),
                        base: home,
                        values: vec![value].into(),
                        result_locals: local.into_iter().collect(),
                        discarded_result: None,
                        assignment_targets: Vec::new(),
                        luau_compound_global: false,
                        indexed_target: None,
                        continuing_root: None,
                        retained_copies: Vec::new(),
                        replayed_effects: Vec::new(),
                        removed: Vec::new(),
                    })
                }),
            };
            if let Some(mut plan) = candidate {
                plan.removed = flat[start + plan.start..index]
                    .iter()
                    .map(|entry| entry.as_ref().unwrap().id)
                    .collect();
                plan.start = plan.removed.first().copied().unwrap_or(stmt_id);
                plan.sink = stmt_id;
                plans.push(plan);
            }
        }
        // 三类 VM 的字段/SETLIST 都已由 FrameBuilder 核对原布局与事件；
        // 收集器保留完整参数构造区，不能在接收 CALL 前先丢掉其 allocation/callee。
        let constructor_step = super::super::table_constructors::constructor_write(stmt).is_some()
            || matches!(stmt, HirStmt::LocalRootRelease(_));
        let pending_initializer = matches!(stmt, HirStmt::LocalDecl(decl)
            if decl.values.is_empty())
            || flat
                .get(index + 1)
                .and_then(Option::as_ref)
                .is_some_and(|next| {
                    split_expression_initializer(stmt, next.stmt).is_some()
                        || batched_initializer(stmt, next.stmt, facts).is_some()
                })
            || matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_initializer_producer.is_some())
            || nil_argument_group(stmt, facts).is_some();
        if initializer
            || concat_sink.is_some()
            || (scalar_binding(stmt).is_none() && !constructor_step && !pending_initializer)
        {
            // 含表的完整 initializer 每段最多尝试一次；拒绝的表也不能作为后续调用树
            // 的中间 producer。普通无表嵌套调用仍沿现有单次 CallStmt 扫描。
            start = index + 1;
            constructor_high = None;
        }
    }
    if prefix_assumption {
        prefix_assumed_sinks.extend(plans[collected..].iter().map(|plan| plan.sink));
    }
    // 构造器事务可能已消费最初的值，却为后继原槽写留下 empty LocalDecl。
    // 紧邻的一组空声明及其首写被本批完整帧消费时，声明必须同批退休；
    // 整体 preview 仍逐身份拒绝任何在重写前的 read/capture，不能靠空声明掩盖缺失值。
    // 真实 LOADNIL 仍有独立写入义务，不从空声明外形推断可以删除。
    let original_nil_locals = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect::<BTreeSet<_>>();
    let mut empty_declarations = BTreeMap::new();
    let mut pending = Vec::new();
    let mut first_local = None;
    for entry in &flat {
        let Some(entry) = entry else {
            pending.clear();
            first_local = None;
            continue;
        };
        if let HirStmt::LocalDecl(decl) = entry.stmt
            && removable_empty_declaration(proto, &original_nil_locals, decl)
        {
            first_local.get_or_insert(decl.bindings[0]);
            pending.push(entry.id);
            continue;
        }
        if let Some(local) = first_local.take()
            && scalar_local(entry.stmt).is_some_and(|(written, _)| written == local)
        {
            empty_declarations.insert(entry.id, (std::mem::take(&mut pending), local));
        }
        pending.clear();
    }
    for plan in &mut plans[first_plan..] {
        if let Some((declarations, local)) = empty_declarations.remove(&plan.start)
            && plan.removed.first() == Some(&plan.start)
            && facts.trusted_local_home_slot(local) == Some(plan.base)
        {
            plan.start = declarations[0];
            plan.removed.splice(0..0, declarations);
        }
    }
    if !context.constants_fit_rk {
        let mut index = 0;
        plans.retain(|plan| {
            let belongs = index >= first_plan;
            index += 1;
            !belongs
                || !prefix_assumed_sinks.contains(&plan.sink)
                || plan.start >= rk_prefix_end
                || plan.sink < rk_prefix_end
        });
    }
}
/// initializer CALL 与 dispatch root endpoints 属于同一循环头事务。
/// marker 只提供原配对；完整 CALL、控制槽、成功结果槽及最终声明前缀仍分别核对。
fn generic_for_dispatch_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirGenericFor,
) -> Option<Plan> {
    let frame = facts.generic_for_body_frame(for_)?;
    let dispatch = for_.body_frame_source?;
    let base = *frame.initializers.first()?;
    let results = for_
        .dispatch_results
        .iter()
        .zip(&frame.bindings)
        .map(|(result, home)| (result.result_def, *home))
        .collect::<BTreeMap<_, _>>();
    let mut seen_results = BTreeSet::new();
    let mut release_start = run.len();
    while let Some(HirStmt::Assign(assign)) = release_start.checked_sub(1).map(|index| run[index]) {
        let Some(release) = assign.generic_for_dispatch_release else {
            break;
        };
        let home = *results.get(&release.result_def)?;
        let target_matches = match assign.targets.as_slice() {
            [HirLValue::Temp(temp)] => *temp == release.released,
            [HirLValue::Local(local)] => {
                facts.promoted_local_for_temp(release.released) == Some(*local)
                    && facts.trusted_local_home_slot(*local) == Some(home)
            }
            _ => false,
        };
        if release.dispatch != dispatch
            || !target_matches
            || facts.trusted_temp_home_slot(release.released) != Some(home)
            || assign.values.fixed.as_slice() != [HirExpr::Nil]
            || assign.values.tail.is_some()
            || (context.barred.contains(&home)
                && !facts.temp_definition_reference_unaliased(release.released))
            || context.closed.contains(&home)
            || !seen_results.insert(release.result_def)
        {
            return None;
        }
        release_start -= 1;
    }
    // dispatch release 是可选的尾部协议；没有 release 时仍需把 initializer
    // CALL 与其构造准备作为完整帧证明，不能要求 iterator 先独立折叠。
    let initializer = release_start.checked_sub(1)?;
    let HirStmt::Assign(assign) = run[initializer] else {
        return None;
    };
    let call = super::super::generic_for_iterators::single_call_initializer(assign, for_)?;
    let results_unaliased = facts.native_call_layout(call)?.fixed_results_unaliased;
    if assign
        .targets
        .iter()
        .zip(&frame.initializers)
        .any(|(target, home)| {
            let (home_slot, has_debug) = match target {
                HirLValue::Temp(temp) => (
                    facts.trusted_temp_home_slot(*temp),
                    context
                        .proto
                        .temp_debug_locals
                        .get(temp.index())
                        .is_some_and(Option::is_some),
                ),
                HirLValue::Local(local) => (
                    facts.trusted_local_home_slot(*local),
                    context.proto.local_debug_hints[local.index()].is_some()
                        || context.proto.local_debug_scopes[local.index()].is_some(),
                ),
                _ => return true,
            };
            home_slot != Some(*home)
                || has_debug
                || (context.barred.contains(home) && !results_unaliased)
                || context.closed.contains(home)
        })
    {
        return None;
    }
    // 紧邻的整组空声明与初始化一起消费；连续循环也可复用前一组声明。
    // 后一种情况由整批 preview 核对旧声明是否已退休及后继读写，不能把它
    // 预先合成普通 initializer 而丢掉 GenericFor 的 occurrence 身份。
    let prefix_end = match initializer.checked_sub(1).and_then(|declaration| {
        batched_initializer(run[declaration], run[initializer], facts)
            .map(|(_, width)| (declaration, width))
    }) {
        Some((declaration, width)) if width == frame.initializers.len() => declaration,
        Some(_) => return None,
        None => {
            // 只有部分控制值因后续同槽捕获被提升为 Local 时，其余结果仍是 Temp。
            // 三个原结果已在上方核对；这里仅消费这次初始化紧邻的合成空声明。
            initializer
                .checked_sub(1)
                .filter(|&index| {
                    matches!(run[index], HirStmt::LocalDecl(decl)
                    if decl.values.is_empty()
                        && decl.initializer_merge_transaction.is_none()
                        && !decl.bindings.is_empty()
                        && decl.bindings.iter().all(|local|
                            assign.targets.contains(&HirLValue::Local(*local))))
                })
                .unwrap_or(initializer)
        }
    };
    let prefix_run = &run[..prefix_end];
    let mut builder = frame_builder(context, prefix_run, facts, dialect, base.slot())?;
    if dialect == DecompileDialect::Luau {
        // Luau 在初始化表达式前预留 iterator/state/control；表的数组缓冲从
        // 整个协议槽组之后开始，不一定紧邻 table 参数槽。
        builder.declaration_reserved_top = Some(base.slot() + frame.initializers.len());
    }
    let call = builder.call(
        call,
        prefix_run.len(),
        base.slot(),
        true,
        CallWidth::Fixed(frame.initializers.len()),
    )?;
    if builder.first_event.is_some() && builder.next_event != prefix_run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: builder.first_event.unwrap_or(prefix_end),
        sink: run.len(),
        base,
        values: HirValuePack {
            fixed: Vec::new(),
            tail: Some(HirPackTail::open(HirExpr::Call(Box::new(call)))),
        },
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 相邻空声明与首个表达式写共同形成 initializer；值树仍由完整帧核对原输入与结果槽。
fn split_expression_initializer<'a>(
    previous: &'a HirStmt,
    stmt: &HirStmt,
) -> Option<&'a HirLocalDecl> {
    let (HirStmt::LocalDecl(decl), HirStmt::Assign(assign)) = (previous, stmt) else {
        return None;
    };
    let [local] = decl.bindings.as_slice() else {
        return None;
    };
    (decl.values.is_empty()
        && decl.initializer_merge_transaction.is_none()
        && assign.initializer_merge_transaction.is_none()
        && assign.generic_for_initializer_producer.is_none()
        && assign.generic_for_dispatch_release.is_none()
        && assign.method_rewrite_transaction.is_none()
        && assign.targets.as_slice() == [HirLValue::Local(*local)]
        && assign.values.tail.is_none()
        && match assign.values.fixed.as_slice() {
            [HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)] => true,
            [HirExpr::Binary(binary)] => {
                use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
                matches!(binary.op, Eq | Lt | Le | Gt | Ge)
            }
            _ => false,
        })
    .then_some(decl)
}

/// 同一固定结果包可混合新声明与复用绑定；这里只核对当前左值和原结果 Def。
/// 复用绑定能否重新声明由整批 preview 的缺失 epoch 决定，不能在此仅凭槽位合并。
fn batched_initializer<'a>(
    previous: &HirStmt,
    stmt: &'a HirStmt,
    facts: &ProtoPromotionFacts,
) -> Option<(&'a HirCallExpr, usize)> {
    let (HirStmt::LocalDecl(decl), HirStmt::Assign(assign)) = (previous, stmt) else {
        return None;
    };
    let width = assign.targets.len();
    let complete = decl.bindings.len() == width;
    let declared = decl.bindings.iter().copied().collect::<BTreeSet<_>>();
    if !decl.values.is_empty()
        || decl.bindings.is_empty()
        || width < 2
        || decl.bindings.len() > width
        || (complete && decl.initializer_merge_transaction.is_none())
        || assign.initializer_merge_transaction != decl.initializer_merge_transaction
        || (!complete && decl.initializer_merge_transaction.is_some())
        || assign.generic_for_dispatch_release.is_some()
        || assign.method_rewrite_transaction.is_some()
        || !assign
            .targets
            .iter()
            .filter_map(|target| match target {
                HirLValue::Local(local) if declared.contains(local) => Some(local),
                _ => None,
            })
            .eq(decl.bindings.iter())
        || !assign.values.fixed.is_empty()
    {
        return None;
    }
    let tail = assign.values.tail.as_ref()?;
    let HirExpr::Call(call) = tail.as_expr() else {
        return None;
    };
    let frame = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))?;
    if tail.exact_width() != Some(width)
        || frame.results
            != Some(ResultPack::Fixed(crate::transformer::RegRange {
                start: crate::transformer::Reg(frame.home.slot()),
                len: width,
            }))
        || !assign.targets.iter().enumerate().all(|(index, target)| {
            let HirLValue::Local(local) = target else {
                return false;
            };
            facts.fixed_call_result(call, index).is_some_and(|result| {
                // 当前赋值已经绑定本次结果身份；全局 Temp→Local 合并表
                // 可能指向后续写回的 owner，不能替代这次初始化的明确左值。
                facts.trusted_temp_home_slot(result).is_some_and(|home| {
                    home.slot() == frame.home.slot() + index
                        && facts.trusted_local_home_slot(*local) == Some(home)
                })
            })
        })
    {
        return None;
    }
    Some((call, width))
}

/// 当前左值逐项承接原固定 CALL 结果；是否可把先前准备声明改为结果声明由整帧 preview 决定。
fn call_result_bindings(
    assign: &crate::hir::common::HirAssign,
    facts: &ProtoPromotionFacts,
) -> Option<Vec<LocalId>> {
    let width = assign.targets.len();
    if width < 2
        || !assign.values.fixed.is_empty()
        || assign.is_phi_transfer
        || assign.initializer_merge_transaction.is_some()
        || assign.generic_for_initializer_producer.is_some()
        || assign.generic_for_dispatch_release.is_some()
        || assign.method_rewrite_transaction.is_some()
    {
        return None;
    }
    let tail = assign.values.tail.as_ref()?;
    if tail.exact_width() != Some(width) {
        return None;
    }
    let HirExpr::Call(call) = tail.as_expr() else {
        return None;
    };
    let frame = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))?;
    if !matches!(frame.results, Some(ResultPack::Fixed(pack))
        if pack.start.index() == frame.home.slot() && pack.len == width)
    {
        return None;
    }
    assign
        .targets
        .iter()
        .enumerate()
        .map(|(index, target)| {
            let HirLValue::Local(local) = target else {
                return None;
            };
            let home = facts.trusted_temp_home_slot(facts.fixed_call_result(call, index)?)?;
            (home.slot() == frame.home.slot() + index
                && facts.trusted_local_home_slot(*local) == Some(home))
            .then_some(*local)
        })
        .collect()
}

/// 连续两项比较先各写原 Boolean 槽，再逆序提交上值；两侧准备与声明一起验证，
/// 不把第一次上值更新提前到第二次比较可能触发的元方法之前。
fn parallel_upvalue_comparisons(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    first: FlatStmt<'_>,
    second: FlatStmt<'_>,
    last: FlatStmt<'_>,
) -> Option<Plan> {
    if matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) {
        return None;
    }
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let ([local], [left], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let (HirStmt::Assign(right_write), HirStmt::Assign(left_write)) = (second.stmt, last.stmt)
    else {
        return None;
    };
    let ([left_target @ HirLValue::Upvalue(_)], [HirExpr::LocalRef(read)], None) = (
        left_write.targets.as_slice(),
        left_write.values.fixed.as_slice(),
        &left_write.values.tail,
    ) else {
        return None;
    };
    let ([right_target @ HirLValue::Upvalue(_)], [right], None) = (
        right_write.targets.as_slice(),
        right_write.values.fixed.as_slice(),
        &right_write.values.tail,
    ) else {
        return None;
    };
    if read != local
        || decl.initializer_merge_transaction.is_some()
        || [left_write, right_write].iter().any(|assign| {
            assign.is_phi_transfer
                || assign.initializer_merge_transaction.is_some()
                || assign.generic_for_initializer_producer.is_some()
                || assign.generic_for_dispatch_release.is_some()
                || assign.method_rewrite_transaction.is_some()
        })
    {
        return None;
    }
    let result = |mut value: &HirExpr| {
        while let HirExpr::Unary(unary) = value
            && unary.source_site.is_none()
            && unary.op == crate::hir::common::HirUnaryOpKind::Not
        {
            value = &unary.expr;
        }
        let HirExpr::Binary(binary) = value else {
            return None;
        };
        facts.comparison_result_temp(binary)
    };
    let left_result = result(left)?;
    let right_result = result(right)?;
    let base = facts.trusted_temp_home_slot(left_result)?;
    let right_home = facts.trusted_temp_home_slot(right_result)?;
    if facts.promoted_local_for_temp(left_result) != Some(*local)
        || facts.trusted_local_home_slot(*local) != Some(base)
        || right_home.slot() != base.slot() + 1
        || [left_result, right_result].iter().any(|&temp| {
            facts
                .complete_temp_definition_write_homes(temp)
                .iter()
                .copied()
                .ne(facts.trusted_temp_home_slot(temp))
        })
    {
        return None;
    }
    let run = [first.stmt];
    let mut builder = frame_builder(context, &run, facts, dialect, base.slot())?;
    let left = builder.expr(
        &HirExpr::LocalRef(*local),
        1,
        base.slot(),
        None,
        false,
        true,
        Some(left_result),
    )?;
    let right = builder.expr(
        right,
        1,
        right_home.slot(),
        None,
        false,
        true,
        Some(right_result),
    )?;
    if builder.first_event != Some(0) || builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: last.id,
        base,
        values: vec![left, right].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![left_target.clone(), right_target.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![second.id],
        removed: vec![first.id, second.id],
    })
}

/// 原高槽快照及两次低槽写回合成并行交换，保持 Lua 编译器的相同 MOVE 顺序。
fn swap_assignment_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    frames: &BTreeMap<LocalId, Option<(LocalId, LocalId, HomeSlotKey)>>,
    first: FlatStmt<'_>,
    second: FlatStmt<'_>,
    last: FlatStmt<'_>,
) -> Option<Plan> {
    let HirStmt::LocalDecl(decl) = first.stmt else {
        return None;
    };
    let ([snapshot], [HirExpr::LocalRef(source)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let &(left, right, home) = frames.get(snapshot)?.as_ref()?;
    if *source != right
        || left == right
        || [left, right].contains(snapshot)
        || decl.initializer_merge_transaction.is_some()
    {
        return None;
    }
    for local in [*snapshot, left, right] {
        let local_home = facts.trusted_local_home_slot(local)?;
        if context.barred.contains(&local_home)
            || context.closed.contains(&local_home)
            || (local == *snapshot
                && (context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some()
                    || context
                        .proto
                        .inline_dispositions
                        .local(local)
                        .must_preserve()))
        {
            // SemanticBarrier:Capture/DebugScope：目标的原写序不变，其 debug 身份仍保留；
            // 只有被删除的高槽快照不能拥有独立源码身份。
            return None;
        }
    }
    let copy = |stmt: &HirStmt, target, source| {
        matches!(stmt, HirStmt::Assign(assign)
            if assign.targets.as_slice() == [HirLValue::Local(target)]
                && assign.values.fixed.as_slice() == [HirExpr::LocalRef(source)]
                && assign.values.tail.is_none()
                && assign.initializer_merge_transaction.is_none()
                && assign.generic_for_initializer_producer.is_none()
                && assign.generic_for_dispatch_release.is_none()
                && assign.method_rewrite_transaction.is_none())
    };
    if !copy(second.stmt, right, left) || !copy(last.stmt, left, *snapshot) {
        return None;
    }
    // 原 Def 已证明 snapshot 只被末次 MOVE 读取；当前后缀仍由 preview 检查。
    // 前缀必须精确结束于原高槽，不能让并行 RHS 因删除声明而换到另一物理位置。
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: last.id,
        base: home,
        values: vec![HirExpr::LocalRef(right), HirExpr::LocalRef(left)].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![HirLValue::Local(left), HirLValue::Local(right)],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: vec![second.id],
        removed: vec![first.id, second.id],
    })
}

/// `a,b=f(),9` 的 CALL、标量写和结果 COPY 共同恢复；先在原 scratch 求值，再按
/// 原顺序写回两项。参数是已存在的低槽绑定，不为它创建 Local 占位或改写返回身份。
/// 三个原 Def 由 Promotion 签证；这里只匹配当前树并复用完整帧/声明后缀事务。
fn scalar_assignment_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    scalar: &HirStmt,
    copy: &HirStmt,
) -> Option<Plan> {
    let (source, HirExpr::Call(call)) = scalar_local(run.last()?)? else {
        return None;
    };
    let frame = facts.native_call_frame(call)?;
    let assignment = facts.native_scalar_assignment(call)?;
    let (HirStmt::Assign(scalar), HirStmt::Assign(copy)) = (scalar, copy) else {
        return None;
    };
    let ([scalar_target], [value], None) = (
        scalar.targets.as_slice(),
        scalar.values.fixed.as_slice(),
        &scalar.values.tail,
    ) else {
        return None;
    };
    let ([target], [HirExpr::LocalRef(read)], None) = (
        copy.targets.as_slice(),
        copy.values.fixed.as_slice(),
        &copy.values.tail,
    ) else {
        return None;
    };
    let home = |target: &HirLValue| match target {
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local),
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param),
        _ => None,
    };
    if *read != source
        || facts.promoted_local_for_temp(assignment.result) != Some(source)
        || facts.trusted_local_home_slot(source) != Some(frame.home)
        || home(scalar_target) != Some(assignment.scalar_home)
        || home(target) != Some(assignment.target_home)
        || !assignment.value.matches_hir_expr(value)
        || [assignment.scalar_home, assignment.target_home]
            .iter()
            .any(|home| context.barred.contains(home) || context.closed.contains(home))
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    builder.result_move = Some((
        source,
        run.len() - 1,
        BTreeSet::from([assignment.target_home]),
    ));
    let call = builder.expr(
        &HirExpr::LocalRef(source),
        run.len(),
        frame.home.slot(),
        None,
        false,
        true,
        None,
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: 0,
        base: frame.home,
        values: vec![call, value.clone()].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![target.clone(), scalar_target.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 低槽、上值与表字段写共用单结果 CALL 帧。寄存器 base 必须保持原低槽身份；
/// PUC SETTABUP 则在 CALL 后直接读取原上值 cell，不提前快照可被 CALL 改写的 base。
fn call_assignment_targets(
    target: &HirLValue,
    result: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    constants_fit_rk: bool,
    barred: &BTreeSet<HomeSlotKey>,
) -> Option<Vec<LocalId>> {
    match target {
        HirLValue::Local(local) => facts
            .trusted_local_home_slot(*local)
            .filter(|home| home.slot() < result.slot())
            .map(|_| vec![*local]),
        HirLValue::Param(param) => facts
            .trusted_param_home_slot(*param)
            .filter(|home| home.slot() < result.slot())
            .map(|_| Vec::new()),
        // SETUPVAL 在 CALL 完成后直接消费原结果槽，不准备寄存器左值。
        // 结果 Def、全部 COPY 写域与后继复用仍由同一 builder/preview 验证。
        HirLValue::Upvalue(_) => Some(Vec::new()),
        HirLValue::Global(global)
            if constants_fit_rk
                && facts.global_write_value_home(global, dialect) == Some(result) =>
        {
            // 原环境写没有左值准备槽；CALL/FASTCALL 在原 freereg 完成后再写入。
            Some(Vec::new())
        }
        HirLValue::TableAccess(access)
            if constants_fit_rk
                && !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
        {
            if let HirExpr::UpvalueRef(base) = access.base {
                // 候选拒绝[TargetConstraint]：只有 PUC5.2+ 原 SETTABUP 可无 base 临时槽；
                // 动态 key 仍需独立准备协议，不能按当前字面量形状忽略原 key 槽。
                if !matches!(
                    dialect,
                    DecompileDialect::Lua52
                        | DecompileDialect::Lua53
                        | DecompileDialect::Lua54
                        | DecompileDialect::Lua55
                ) {
                    return None;
                }
                let layout = facts.native_upvalue_table_write_layout(access)?;
                return (base == layout.base
                    && layout.key.is_none()
                    && layout.value == Some(result)
                    && matches!(
                        access.key,
                        HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                    ))
                .then(Vec::new);
            }
            let layout = facts.native_table_write_layout(access)?;
            let base = match &access.base {
                HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                _ => None,
            }?;
            (base == layout.base
                && base.slot() < result.slot()
                && !barred.contains(&base)
                && layout.key.is_none()
                && layout.value == Some(result)
                && matches!(
                    access.key,
                    HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                ))
            .then(Vec::new)
        }
        _ => None,
    }
}

/// 多结果赋值先在空闲区返回，再按目标 VM 的 MOVE 顺序写入现存低槽。消费的是这次
/// 返回值版本；同 Local 的后续独立写仍由 apply_preview 的 missing 事务重声明。
#[expect(
    clippy::too_many_arguments,
    reason = "复用当前批次的原槽、身份和词法快照"
)]
fn multi_result_assignment(
    proto: &HirProto,
    flat: &[Option<FlatStmt<'_>>],
    initializer: usize,
    width: usize,
    base: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
) -> Option<(usize, Vec<HirLValue>)> {
    let (sources, values) = match flat[initializer]?.stmt {
        HirStmt::Assign(assign) => {
            let HirExpr::Call(call) = assign.values.tail.as_ref()?.as_expr() else {
                return None;
            };
            if let Some((end, targets)) = phi_result_assignment(
                proto,
                flat,
                initializer,
                assign,
                call,
                base,
                facts,
                dialect,
                barred,
                closed,
            ) {
                return Some((end, targets.into_iter().map(HirLValue::Local).collect()));
            }
            (
                assign
                    .targets
                    .iter()
                    .map(|target| match target {
                        HirLValue::Local(local) => Some(*local),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?,
                &assign.values,
            )
        }
        HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none() => {
            (decl.bindings.clone(), &decl.values)
        }
        _ => return None,
    };
    let HirExpr::Call(call) = values.tail.as_ref()?.as_expr() else {
        return None;
    };
    if sources.len() != width {
        return None;
    }
    let mut table_bases = BTreeSet::new();
    let end = initializer + width;
    let copies = flat.get(initializer + 1..=end)?;
    let mut targets = Vec::with_capacity(width);
    let mut unique = BTreeSet::new();
    for (offset, entry) in copies.iter().enumerate() {
        // PUC/JIT 从末项回写，Luau 从首项回写；保持原顺序，不能按无副作用猜测交换。
        let result_index = if dialect == DecompileDialect::Luau {
            offset
        } else {
            width - offset - 1
        };
        let source = &sources[result_index];
        let entry = (*entry)?;
        if entry.id != flat[initializer]?.id + offset + 1 {
            return None;
        }
        let HirStmt::Assign(copy) = entry.stmt else {
            return None;
        };
        let ([target], [HirExpr::LocalRef(read)], None) = (
            copy.targets.as_slice(),
            copy.values.fixed.as_slice(),
            &copy.values.tail,
        ) else {
            return None;
        };
        let result = facts.fixed_call_result(call, result_index)?;
        let home = facts.trusted_temp_home_slot(result)?;
        let target_home = match target {
            HirLValue::Local(local) => {
                let home = facts.trusted_local_home_slot(*local)?;
                if home.slot() >= base.slot() || !unique.insert(*local) {
                    return None;
                }
                Some(home)
            }
            HirLValue::TableAccess(access)
                if !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
            {
                let layout = facts.native_table_write_layout(access)?;
                let owner = match access.base {
                    HirExpr::ParamRef(param) => facts.trusted_param_home_slot(param)?,
                    HirExpr::LocalRef(local) => {
                        table_bases.insert(local);
                        facts.trusted_local_home_slot(local)?
                    }
                    _ => return None,
                };
                if owner != layout.base
                    || owner.slot() >= base.slot()
                    || layout.key.is_some()
                    || layout.value != Some(home)
                    || !super::tables::literal_rk(&access.key)
                {
                    return None;
                }
                None
            }
            _ => return None,
        };
        // 同一 Local 后续可以承接另一组 CALL 结果，其写回目标不属于本次事务。
        // 原固定结果 Def 保留这次 MOVE 写域；后续版本仍由 preview 重新声明并核对。
        let writes = facts.complete_temp_definition_write_homes(result);
        // 捕获集合覆盖整个 proto；未来在结果槽创建的 cell 不能回溯到本次 CALL。
        // 结果 home 需要当时未捕获的证明；低槽目标即使被捕获也在原 CALL 后
        // 按同一顺序接收结果，不能把原写回误当作被消费的捕获根。CLOSE 边界不变。
        if source != read
            || facts.trusted_local_home_slot(*source) != Some(home)
            || home.slot() != base.slot() + result_index
            || proto.local_debug_hints[source.index()].is_some()
            || proto.local_debug_scopes[source.index()].is_some()
            || proto.inline_dispositions.local(*source).must_preserve()
            || writes.iter().any(|write| {
                barred.contains(write)
                    && Some(*write) != target_home
                    && (*write != home
                        || !facts
                            .native_call_layout(call)
                            .is_some_and(|layout| layout.fixed_results_unaliased))
            })
            || !writes.is_disjoint(closed)
            || writes
                .iter()
                .any(|write| *write != home && Some(*write) != target_home)
        {
            return None;
        }
        targets.push(target.clone());
    }
    if !table_bases.is_disjoint(&unique) {
        return None;
    }
    if dialect != DecompileDialect::Luau {
        targets.reverse();
    }
    Some((end, targets))
}

/// 原 MOVE 的剩余 Temp 写与合流转移共同交给完整 CALL 事务；没有原写回序列时不猜。
#[expect(
    clippy::too_many_arguments,
    reason = "沿用当前 CALL 事务的完整证明上下文"
)]
fn phi_result_assignment(
    proto: &HirProto,
    flat: &[Option<FlatStmt<'_>>],
    initializer: usize,
    assign: &crate::hir::common::HirAssign,
    call: &HirCallExpr,
    base: HomeSlotKey,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
    closed: &BTreeSet<HomeSlotKey>,
) -> Option<(usize, Vec<LocalId>)> {
    let writes = facts.native_result_writebacks(call)?;
    let width = assign.targets.len();
    if writes.len() != width {
        return None;
    }
    let sources = assign
        .targets
        .iter()
        .map(|target| match target {
            HirLValue::Local(local) => Some(*local),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    for (offset, write) in writes.iter().enumerate() {
        let expected = if dialect == DecompileDialect::Luau {
            offset
        } else {
            width - offset - 1
        };
        if write.result_index != expected {
            return None;
        }
    }
    let mut end = initializer + 1;
    // 至多一组原写回；不会逐候选扫描整个后缀。
    for write in writes {
        let entry = flat.get(end).copied().flatten()?;
        let HirStmt::Assign(copy) = entry.stmt else {
            return None;
        };
        if copy.is_phi_transfer {
            break;
        }
        if entry.id != flat[initializer]?.id + end - initializer
            || proto.temp_debug_locals[write.writeback.index()].is_some()
            || proto.temp_debug_scopes[write.writeback.index()].is_some()
            || copy.initializer_merge_transaction.is_some()
            || copy.generic_for_initializer_producer.is_some()
            || copy.generic_for_dispatch_release.is_some()
            || copy.method_rewrite_transaction.is_some()
            || !matches!((copy.targets.as_slice(), copy.values.fixed.as_slice(), &copy.values.tail),
                ([HirLValue::Temp(target)], [HirExpr::LocalRef(source)], None)
                    if *target == write.writeback && *source == sources[write.result_index])
        {
            return None;
        }
        end += 1;
    }
    let entry = flat.get(end).copied().flatten()?;
    let HirStmt::Assign(phi) = entry.stmt else {
        return None;
    };
    if !phi.is_phi_transfer
        || phi.initializer_merge_transaction.is_some()
        || phi.generic_for_initializer_producer.is_some()
        || phi.generic_for_dispatch_release.is_some()
        || phi.method_rewrite_transaction.is_some()
        || phi.targets.len() != width
        || phi.values.fixed.len() != width
        || phi.values.tail.is_some()
        || entry.id != flat[initializer]?.id + end - initializer
    {
        return None;
    }
    let mut targets = vec![None; width];
    let mut homes = BTreeMap::new();
    for write in writes {
        homes.insert(write.target_home, write.result_index);
    }
    for (target, value) in phi.targets.iter().zip(&phi.values.fixed) {
        let (HirLValue::Local(target), HirExpr::LocalRef(source)) = (target, value) else {
            return None;
        };
        let target_home = facts.trusted_local_home_slot(*target)?;
        let result_index = *homes.get(&target_home)?;
        let result = facts.fixed_call_result(call, result_index)?;
        let home = facts.trusted_temp_home_slot(result)?;
        let writes = facts.complete_temp_definition_write_homes(result);
        if *source != sources[result_index]
            || home.slot() != base.slot() + result_index
            || facts.trusted_local_home_slot(*source) != Some(home)
            || targets[result_index].replace(*target).is_some()
            || proto.local_debug_hints[source.index()].is_some()
            || proto.local_debug_scopes[source.index()].is_some()
            || proto.inline_dispositions.local(*source).must_preserve()
            || !writes.is_disjoint(barred)
            || !writes.is_disjoint(closed)
            || writes
                .iter()
                .any(|write| *write != home && *write != target_home)
        {
            return None;
        }
    }
    Some((end, targets.into_iter().collect::<Option<Vec<_>>>()?))
}

#[derive(Clone, Copy)]
struct FlatStmt<'a> {
    id: usize,
    stmt: &'a HirStmt,
}

/// 单次逆序归并后续原求值帧的最低槽：结果低于整个后续帧时才独立恢复初始化。
/// 不能提前冻结 `print(make(), other())` 的高槽 make 结果，否则会抬高 print 的 caller top。
/// CONCAT/RETURN 同样拥有准备区，不能先把其中的 CALL 结果固化为永久声明。
#[derive(Clone, Copy, Default)]
struct FollowingFrameFloor {
    all: Option<usize>,
    original_calls: Option<usize>,
}

fn following_frame_floors(
    flat: &[Option<FlatStmt<'_>>],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Vec<FollowingFrameFloor> {
    use crate::hir::visit::HirVisitor;
    struct Calls<'a> {
        facts: &'a ProtoPromotionFacts,
        dialect: DecompileDialect,
        floor: FollowingFrameFloor,
    }
    impl HirVisitor<'_> for Calls<'_> {
        fn visit_lvalue(&mut self, value: &HirLValue) {
            if let HirLValue::TableAccess(access) = value
                && matches!(access.base, HirExpr::GlobalRef(_))
                && let Some((_, home)) = self
                    .facts
                    .table_write_base_preparation(access, &access.base)
            {
                // 全局表字段写先在 scratch 读取目标；低槽 CALL 结果在此仍是
                // 已有值，不属于字段写的准备区。发布原 base Def 的槽边界，
                // 避免把前一个方法结果和 receiver 永久拆成两个声明。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            if let HirLValue::Global(global) = value
                && let Some(home) = self.facts.global_write_value_home(global, self.dialect)
            {
                // 环境写也有原 RHS 准备槽；即使 RHS 已合并为 nil，仍可界定
                // 前一个更低槽 CALL 的独立结果，不把它误留在 callee 准备声明中。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
        }

        fn visit_expr(&mut self, expr: &HirExpr) {
            if let HirExpr::Binary(binary) = expr
                && let Some(result) = self.facts.comparison_result_temp(binary)
                && let Some(home) = self.facts.trusted_temp_home_slot(result)
            {
                // 比较的 Boolean 结果也是完整 initializer 的入口。忽略它会把
                // 同槽 CALL 提前冻结为独立声明，并切断尚待恢复的操作数准备区。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            if let HirExpr::Unary(unary) = expr
                && unary.op == crate::hir::common::HirUnaryOpKind::Neg
                && let Some(home) = self.facts.unary_operand_home(unary)
            {
                // CALL 已树化为取负的输入时，原操作数槽仍属于后继完整表达式。
                // 不能只看到更晚 assert 的高槽，就提前冻结这个 CALL 结果声明。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            if let HirExpr::Binary(binary) = expr
                && binary.op == crate::hir::common::HirBinaryOpKind::Concat
                && let Some(buffer) = self.facts.native_concat_buffer(binary)
            {
                let slot = buffer.start.index();
                self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            }
        }

        fn visit_stmt(&mut self, stmt: &HirStmt) {
            if let HirStmt::Assign(assign) = stmt
                && let (
                    [HirLValue::Upvalue(_) | HirLValue::Global(_)],
                    [HirExpr::Binary(binary)],
                    None,
                ) = (
                    assign.targets.as_slice(),
                    assign.values.fixed.as_slice(),
                    &assign.values.tail,
                )
                && let Some(home) = binary
                    .source_site
                    .and_then(|source| self.facts.operation_result_home(source))
            {
                // SETUPVAL 的完整算术/CONCAT RHS 同样拥有准备入口，内部短路
                // 不能先冻结独立声明并截断左操作数的读取。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            if let Some((local, HirExpr::Closure(closure))) = scalar_local(stmt)
                && let Some(site) = closure.source_site
                && (matches!(stmt, HirStmt::LocalDecl(_))
                    || self
                        .facts
                        .operation_result_temp(site)
                        .is_some_and(|temp| self.facts.temp_requires_call_frame(temp)))
                && let Some(home) = self.facts.operation_result_home(site)
                && self.facts.trusted_local_home_slot(local) == Some(home)
            {
                // 原独立 CLOSURE 声明或 Promotion 保留的低槽 callee 前缀可
                // 复用旧结果槽。字段闭包仍属于构造器事务，不能单凭同槽赋值
                // 就截断它的准备区；否则 FASTCALL 参数会被逐轮新增声明。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            let lookup = scalar_local(stmt)
                .and_then(|(local, value)| {
                    let HirExpr::TableAccess(access) = value else {
                        return None;
                    };
                    Some((self.facts.trusted_local_home_slot(local)?, access.as_ref()))
                })
                .or_else(|| {
                    let HirStmt::Assign(assign) = stmt else {
                        return None;
                    };
                    let ([HirLValue::Param(param)], [HirExpr::TableAccess(access)], None) = (
                        assign.targets.as_slice(),
                        assign.values.fixed.as_slice(),
                        &assign.values.tail,
                    ) else {
                        return None;
                    };
                    Some((self.facts.trusted_param_home_slot(*param)?, access.as_ref()))
                });
            if let Some((home, access)) = lookup
                && self.facts.table_read_result_home(access) == Some(home)
            {
                // 循环前保存的字段快照也拥有独立结果槽。更低槽的 CALL 可以完成
                // 自己的初始化，不必等待循环边界之外的调用；快照和循环仍留在原处。
                // 写回参数也结束该 RHS；不能只看其高槽 key CALL 而冻结前一个结果。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(home.slot(), |old| old.min(home.slot())),
                );
            }
            // 空 RETURN 没有返回值准备区；其原清理事务不在这里改写。
            if let HirStmt::Return(ret) = stmt
                && !ret.values.is_empty()
                && let Some(frame) = self.facts.native_return_frame(ret)
            {
                let slot = frame.home.slot();
                self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            }
            if let HirStmt::GenericFor(for_) = stmt
                && let Some(frame) = self.facts.generic_for_body_frame(for_)
                && let Some(base) = frame.initializers.first()
            {
                // 迭代器调用的索引准备属于整个控制帧；不能把高槽 base
                // 先固定成独立声明，使随后循环头无法消费同一准备区。
                self.floor.all = Some(
                    self.floor
                        .all
                        .map_or(base.slot(), |old| old.min(base.slot())),
                );
            }
        }

        fn visit_call(&mut self, call: &HirCallExpr) {
            // 后继 FASTCALL 同样拥有原帧；布局已证明时不把它当成未知零下界。
            // 此查询只决定候选边界，builtin、准备顺序及删除仍由 FASTCALL builder 核对。
            let slot = self
                .facts
                .native_call_layout(call)
                .map(|frame| frame.home.slot())
                .or_else(|| {
                    self.facts
                        .native_fastcall_frame(call)
                        .map(|frame| frame.home.slot())
                })
                .unwrap_or(0);
            self.floor.all = Some(self.floor.all.map_or(slot, |old| old.min(slot)));
            // 合成 factory 调用没有原 CALL 参数区；不据它猜原 buffer 布局。
            // 有原来源但缺布局的调用仍以零下界阻断独立原 initializer 恢复。
            if call.source_site.is_some() {
                self.floor.original_calls =
                    Some(self.floor.original_calls.map_or(slot, |old| old.min(slot)));
            }
        }
    }
    let mut result = vec![FollowingFrameFloor::default(); flat.len()];
    let mut calls = Calls {
        facts,
        dialect,
        floor: FollowingFrameFloor::default(),
    };
    for (index, entry) in flat.iter().enumerate().rev() {
        let Some(entry) = entry else {
            calls.floor = FollowingFrameFloor::default();
            continue;
        };
        result[index] = calls.floor;
        if matches!(entry.stmt, HirStmt::LocalRootRelease(_)) {
            // 根退出标记没有独立求值，不能截断后继 CALL/CONCAT 的准备区；
            // 否则参数会先被冻结为 local，完整调用帧再也无法消费它。
            continue;
        }
        if flat
            .get(index + 1)
            .and_then(Option::as_ref)
            .is_some_and(|next| {
                batched_initializer(entry.stmt, next.stmt, facts).is_some()
                    || split_expression_initializer(entry.stmt, next.stmt).is_some()
            })
        {
            // 多结果初始化事务的空声明没有独立求值；原 CALL 帧已由紧邻赋值发布，
            // 不能在这里抹掉它，让前一个低槽 CALL 失去独立初始化的边界证明。
            continue;
        }
        if let HirStmt::NumericFor(for_) = entry.stmt
            && let Some(base) = numeric_header_base(for_, dialect)
        {
            // 三个 header 值属于同一个准备区，不能先把较低槽 CALL 固定为源码 local。
            calls.floor = FollowingFrameFloor {
                all: Some(base.slot()),
                original_calls: Some(base.slot()),
            };
            continue;
        }
        if let HirStmt::Assign(assign) = entry.stmt
            && let ([HirLValue::Global(global)], [value], None) = (
                assign.targets.as_slice(),
                assign.values.fixed.as_slice(),
                &assign.values.tail,
            )
            && tables::literal_rk(value)
            && facts.global_write_has_no_preparation(global, dialect)
        {
            // RK 环境写不占准备槽，不应抹掉后继帧下界。写入本身仍原位保留，
            // 元方法可能观察的低槽前缀继续由整批 preview 验证。
            continue;
        }
        // SETLIST 是构造器的缓冲提交，后继 CALL 仍拥有该准备区；
        // 不把它当控制边界抹掉外层帧下界，批次输入仍由完整构造事务验证。
        if let HirStmt::TableSetList(batch) = entry.stmt
            && let Some(layout) = facts.native_table_batch_layout(batch)
        {
            calls.floor.all = Some(
                calls
                    .floor
                    .all
                    .map_or(layout.base.slot(), |old| old.min(layout.base.slot())),
            );
            crate::hir::visit::visit_stmt_header(entry.stmt, &mut calls);
            continue;
        }
        if scalar_local(entry.stmt).is_none() {
            calls.floor = FollowingFrameFloor::default();
            if !matches!(
                entry.stmt,
                HirStmt::CallStmt(_)
                    | HirStmt::Return(_)
                    | HirStmt::LocalDecl(_)
                    | HirStmt::Assign(_)
                    | HirStmt::GenericFor(_)
            ) {
                continue;
            }
        }
        crate::hir::visit::visit_stmt_header(entry.stmt, &mut calls);
    }
    result
}

/// 直线后缀内，字段写的 RHS 在下一次覆盖前仍被读取的终点。边界外留给整批 preview，
/// 每个表达式只访问常数次，不为各个 SETTABLE 重扫后缀。
fn live_indexed_results(flat: &[Option<FlatStmt<'_>>]) -> BTreeSet<usize> {
    let mut live = BTreeSet::new();
    let mut results = BTreeSet::new();
    for (index, entry) in flat.iter().enumerate().rev() {
        let Some(entry) = entry else {
            live.clear();
            continue;
        };
        if let HirStmt::Assign(assign) = entry.stmt
            && indexed::is_candidate(assign)
            && let [HirExpr::LocalRef(local)] = assign.values.fixed.as_slice()
            && live.contains(local)
        {
            results.insert(index);
        }
        crate::hir::visit::visit_stmt_header(
            entry.stmt,
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    live.remove(&local);
                }
            }),
        );
        crate::hir::visit::visit_stmt_header(
            entry.stmt,
            &mut BindingReadCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    live.insert(local);
                }
            }),
        );
    }
    results
}

fn flatten_scope<'a>(
    block: &'a HirBlock,
    cursor: &mut usize,
    output: &mut Vec<Option<FlatStmt<'a>>>,
) {
    prefix::coordinates::visit(block, cursor, &mut |id, kind, stmt| match (kind, stmt) {
        (PointKind::Boundary, _) | (PointKind::Statement, HirStmt::Repeat(_)) => output.push(None),
        (PointKind::Statement, HirStmt::Block(_)) => {}
        (PointKind::Statement, HirStmt::While(_)) => {
            output.push(None);
            output.push(Some(FlatStmt { id, stmt }));
            output.push(None);
        }
        (PointKind::Statement, HirStmt::NumericFor(_)) => {
            output.push(Some(FlatStmt { id, stmt }));
            output.push(None);
        }
        _ => output.push(Some(FlatStmt { id, stmt })),
    });
}

/// 多个谓词共享的索引结果在条件入口完成初始化，保留实际结果绑定。
fn shared_condition_initializer(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
) -> Option<Plan> {
    let sink = run
        .iter()
        .rposition(|stmt| !matches!(stmt, HirStmt::LocalRootRelease(_)))?;
    let (local, HirExpr::TableAccess(access)) = scalar_local(run[sink])? else {
        return None;
    };
    let mut reads = 0;
    crate::hir::visit::visit_expr(
        condition,
        &mut BindingReadCollector(|binding| {
            if binding == HirBinding::Local(local) {
                reads += 1;
            }
        }),
    );
    if reads < 2 {
        return None;
    }
    // 共享谓词需要一个实际结果绑定，不能把准备链复制进每个比较。
    // 仅重建该结果的 RHS；原槽、完整事件及旧身份后继仍由同一帧事务证明。
    lookup_initializer(
        context,
        &run[..sink],
        facts,
        dialect,
        Some(local),
        access,
        facts.trusted_local_home_slot(local)?,
    )
}

/// 只剥离结构恢复的极性包装；带原指令来源的 NOT 需要独立的物理写证明。
fn synthetic_not_subject(mut value: &HirExpr) -> (&HirExpr, usize) {
    let mut depth = 0;
    while let HirExpr::Unary(unary) = value
        && unary.op == crate::hir::common::HirUnaryOpKind::Not
        && unary.source_site.is_none()
    {
        value = &unary.expr;
        depth += 1;
    }
    (value, depth)
}

/// 条件前的 CALL/索引结果与准备链共同恢复，仍重发原单结果槽；
/// 分叉由扁平视图隔断，后继身份由整批 preview 核对。
fn condition_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
) -> Option<Plan> {
    let mut subject = condition;
    let mut depth = 0;
    let mut tails = Vec::new();
    loop {
        match subject {
            HirExpr::Unary(unary)
                if unary.op == crate::hir::HirUnaryOpKind::Not && unary.source_site.is_none() =>
            {
                subject = &unary.expr
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                tails.push(&logical.rhs);
                subject = &logical.lhs;
            }
            _ => break,
        }
        depth += 1;
    }
    if tails.is_empty() {
        return condition_leaf_plan(context, run, facts, dialect, condition);
    }
    let mut plan = condition_leaf_plan(context, run, facts, dialect, subject)?;
    // 首个谓词必达，后续仅测试已有低槽，既不覆盖 CALL 结果根也不插入求值。
    // 带调用、索引或原 NOT 写的尾部需要完整操作帧，不能借纯控制包装移动它们。
    if !tails
        .iter()
        .all(|tail| predicate_preserves_frame(context, facts, dialect, tail, plan.base))
    {
        return None;
    }
    let mut rebuilt = condition.clone();
    let mut destination = &mut rebuilt;
    for _ in 0..depth {
        destination = match destination {
            HirExpr::Unary(unary) => &mut unary.expr,
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => &mut logical.lhs,
            _ => unreachable!(),
        };
    }
    *destination = plan.values.fixed.pop()?;
    plan.values = vec![rebuilt].into();
    Some(plan)
}

fn predicate_reads_below(expr: &HirExpr, facts: &ProtoPromotionFacts, floor: usize) -> bool {
    !crate::hir::visit::any_expr(expr, &mut |expr| !match expr {
        HirExpr::LocalRef(local) => facts
            .trusted_local_home_slot(*local)
            .is_some_and(|home| home.slot() < floor),
        HirExpr::ParamRef(param) => facts
            .trusted_param_home_slot(*param)
            .is_some_and(|home| home.slot() < floor),
        HirExpr::Unary(unary) => {
            unary.op == crate::hir::HirUnaryOpKind::Not && unary.source_site.is_none()
        }
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => true,
        _ => false,
    })
}

fn condition_leaf_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
) -> Option<Plan> {
    let (subject, not_depth) = synthetic_not_subject(condition);
    let value = if let HirExpr::LocalRef(local) = subject {
        let (target, value) = scalar_local(run.last()?)?;
        if target != *local {
            return None;
        }
        value
    } else {
        subject
    };
    let (base, source) = match value {
        HirExpr::Call(call) => (facts.native_call_frame(call)?.home, call.source_site?),
        HirExpr::GlobalRef(global) if matches!(subject, HirExpr::LocalRef(_)) => {
            let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
                return None;
            };
            (facts.global_read_frame(global, dialect)?, source)
        }
        HirExpr::TableAccess(access) => {
            let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
                return None;
            };
            (facts.table_read_result_home(access)?, source)
        }
        _ => return comparison_plan(context, run, facts, dialect, condition),
    };
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let value = if matches!(subject, HirExpr::LocalRef(_)) {
        let indexed = matches!(value, HirExpr::TableAccess(_));
        // 索引条件也有独立结果槽；沿 register lookup 核对 base/key，不能仅凭
        // 字面键把读取视作无需重发的简单值。后续同槽写由整批 preview 共同退休。
        builder.register_operand = indexed;
        builder.expr(
            subject,
            run.len(),
            base.slot(),
            None,
            !indexed,
            indexed,
            Some(facts.operation_result_temp(source)?),
        )?
    } else if let HirExpr::TableAccess(access) = value {
        builder.register_lookup(access, run.len(), base.slot())?
    } else {
        let HirExpr::Call(call) = value else {
            return None;
        };
        HirExpr::Call(Box::new(builder.call(
            call,
            run.len(),
            base.slot(),
            true,
            CallWidth::Fixed(1),
        )?))
    };
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    // 只穿过结构恢复产生的极性/Boolean 包装；原生 NOT 仍由其操作数与结果帧证明。
    let mut rebuilt = condition.clone();
    let mut destination = &mut rebuilt;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = destination else {
            unreachable!()
        };
        destination = &mut unary.expr;
    }
    *destination = value;
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![rebuilt].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

fn numeric_header_base(
    for_: &crate::hir::common::HirNumericFor,
    dialect: DecompileDialect,
) -> Option<HomeSlotKey> {
    // Luau 的物理顺序是 limit/step/index，求值顺序仍为 start/limit/step。
    // JIT 的 FR2 帧隙由 FrameBuilder.call 消费，不改变三个控制值的槽序。
    let order = if dialect == DecompileDialect::Luau {
        [2, 0, 1]
    } else {
        [0, 1, 2]
    };
    let base = for_.control_homes[usize::from(dialect == DecompileDialect::Luau)];
    for_.control_homes
        .iter()
        .enumerate()
        // CLOSE 只改变曾被使用槽的 epoch；连续控制槽不必拥有相同 epoch。
        // 此处只核对布局，producer 的完整 home 由各控制值的帧证明消费。
        .all(|(offset, home)| home.slot() == base.slot() + order[offset])
        .then_some(base)
}

/// 比较头的两个准备按原 Def、原槽与事件顺序共同消费；CALL 结果仍作为原 scratch
/// 存活，不以“只读于条件”撤销根义务。后续声明身份与源码前缀由同批事务核对。
fn comparison_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
) -> Option<Plan> {
    let mut operand = condition;
    let mut not_depth = 0;
    while let HirExpr::Unary(unary) = operand
        && unary.op == crate::hir::common::HirUnaryOpKind::Not
    {
        operand = &unary.expr;
        not_depth += 1;
    }
    let HirExpr::Binary(binary) = operand else {
        return None;
    };
    if let Some(plan) =
        comparison_operation_plan(context, run, facts, dialect, condition, binary, not_depth)
    {
        return Some(plan);
    }
    if let Some(plan) =
        comparison_selected_read_plan(context, run, facts, dialect, condition, binary, not_depth)
    {
        return Some(plan);
    }
    let read_input = comparison_read_input(run, facts, dialect, binary);
    if read_input.is_none() && matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
    {
        return comparison_literal_plan(context, run, facts, condition, binary, not_depth);
    }
    let lookup_pair = comparison_lookup_inputs(run, facts, binary);
    let prepared = facts.comparison_preparation_inputs(binary);
    let spilled_literal = comparison_spilled_literal_inputs(run, facts, dialect, binary);
    let (lhs_producer, rhs_producer, base) = if let Some((producer, base)) = read_input {
        (producer, None, base)
    } else if let Some((lhs, rhs, base)) = prepared.or(lookup_pair).or(spilled_literal) {
        (lhs, Some(rhs), base)
    } else {
        use crate::hir::common::HirBinaryOpKind;
        if !matches!(
            binary.op,
            HirBinaryOpKind::Eq
                | HirBinaryOpKind::Lt
                | HirBinaryOpKind::Le
                | HirBinaryOpKind::Gt
                | HirBinaryOpKind::Ge
        ) {
            return None;
        }
        let (HirExpr::Call(lhs), HirExpr::Call(rhs)) = (&binary.lhs, &binary.rhs) else {
            return None;
        };
        let lhs_frame = facts.native_call_layout(lhs)?;
        let rhs_frame = facts.native_call_layout(rhs)?;
        let layout = facts.native_binary_layout(binary)?;
        if layout.lhs != Some(lhs_frame.home)
            || layout.rhs != Some(rhs_frame.home)
            || rhs_frame.home.slot() != lhs_frame.home.slot() + 1
        {
            return None;
        }
        // 两侧 CALL 各自重发原帧。左侧 SELF receiver 的双用途 carrier 由共享
        // method builder 消费；不能把 receiver 声明塞进无读取的 nil run。
        (
            facts.operation_result_temp(lhs.source_site?)?,
            Some(facts.operation_result_temp(rhs.source_site?)?),
            lhs_frame.home,
        )
    };
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    if read_input.is_some()
        && !builder.comparison_literal_layout(binary, &binary.rhs, base.slot() + 1)
    {
        // TargetConstraint：内嵌 RHS 仍须符合原 RK 或立即数比较布局。
        return None;
    }
    // 比较读取仍按原寄存器布局发出，字段 base/key 的准备不能套用 callee 语法许可。
    builder.register_operand = spilled_literal.is_some()
        || lookup_pair.is_some()
        || read_input.is_some()
            && run
                .last()
                .and_then(|stmt| scalar_binding(stmt))
                .is_some_and(|(_, value)| matches!(value, HirExpr::TableAccess(_)));
    let lhs = builder.expr(
        &binary.lhs,
        run.len(),
        base.slot(),
        None,
        true,
        false,
        Some(lhs_producer),
    )?;
    let rhs = if let Some(rhs_producer) = rhs_producer {
        if spilled_literal.is_some() {
            let literal = if super::tables::literal_rk(&binary.rhs) {
                &binary.rhs
            } else {
                scalar_binding(run.last()?)?.1
            };
            // TargetConstraint：池满后原 LOADK/LOADNIL 必须仍发到相邻 RHS 槽。
            if !builder.comparison_literal_layout(binary, literal, base.slot() + 1) {
                return None;
            }
            builder.register_operand = false;
        }
        builder.expr(
            &binary.rhs,
            run.len(),
            base.slot() + 1,
            None,
            true,
            spilled_literal.is_some(),
            Some(rhs_producer),
        )?
    } else {
        binary.rhs.clone()
    };
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let rebuilt = crate::hir::common::HirBinaryExpr {
        source_site: binary.source_site,
        op: binary.op,
        lhs,
        rhs,
    };
    if prepared.is_some() && facts.comparison_preparation_frame(&rebuilt) != Some(base) {
        return None;
    }
    let mut condition = condition.clone();
    let mut operand = &mut condition;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = operand else {
            unreachable!()
        };
        operand = &mut unary.expr;
    }
    *operand = HirExpr::Binary(Box::new(rebuilt));
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![condition].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 字段默认值与比较右侧的 GETUPVAL 共同准备；短路只控制默认值，不移动右侧读取。
fn comparison_selected_read_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
    binary: &crate::hir::common::HirBinaryExpr,
    not_depth: usize,
) -> Option<Plan> {
    if matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
        || !matches!(
            binary.op,
            crate::hir::HirBinaryOpKind::Eq
                | crate::hir::HirBinaryOpKind::Lt
                | crate::hir::HirBinaryOpKind::Le
                | crate::hir::HirBinaryOpKind::Gt
                | crate::hir::HirBinaryOpKind::Ge
        )
    {
        return None;
    }
    let (HirExpr::LogicalOr(logical) | HirExpr::LogicalAnd(logical)) = &binary.lhs else {
        return None;
    };
    let HirExpr::TableAccess(access) = &logical.lhs else {
        return None;
    };
    if !tables::literal_rk(&logical.rhs) || !matches!(binary.rhs, HirExpr::UpvalueRef(_)) {
        return None;
    }
    let base = facts.table_read_result_home(access)?;
    let layout = facts.native_binary_layout(binary)?;
    let (right, right_home) = facts.comparison_operand_preparation(binary, 1, &binary.rhs)?;
    if layout.lhs != Some(base)
        || layout.rhs != Some(right_home)
        || right_home.slot() != base.slot() + 1
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let lhs = builder.comparison_tree(&binary.lhs, run.len(), base.slot(), true)?;
    let rhs = builder.expr(
        &binary.rhs,
        run.len(),
        right_home.slot(),
        None,
        false,
        true,
        Some(right),
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let mut rebuilt = condition.clone();
    let mut operand = &mut rebuilt;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = operand else {
            unreachable!()
        };
        operand = &mut unary.expr;
    }
    let HirExpr::Binary(binary) = operand else {
        unreachable!()
    };
    binary.lhs = lhs;
    binary.rhs = rhs;
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![rebuilt].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 比较的一侧在低槽直接读取，另一侧在空闲槽完成原算术；不制造中间声明。
fn comparison_operation_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    condition: &HirExpr,
    binary: &crate::hir::common::HirBinaryExpr,
    not_depth: usize,
) -> Option<Plan> {
    let (target, value) = scalar_local(run.last()?)?;
    if !matches!(value, HirExpr::Binary(_) | HirExpr::Unary(_)) {
        return None;
    }
    let side = [&binary.lhs, &binary.rhs]
        .iter()
        .position(|value| matches!(value, HirExpr::LocalRef(local) if *local == target))?;
    let (producer, base) = facts.comparison_operand_preparation(binary, side, value)?;
    let other = facts.direct_binary_operand_home(binary, 1 - side)?;
    let layout = facts.native_binary_layout(binary)?;
    if other.slot() >= base.slot() || [layout.lhs, layout.rhs][1 - side] != Some(other) {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let value = builder.expr(
        [&binary.lhs, &binary.rhs][side],
        run.len(),
        base.slot(),
        None,
        false,
        true,
        Some(producer),
    )?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    let mut condition = condition.clone();
    let mut operand = &mut condition;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = operand else {
            unreachable!()
        };
        operand = &mut unary.expr;
    }
    let HirExpr::Binary(rebuilt) = operand else {
        unreachable!()
    };
    if side == 0 {
        rebuilt.lhs = value;
    } else {
        rebuilt.rhs = value;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![condition].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 宽常量池中的读取与字面量按原相邻槽准备；两边均绑定比较的唯一 use→Def。
fn comparison_spilled_literal_inputs(
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    binary: &crate::hir::common::HirBinaryExpr,
) -> Option<(TempId, TempId, HomeSlotKey)> {
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
        || !matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Eq
                | crate::hir::common::HirBinaryOpKind::Lt
                | crate::hir::common::HirBinaryOpKind::Le
                | crate::hir::common::HirBinaryOpKind::Gt
                | crate::hir::common::HirBinaryOpKind::Ge
        )
    {
        return None;
    }
    let literal = if super::tables::literal_rk(&binary.rhs) {
        &binary.rhs
    } else {
        let (rhs, literal) = scalar_binding(run.last()?)?;
        if rhs.expr() != binary.rhs || !super::tables::literal_rk(literal) {
            return None;
        }
        literal
    };
    let (right, right_home) = facts.comparison_operand_preparation(binary, 1, literal)?;
    let left_value = run
        .iter()
        .rev()
        .filter_map(|stmt| scalar_binding(stmt))
        .find_map(|(binding, value)| (binding.expr() == binary.lhs).then_some(value))?;
    if !matches!(
        left_value,
        HirExpr::TableAccess(_) | HirExpr::GlobalRef(_) | HirExpr::UpvalueRef(_)
    ) {
        return None;
    }
    let (left, left_home) = facts.comparison_operand_preparation(binary, 0, left_value)?;
    (right_home.slot() == left_home.slot() + 1).then_some((left, right, left_home))
}

/// 常量比较的单个准备沿用原 use→Def；全局读取另核对原 free slot 和内嵌常量。
/// 两个字段读取仍在相邻原槽准备；左侧的唯一声明由整批事务消费。
fn comparison_lookup_inputs(
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    binary: &crate::hir::common::HirBinaryExpr,
) -> Option<(TempId, TempId, HomeSlotKey)> {
    if !matches!(
        binary.op,
        crate::hir::common::HirBinaryOpKind::Eq
            | crate::hir::common::HirBinaryOpKind::Lt
            | crate::hir::common::HirBinaryOpKind::Le
            | crate::hir::common::HirBinaryOpKind::Gt
            | crate::hir::common::HirBinaryOpKind::Ge
    ) {
        return None;
    }
    let lhs = match &binary.lhs {
        HirExpr::LocalRef(local) => {
            let (target, value) = scalar_local(run.last()?)?;
            if target != *local {
                return None;
            }
            value
        }
        value => value,
    };
    let (HirExpr::TableAccess(lhs), HirExpr::TableAccess(rhs)) = (lhs, &binary.rhs) else {
        return None;
    };
    let layout = facts.native_binary_layout(binary)?;
    let (left, right) = (
        facts.table_read_result_home(lhs)?,
        facts.table_read_result_home(rhs)?,
    );
    if layout.lhs != Some(left) || layout.rhs != Some(right) || right.slot() != left.slot() + 1 {
        return None;
    }
    let (
        crate::hir::common::HirOperationSources::Single(ls),
        crate::hir::common::HirOperationSources::Single(rs),
    ) = (&lhs.sources, &rhs.sources)
    else {
        return None;
    };
    Some((
        facts.operation_result_temp(*ls)?,
        facts.operation_result_temp(*rs)?,
        left,
    ))
}

/// 尾部已树化的比较须逐操作重发同一准备槽，不能仅凭整体结果为 Boolean 放行。
fn predicate_preserves_frame(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    value: &HirExpr,
    base: HomeSlotKey,
) -> bool {
    match value {
        HirExpr::LogicalAnd(expr) | HirExpr::LogicalOr(expr) => {
            predicate_preserves_frame(context, facts, dialect, &expr.lhs, base)
                && predicate_preserves_frame(context, facts, dialect, &expr.rhs, base)
        }
        HirExpr::Unary(expr)
            if expr.op == crate::hir::HirUnaryOpKind::Not && expr.source_site.is_none() =>
        {
            predicate_preserves_frame(context, facts, dialect, &expr.expr, base)
        }
        HirExpr::Binary(binary) => {
            let literal = super::tables::literal_rk(&binary.rhs);
            let inputs = if literal {
                facts
                    .comparison_operand_preparation(binary, 0, &binary.lhs)
                    .map(|(producer, home)| (producer, None, home))
            } else {
                comparison_lookup_inputs(&[], facts, binary)
                    .map(|(left, right, home)| (left, Some(right), home))
            };
            let Some((lhs, rhs, home)) = inputs else {
                return false;
            };
            if home != base {
                return false;
            }
            let Some(mut builder) = frame_builder(context, &[], facts, dialect, base.slot()) else {
                return false;
            };
            builder.register_operand = true;
            if builder
                .expr(&binary.lhs, 0, base.slot(), None, true, false, Some(lhs))
                .is_none()
            {
                return false;
            }
            if literal {
                // 尾谓词的常量也须按原 RK/显式准备布局重发，不能只按值类型放行。
                builder.comparison_literal_layout(binary, &binary.rhs, base.slot() + 1)
                    && facts.native_binary_layout(binary).is_some_and(|layout| {
                        layout.rhs.is_none()
                            || facts
                                .comparison_operand_preparation(binary, 1, &binary.rhs)
                                .is_some_and(|(_, home)| Some(home) == layout.rhs)
                    })
            } else {
                builder
                    .expr(&binary.rhs, 0, base.slot() + 1, None, true, false, rhs)
                    .is_some()
            }
        }
        _ => predicate_reads_below(value, facts, base.slot()),
    }
}

fn comparison_read_input(
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    binary: &crate::hir::common::HirBinaryExpr,
) -> Option<(TempId, HomeSlotKey)> {
    if !matches!(
        binary.rhs,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    ) {
        return None;
    }
    let value = match HirBinding::from_expr(&binary.lhs) {
        Some(binding) => {
            let (target, value) = scalar_binding(run.last()?)?;
            if target != binding {
                return None;
            }
            value
        }
        None => &binary.lhs,
    };
    if matches!(
        value,
        HirExpr::UpvalueRef(_) | HirExpr::Call(_) | HirExpr::TableAccess(_)
    ) {
        // 上值、字段读取或单结果 CALL 紧邻比较；共享证书固定唯一消费者和原结果槽。
        // 完整 builder 再验证 CALL 的所有嵌套输入，不能只移走最终结果快照。
        return facts.comparison_read_preparation(binary, value);
    }
    let HirExpr::GlobalRef(global) = value else {
        return None;
    };
    if dialect == DecompileDialect::Luau || binary.op != crate::hir::common::HirBinaryOpKind::Eq {
        return None;
    }
    let home = facts.global_read_frame(global, dialect)?;
    let layout = facts.native_binary_layout(binary)?;
    let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
        return None;
    };
    // 候选接受：唯一原读取仍在比较的同一槽执行；不把一次显式 LOADK 改成常量比较。
    (layout.lhs == Some(home) && layout.rhs.is_none())
        .then_some((facts.operation_result_temp(source)?, home))
}

/// 现存低槽的字面量/已有绑定选择只收回首个谓词准备，不移动分支求值或原写回。
fn literal_selection_frame(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt: &HirStmt,
) -> Option<Plan> {
    if !matches!(stmt, HirStmt::Assign(_)) {
        return None;
    }
    let (target @ HirLValue::Local(_), value @ HirExpr::LogicalOr(or_)) = operation_target(stmt)?
    else {
        return None;
    };
    let HirExpr::LogicalAnd(and_) = &or_.lhs else {
        return None;
    };
    let mut plan = condition_plan(context, run, facts, dialect, &and_.lhs)?;
    if ![&and_.rhs, &or_.rhs].iter().all(|value| {
        matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        ) || matches!(value, HirExpr::LocalRef(_) | HirExpr::ParamRef(_))
            && predicate_reads_below(value, facts, plan.base.slot())
    }) {
        return None;
    }
    if dialect == DecompileDialect::Luau
        && matches!(plan.values.fixed.as_slice(), [HirExpr::Call(_)])
    {
        // Luau 的选值表达式先预留结果槽，纯谓词 CALL 在高一槽执行。
        // condition_plan 已核对 CALL 的原槽；整个 Assign 请求的是结果槽处的
        // 空闲前缀，不能要求一个并不存在的中间 local 填满这格。
        // 若该格仍属已有绑定，完整 prefix 验证会拒绝，不挪动 CALL 来让候选成立。
        plan.base = HomeSlotKey::new(plan.base.slot().checked_sub(1)?, 0);
    }
    let HirLValue::Local(local) = target else {
        unreachable!()
    };
    if facts.trusted_local_home_slot(local)?.slot() >= plan.base.slot() {
        return None;
    }
    let mut value = value.clone();
    let HirExpr::LogicalOr(or_) = &mut value else {
        unreachable!()
    };
    let HirExpr::LogicalAnd(and_) = &mut or_.lhs else {
        unreachable!()
    };
    and_.lhs = plan.values.fixed.pop()?;
    plan.values = vec![value].into();
    plan.assignment_targets = vec![HirLValue::Local(local)];
    Some(plan)
}

/// JIT/Luau 的关系比较仍把数值字面量装入 free slot；内嵌后重发同一 LOAD 与比较。
fn comparison_literal_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    condition: &HirExpr,
    binary: &crate::hir::common::HirBinaryExpr,
    not_depth: usize,
) -> Option<Plan> {
    use crate::hir::common::HirBinaryOpKind;
    if !matches!(
        binary.op,
        HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge
    ) {
        // TargetConstraint：相等比较可改发常量池比较指令，不能借此删除原寄存器 LOAD。
        return None;
    }
    let HirExpr::LocalRef(local) = binary.rhs else {
        return None;
    };
    let HirStmt::LocalDecl(decl) = *run.last()? else {
        return None;
    };
    let ([binding], [value], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    if *binding != local
        || !matches!(value, HirExpr::Integer(_) | HirExpr::Number(_))
        || decl.initializer_merge_transaction.is_some()
        || context.proto.local_debug_hints[local.index()].is_some()
        || context.proto.local_debug_scopes[local.index()].is_some()
        || context
            .proto
            .inline_dispositions
            .local(local)
            .must_preserve()
    {
        return None;
    }
    let base = facts.trusted_local_home_slot(local)?;
    let lhs_home = match binary.lhs {
        HirExpr::LocalRef(lhs) => facts.trusted_local_home_slot(lhs)?,
        HirExpr::ParamRef(lhs) => facts.trusted_param_home_slot(lhs)?,
        _ => return None,
    };
    let layout = facts.native_binary_layout(binary)?;
    if lhs_home.slot() >= base.slot()
        || layout.lhs != Some(lhs_home)
        || layout.rhs != Some(base)
        || context.barred.contains(&base)
        || context.closed.contains(&base)
    {
        return None;
    }
    let mut condition = condition.clone();
    let mut operand = &mut condition;
    for _ in 0..not_depth {
        let HirExpr::Unary(unary) = operand else {
            unreachable!();
        };
        operand = &mut unary.expr;
    }
    let HirExpr::Binary(rebuilt) = operand else {
        unreachable!();
    };
    rebuilt.rhs = value.clone();
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: run.len() - 1,
        sink: run.len(),
        base,
        values: vec![condition].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 三个 header 控制值按原事件顺序共同消费，不能独立缩短某个 CALL 结果的根区间。
fn numeric_for_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    for_: &crate::hir::common::HirNumericFor,
) -> Option<Plan> {
    let base = numeric_header_base(for_, dialect)?;
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    if ![&for_.start, &for_.limit, &for_.step]
        .iter()
        .any(|value| match value {
            HirExpr::TempRef(_) => true,
            HirExpr::LocalRef(local) => facts
                .trusted_local_home_slot(*local)
                .is_some_and(|home| home.slot() >= base.slot()),
            HirExpr::Call(call) => matches!(&call.callee, HirExpr::LocalRef(local)
                if builder.definition(*local, run.len()).is_some_and(|index|
                    matches!(scalar_local(run[index]), Some((_, HirExpr::Closure(_)))))),
            _ => false,
        })
    {
        // 已嵌入的 CALL 仍可能留下原 CLOSURE callee；其创建和调用必须一并消费。
        // 其它整个控制值已是表达式时没有 header carrier 可收回；嵌入调用的 receiver/field
        // alias 留给已有 method owner，否则新前缀保留会截断其首事件证明（407）。
        return None;
    }
    let luau_top = if dialect == DecompileDialect::Luau {
        Some(facts.numeric_for_body_frame(for_)?.binding_slot + 1)
    } else {
        None
    };
    let mut values = Vec::with_capacity(3);
    for (offset, value) in [&for_.start, &for_.limit, &for_.step]
        .into_iter()
        .enumerate()
    {
        values.push(if let Some(top) = luau_top {
            luau_numeric_control(
                &mut builder,
                value,
                for_.control_homes[offset],
                for_.control_values[offset],
                top,
            )?
        } else {
            builder.expr(
                value,
                run.len(),
                base.slot() + offset,
                None,
                false,
                true,
                for_.control_values[offset],
            )?
        });
    }
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: values.into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// compileStatFor 先预留控制区与可写 index，再以 compileExprTemp 求三个值。
/// 只有 top-1 目标上的 CALL 原位返回，其余 CALL 在 top 返回并紧邻 MOVE 到控制槽。
/// 控制 COPY 在循环语法中重发，不使用“后缀仍保留 COPY”的另一种证书。
fn luau_numeric_control(
    builder: &mut FrameBuilder<'_>,
    value: &HirExpr,
    target: HomeSlotKey,
    original: Option<TempId>,
    top: usize,
) -> Option<HirExpr> {
    let definition = match value {
        HirExpr::TempRef(temp) => Some((
            HirBinding::Temp(*temp),
            *builder.temp_definitions.get(temp)?,
        )),
        HirExpr::LocalRef(local)
            if builder.facts.trusted_local_home_slot(*local)?.slot() >= builder.base =>
        {
            Some((
                HirBinding::Local(*local),
                builder.definition(*local, builder.run.len())?,
            ))
        }
        _ => None,
    };
    let expression = if let Some((_, index)) = definition {
        scalar_binding(builder.run[index])?.1
    } else {
        value
    };
    let HirExpr::Call(call) = expression else {
        return builder.expr(
            value,
            builder.run.len(),
            target.slot(),
            None,
            false,
            true,
            original,
        );
    };
    let facts = builder.facts;
    // 数值循环的控制 COPY 不区分普通 CALL 与 FASTCALL；后者的 direct 参数、
    // fallback 顺序仍由共享 call builder 的 FASTCALL 协议核对。
    let frame = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))?;
    let producer = facts.operation_result_temp(call.source_site?)?;
    let original = original?;
    let slot = if target.slot() + 1 == top {
        target.slot()
    } else {
        top
    };
    if frame.home != HomeSlotKey::new(slot, 0)
        || facts.trusted_temp_home_slot(original) != Some(target)
        || facts
            .complete_temp_non_move_write_homes(producer)
            .iter()
            .any(|home| *home != frame.home)
    {
        return None;
    }
    let moves = facts.trusted_immediate_moves(producer)?;
    if target == frame.home {
        if original != producer || !moves.is_empty() {
            return None;
        }
    } else if !matches!(moves, [copy] if copy.source == Some(producer)
        && copy.source_home == frame.home && copy.target == original && copy.target_home == target)
    {
        return None;
    }
    if facts
        .complete_temp_definition_write_homes(producer)
        .iter()
        .any(|home| *home != frame.home && *home != target)
    {
        return None;
    }
    let before = if let Some((binding, index)) = definition {
        if index < builder.next_event {
            return None;
        }
        let context = builder.native?;
        match binding {
            HirBinding::Temp(temp) => {
                if (temp != producer && temp != original)
                    || context.proto.inline_dispositions.temp(temp).must_preserve()
                {
                    return None;
                }
            }
            HirBinding::Local(local) => {
                if (facts.promoted_local_for_temp(producer) != Some(local)
                    && facts.promoted_local_for_temp(original) != Some(local))
                    || context.proto.local_debug_scopes[local.index()].is_some()
                    || context.proto.local_debug_hints[local.index()].is_some()
                    || context
                        .proto
                        .inline_dispositions
                        .local(local)
                        .must_preserve()
                {
                    return None;
                }
            }
            _ => return None,
        }
        if context.closed.contains(&target) || context.closed.contains(&frame.home) {
            return None;
        }
        index
    } else {
        builder.run.len()
    };
    let call = builder.call(call, before, slot, false, CallWidth::Single)?;
    if let Some((_, index)) = definition {
        builder.finish_event(index)?;
    }
    Some(HirExpr::Call(Box::new(call)))
}

/// 低槽快照字段写，或将原 CALL 结果用作常量字段 base，都结束该 CALL 的表达式准备。
/// 这里只选择独立 initializer，删除参数准备仍由完整帧和后继 root preview 证明。
fn low_slot_store_boundary(
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    base: usize,
) -> bool {
    let HirStmt::Assign(assign) = stmt else {
        return false;
    };
    let ([HirLValue::TableAccess(access)], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return false;
    };
    let low = |value: &HirExpr| {
        matches!(value, HirExpr::LocalRef(local)
        if facts.trusted_local_home_slot(*local).is_some_and(|home| home.slot() < base))
    };
    if tables::literal_rk(&access.key)
        && tables::literal_rk(value)
        && let HirExpr::LocalRef(local) = access.base
        && let Some(home) = facts.trusted_local_home_slot(local)
        && home.slot() == base
        && facts
            .native_table_write_layout(access)
            .is_some_and(|layout| {
                if layout.base != home {
                    return false;
                }
                match (layout.key, layout.value) {
                    (None, None) => true,
                    (None, Some(value))
                        if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau) =>
                    {
                        value == HomeSlotKey::new(base + 1, 0)
                    }
                    (Some(key), Some(value)) if dialect == DecompileDialect::Luau => {
                        key == HomeSlotKey::new(base + 1, 0)
                            && value == HomeSlotKey::new(base + 2, 0)
                    }
                    _ => false,
                }
            })
    {
        // 原 CALL 结果随后作为 SETTABLE 的现成 base；PUC 使用 RK，JIT/Luau
        // 的字面量仍按字段 scratch 布局准备。字段写不属于 CALL 的结果表达式。
        return true;
    }
    // 原 CALL 结果作为 SETTABLE value，base/key 都是已有低槽时，字段写结束
    // 结果的准备区。这里只划分候选；原 Def、调用帧及写回由完整计划验证。
    if low(&access.base)
        && facts
            .native_table_write_layout(access)
            .is_some_and(|layout| {
                layout.base.slot() < base
                    && layout.key.is_none_or(|home| home.slot() < base)
                    && layout.value.is_some_and(|home| home.slot() == base)
            })
        && matches!(value, HirExpr::LocalRef(local)
            if facts.trusted_local_home_slot(*local).is_some_and(|home| home.slot() == base))
    {
        return true;
    }
    low(&access.base)
        && matches!(access.key, HirExpr::String(_) | HirExpr::Integer(_))
        && low(value)
}

fn plan(
    context: NativeFrameContext<'_>,
    stmts: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    let frame = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))?;
    let assignment_targets = match stmts[sink] {
        HirStmt::Assign(assign)
            if scalar_local(stmts[sink]).is_some_and(|(local, _)| {
                facts
                    .trusted_local_home_slot(local)
                    .is_some_and(|home| home.slot() < frame.home.slot())
            }) =>
        {
            assign.targets.clone()
        }
        _ => Vec::new(),
    };
    // 已树化的低槽写回仍在原空闲区准备 CALL/FASTCALL；目标保持已有身份，
    // 不作为调用结果的新声明占据 freereg。共同提交参数、结果槽和后继根释放。
    let result_locals = if let HirStmt::Assign(assign) = stmts[sink]
        && let Some(locals) = call_result_bindings(assign, facts)
    {
        locals
    } else if assignment_targets.is_empty() {
        scalar_local(stmts[sink])
            .map(|(local, _)| local)
            .into_iter()
            .collect()
    } else {
        Vec::new()
    };
    if call.fastcall.is_some() {
        let mut plan = fastcall_plan(context, &stmts[..sink], facts, dialect, sink, call, width)?;
        if let CallWidth::Fixed(width) = width {
            let value = plan.values.fixed.pop()?;
            plan.values = HirValuePack::expanding(Vec::new(), HirPackTail::exact(value, width));
        }
        plan.assignment_targets = assignment_targets;
        plan.result_locals = result_locals;
        return Some(plan);
    }
    // 固定多返回值的声明可被 promotion 提前放在 CALL 前。它不执行准备事件，
    // 且由同一计划在结果位置重建；不能让这组空声明截断 callee/参数的原帧。
    let mut preparation_end = sink;
    while preparation_end > 0
        && matches!(stmts[preparation_end - 1],
        HirStmt::LocalDecl(decl) if decl.values.is_empty()
            && decl.initializer_merge_transaction.is_none()
            && !decl.bindings.is_empty()
            && decl.bindings.iter().all(|local| result_locals.contains(local)))
    {
        preparation_end -= 1;
    }
    let run = &stmts[..preparation_end];
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    if dialect == DecompileDialect::Luau
        && let HirStmt::GenericFor(for_) = stmts[sink]
    {
        let iterator = facts.generic_for_body_frame(for_)?;
        builder.declaration_reserved_top = Some(frame.home.slot() + iterator.initializers.len());
    }
    let call = builder.call(call, run.len(), frame.home.slot(), true, width)?;
    let first = match builder.first_event {
        Some(first) if builder.next_event == run.len() => first,
        // 已经嵌入的完整 CALL 仍依赖原低槽声明前缀；没有 producer 可删不表示
        // AST 可以删除前缀常量，让观察点的整帧下移。TAILCALL 搬移参数后，原准备区
        // 仍可能留下 caller 可观察的残根；开放返回包同样发布前缀。共享 builder 核对全部事件。
        None if matches!(width, CallWidth::Ignore | CallWidth::Tail)
            || matches!(stmts[sink], HirStmt::GlobalDecl(_)) =>
        {
            sink
        }
        _ => return None,
    };
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink,
        base: frame.home,
        values: if let CallWidth::Fixed(width) = width
            && matches!(stmts[sink], HirStmt::GlobalDecl(_))
        {
            HirValuePack::expanding(
                Vec::new(),
                HirPackTail::exact(HirExpr::Call(Box::new(call)), width),
            )
        } else if matches!(width, CallWidth::Tail | CallWidth::Fixed(_)) {
            HirValuePack {
                fixed: Vec::new(),
                tail: Some(HirPackTail::open(HirExpr::Call(Box::new(call)))),
            }
        } else {
            vec![HirExpr::Call(Box::new(call))].into()
        },
        result_locals,
        discarded_result: None,
        assignment_targets,
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// Boolean initializer 或直接上值写回在原结果槽重发 ValueDecision 的预写。
/// 结果身份来自原决策及 SETUPVAL 来源，不按相邻常量与逻辑表达式的外形猜配对。
fn boolean_value_initializer(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    first: FlatStmt<'_>,
    sink: FlatStmt<'_>,
    (initial, result, home, initial_value): (
        crate::hir::common::TempId,
        crate::hir::common::TempId,
        HomeSlotKey,
        bool,
    ),
    read_locals: &BTreeSet<LocalId>,
) -> Option<Plan> {
    let (initial_binding, HirExpr::Boolean(original)) = scalar_binding(first.stmt)? else {
        return None;
    };

    let writeback = scalar_local(sink.stmt).and_then(|(target, _)| {
        let copy = facts.value_result_copy(result)?;
        (matches!(sink.stmt, HirStmt::Assign(_))
            && copy.source_home == home
            && copy.target_home.slot() < home.slot()
            && facts.promoted_local_for_temp(copy.target) == Some(target)
            && facts.trusted_local_home_slot(target) == Some(copy.target_home))
        .then_some(target)
    });
    let (target, value) = if let Some((target, value)) = scalar_local(sink.stmt) {
        if facts.promoted_local_for_temp(result) != Some(target) && writeback != Some(target) {
            return None;
        }
        (Some(target), value)
    } else {
        let HirStmt::Assign(assign) = sink.stmt else {
            return None;
        };
        let ([value], None) = (assign.values.fixed.as_slice(), &assign.values.tail) else {
            return None;
        };
        if facts.boolean_upvalue_prewrite(assign) != Some((initial, result, home, initial_value)) {
            return None;
        }
        (None, value)
    };

    if *original != initial_value
        || !(matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            || matches!(value, HirExpr::Binary(binary)
                if facts.comparison_result_temp(binary) == Some(result)))
        || context.barred.contains(&home)
        || context.closed.contains(&home)
        || target.is_some_and(|local| {
            writeback != Some(local) && facts.trusted_local_home_slot(local) != Some(home)
        })
        || match initial_binding {
            HirBinding::Temp(temp) => temp != initial,
            HirBinding::Local(local) => {
                target == Some(local)
                    || facts.promoted_local_for_temp(initial) != Some(local)
                    || read_locals.contains(&local)
            }
            _ => true,
        }
    {
        return None;
    }

    let run = [first.stmt, sink.stmt];
    // 上值写回不定义当前 frame 的槽，只有其 RHS 准备区进入定义索引。
    let preparation = &run[..1 + usize::from(target.is_some())];
    let mut builder = frame_builder(
        context,
        preparation,
        facts,
        DecompileDialect::Luau,
        home.slot(),
    )?;
    if writeback.is_none()
        && target
            .is_some_and(|target| !builder.homes_match(target, 1, home.slot(), None, Some(result)))
    {
        return None;
    }
    // 匿名预写可能尚未提升为 Local；Temp 与 Local 使用同一来源校验，
    // 只消去准备语句，保留结果的 debug 声明及其原 home。
    builder.consume_boolean_prewrite(
        (initial, result, home, initial_value),
        facts.temp_definition_reference_unaliased(initial),
        value,
        1,
        home.slot(),
    )?;

    builder.boolean_frame = Some(home.slot());
    let value = builder.expr(value, 1, home.slot(), None, false, true, Some(result))?;

    builder.finish_event(1)?;
    // 裸比较的原入口 LOADB 不能作为孤立 false 声明留下；与 CALL 参数
    // 使用相同的 Boolean 外壳重发预写，AST 不得将其按真值恒等式删除。
    let value = if matches!(value, HirExpr::Binary(_)) {
        let logical = Box::new(crate::hir::common::HirLogicalExpr {
            lhs: value,
            rhs: HirExpr::Boolean(!initial_value),
            preserves_boolean_prewrite: true,
        });
        if initial_value {
            HirExpr::LogicalOr(logical)
        } else {
            HirExpr::LogicalAnd(logical)
        }
    } else {
        value
    };
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first.id,
        sink: sink.id,
        base: home,
        values: vec![value].into(),
        result_locals: target.filter(|_| writeback.is_none()).into_iter().collect(),
        discarded_result: None,
        assignment_targets: writeback.map(HirLValue::Local).into_iter().collect(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: vec![first.id],
    })
}

/// FASTCALL 参数准备按原 direct/COPY/开放域恢复，之后执行 fallback lookup；Boolean 可附常量消息。
/// 原 header Boolean 由 ValueDecision 配对，恢复短路时在相同槽重发；不假定 fast path 必成功。
fn fastcall_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    if call.fastcall.is_some_and(|protocol| {
        protocol.tail_is_direct()
            && (0..call.args.fixed.len()).all(|index| protocol.fixed_is_direct(index))
    }) && call.args.tail.is_some()
        && matches!(
            width,
            CallWidth::Single | CallWidth::Ignore | CallWidth::Fixed(_)
        )
    {
        return fastcall_open_plan(context, run, facts, dialect, sink, call, width);
    }
    if matches!(width, CallWidth::Single | CallWidth::Ignore)
        && (fastcall_has_copy_arguments(call)
            || matches!(call.fastcall,
                Some(crate::transformer::FastCallProtocol::Mask { builtin, .. })
                    if builtin != 1 || matches!(width, CallWidth::Single)))
    {
        return fastcall_fixed_arguments_plan(context, run, facts, dialect, sink, call, width);
    }
    // Luau Bytecode.h 的 LBF_ASSERT = 1；保留原编号，不凭 fallback 名字猜内建语义。
    let protocol @ crate::transformer::FastCallProtocol::Mask {
        builtin: 1,
        direct_tail: false,
        ..
    } = call.fastcall?
    else {
        return None;
    };
    if dialect != DecompileDialect::Luau
        || !matches!(width, CallWidth::Ignore)
        || call.method != HirMethodCall::None
        || call.args.tail.is_some()
    {
        return None;
    }
    let [argument, message @ ..] = call.args.fixed.as_slice() else {
        return None;
    };
    if message.len() > 1 || !(0..call.args.fixed.len()).all(|index| protocol.fixed_is_direct(index))
    {
        return None;
    }
    let frame = facts.native_fastcall_frame(call)?;
    let ValuePack::Fixed(args) = frame.args else {
        return None;
    };
    if args.len != call.args.fixed.len()
        || args.start.index() != frame.home.slot() + 1
        || frame.results != Some(ResultPack::Ignore)
        || !frame.arguments_unaliased
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let value = match argument {
        HirExpr::LocalRef(local) => {
            if facts
                .trusted_local_home_slot(*local)
                .is_none_or(|home| home.slot() != args.start.index())
            {
                return None;
            }
            scalar_local(run[builder.definition(*local, run.len())?])?.1
        }
        value => value,
    };
    let boolean_prewrite = facts.boolean_argument_prewrite(call, 0).is_some()
        && matches!(value, HirExpr::Binary(_) | HirExpr::Unary(_));
    if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) || boolean_prewrite {
        builder.consume_boolean_argument_prewrite(
            call,
            0,
            argument,
            run.len(),
            args.start.index(),
        )?;
    } else if !(matches!(value, HirExpr::Binary(_))
        || matches!(value, HirExpr::Unary(unary)
            if unary.op == crate::hir::HirUnaryOpKind::Not
                && ((unary.source_site.is_none() && matches!(unary.expr, HirExpr::Binary(_)))
                    || facts.unary_result_home(unary) == Some(HomeSlotKey::new(args.start.index(), 0)))))
    {
        // assert 也接受任意真值；没有 Boolean 物化协议的参数交回通用 fixed 帧，
        // 不能只因 builtin=assert 就要求索引、调用或字面值先变成布尔表达式。
        return fastcall_fixed_arguments_plan(context, run, facts, dialect, sink, call, width);
    }
    builder.boolean_frame = Some(args.start.index());
    let argument = builder.expr(
        argument,
        run.len(),
        args.start.index(),
        None,
        false,
        true,
        facts.call_argument_value(call, 0).filter(|producer| {
            matches!(argument, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(*producer) == Some(*local))
        }),
    )?;
    let mut arguments = vec![argument];
    if let [message] = message {
        // message 也可有 LEN、索引或 CALL；共享 builder 在条件参数之后、
        // fallback callee 之前按原参数槽重发，不能只按字符串/低槽外形拒绝整帧。
        arguments.push(builder.expr(
            message, run.len(), args.start.index() + 1, None, false, true,
            facts.call_argument_value(call, 1).filter(|producer| {
                matches!(message, HirExpr::LocalRef(local) if facts.promoted_local_for_temp(*producer) == Some(*local))
            }),
        )?);
    }
    // fallback lookup 在所有参数准备后发生；它可能已经提升为复用低槽的 local。
    // 同一帧消费该 producer，不能把查找移到可能执行元方法的比较之前。
    let callee = builder.expr(
        &call.callee,
        run.len(),
        frame.home.slot(),
        None,
        true,
        false,
        Some(frame.callee),
    )?;
    if !context.callee_aliases.accepts_assert(&callee) {
        return None;
    }
    // 已完整嵌入的 assert 同普通 CALL 一样发布原前缀义务；没有准备声明可删，
    // 也不能在展开帧的后缀验证中漏掉这一观察点。
    let first = builder.first_event.unwrap_or(run.len());
    if builder.first_event.is_some() && builder.next_event != run.len() {
        return None;
    }
    let mut rebuilt = call.clone();
    rebuilt.callee = callee;
    rebuilt.args = arguments.into();
    if boolean_prewrite {
        rebuilt.boolean_prewrite_arguments =
            vec![(0, facts.boolean_argument_prewrite(call, 0)?.initial_value)];
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 开放参数 CALL 先完成，再执行 fallback lookup；固定参数仍先写入原槽，不压缩尾部返回宽度。
fn fastcall_open_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    let frame = facts.native_fastcall_frame(call)?;
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let rebuilt = builder.fastcall_open(call, run.len(), frame.home.slot(), width)?;
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原 debug、捕获或分支前缀义务给出必须保留的 CALL 结果身份。
/// 只恢复已有同槽声明的 RHS，完整准备事件、词法前缀和后续读写仍由同一帧事务核对。
fn source_call_initializer(
    proto: &HirProto,
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
    captured: &BTreeSet<LocalId>,
    shared_result: bool,
) -> bool {
    let matched = || {
        let (local, HirExpr::Call(call)) = scalar_local(stmt)? else {
            return None;
        };
        let initializer = facts.operation_result_temp(call.source_site?)?;
        // 匿名 Local 可在更早的 CALL+COPY 后复用；前缀义务属于当前结果 Def，
        // 不能据 Local 的未来用途把更早的结果也冻结成声明。
        let original_prefix = matches!(proto.inline_dispositions.temp(initializer),
            crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.contains(&HirInlineRetentionReason::PhysicalFramePrefix));
        // 捕获 cell 的共享 CALL 结果可能仍写回 callee 暂存；当前版本的多处读取
        // 才构成独立初始化边界，不能用 LocalId 的未来捕获冻结较早的临时调用。
        if !matches!(stmt, HirStmt::LocalDecl(_))
            && !original_prefix
            && !(captured.contains(&local)
                && shared_result
                && facts.operation_result_reference_unaliased(call.source_site?))
        {
            return None;
        }
        if !original_prefix
            && !captured.contains(&local)
            && proto
                .local_debug_scopes
                .get(local.index())
                .copied()
                .flatten()
                .and_then(|scope| proto.debug_scopes.get(scope).copied().flatten())
                .and_then(|scope| scope.initializer_temp)
                != Some(initializer)
        {
            return None;
        }
        let frame = facts
            .native_call_frame(call)
            .or_else(|| facts.native_fastcall_frame(call))?;
        (facts.promoted_local_for_temp(initializer) == Some(local)
            && facts.trusted_local_home_slot(local) == Some(frame.home)
            && matches!(frame.results, Some(ResultPack::Fixed(pack))
                if pack.start.index() == frame.home.slot() && pack.len == 1))
        .then_some(())
    };
    matched().is_some()
}

/// 同槽 callee/结果已提升为同一匿名 local 时，把相邻准备与 CALL 写回交给完整帧。
/// 这里只补候选入口；参数 COPY、callee 读取与声明前缀仍由 builder/preview 原子核对。
fn adjacent_callee_result_initializer(
    proto: &HirProto,
    previous: &HirStmt,
    stmt: &HirStmt,
    facts: &ProtoPromotionFacts,
) -> bool {
    let Some((local, value)) = scalar_local(previous) else {
        return false;
    };
    if !matches!(
        value,
        HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::TableAccess(_)
    ) || matches!(previous, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_some())
        || matches!(previous, HirStmt::Assign(assign) if assign.initializer_merge_transaction.is_some())
    {
        return false;
    }
    let Some((target, HirExpr::Call(call))) = scalar_local(stmt) else {
        return false;
    };
    let Some(frame) = facts
        .native_call_frame(call)
        .or_else(|| facts.native_fastcall_frame(call))
    else {
        return false;
    };
    target == local
        && call.callee == HirExpr::LocalRef(local)
        && proto.local_debug_hints[local.index()].is_none()
        && proto.local_debug_scopes[local.index()].is_none()
        && facts.trusted_local_home_slot(local) == Some(frame.home)
        && facts.promoted_local_for_temp(frame.callee) == Some(local)
        && call
            .source_site
            .and_then(|source| facts.operation_result_temp(source))
            .and_then(|result| facts.promoted_local_for_temp(result))
            == Some(local)
        && matches!(frame.results, Some(ResultPack::Fixed(pack))
            if pack.start.index() == frame.home.slot() && pack.len == 1)
}

/// 已有结果声明回到原 CALL 槽；非 direct 参数只能是低槽读取，不提前截断参数表达式树。
/// 这不是普通嵌套 CALL 的独立 initializer 许可，后者仍由后续帧下界决定提交时机。
fn fastcall_copy_initializer(
    stmt: &HirStmt,
    next: Option<&HirStmt>,
    facts: &ProtoPromotionFacts,
    following_floor: Option<usize>,
    nested: bool,
) -> bool {
    if nested || !matches!(stmt, HirStmt::LocalDecl(_)) {
        return false;
    }
    let Some((target, HirExpr::Call(call))) = scalar_local(stmt) else {
        return false;
    };
    if !fastcall_has_copy_arguments(call) {
        return false;
    }
    let Some(frame) = facts.native_fastcall_frame(call) else {
        return false;
    };
    if following_floor.is_some_and(|floor| floor <= frame.home.slot())
        || call
            .source_site
            .and_then(|source| facts.operation_result_temp(source))
            .is_some_and(|temp| facts.temp_is_transferred_call_argument(temp))
        || !matches!(frame.results, Some(ResultPack::Fixed(pack))
        if pack.start.index() == frame.home.slot() && pack.len == 1)
        || facts.trusted_local_home_slot(target) != Some(frame.home)
        || call
            .source_site
            .and_then(|source| facts.operation_result_temp(source))
            .and_then(|temp| facts.promoted_local_for_temp(temp))
            != Some(target)
    {
        return false;
    }
    !next.is_some_and(|next| matches!(scalar_local(next),
        Some((copy, HirExpr::LocalRef(source))) if *source == target
            && facts.trusted_local_home_slot(copy).is_none_or(|home| home.slot() <= frame.home.slot())))
}

fn fastcall_has_copy_arguments(call: &HirCallExpr) -> bool {
    matches!(call.fastcall,
        Some(protocol @ crate::transformer::FastCallProtocol::Mask { direct_tail: false, .. })
            if (0..call.args.fixed.len()).any(|index| !protocol.fixed_is_direct(index)))
}

/// 非 direct 参数保持快速路径的低槽直读和 fallback 的逐参数 COPY，然后才求 callee。
/// direct 参数先按原槽准备，嵌入常量在 fallback 才 LOADK；不按当前语句位置任意排序。
/// 这两条路径必须一起恢复；不能按普通 CALL 的 callee-first 顺序提前移动参数准备。
/// 全 direct 参数使用同一准备协议；是否存在 COPY 不决定表分配事务的恢复资格。
fn fastcall_fixed_arguments_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    call: &HirCallExpr,
    width: CallWidth,
) -> Option<Plan> {
    let frame = facts.native_fastcall_frame(call)?;
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    let rebuilt = builder.fastcall_fixed(call, run.len(), frame.home.slot(), width)?;
    let first = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink,
        base: frame.home,
        values: vec![HirExpr::Call(Box::new(rebuilt))].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

// local a=x; local b=y; return a,b 的高返回 COPY 可能在 caller 覆写低槽后
// 继续保根；终端无事件或低来源仍存活，都不足以直接收成 return x,y。
fn return_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    ret: &crate::hir::common::HirReturn,
) -> Option<Plan> {
    // 没有待消费的准备语句时，返回树已完整；避免为最终必然没有 first_event
    // 的候选递归重建整棵表达式，尤其是已经树化的长算术链。
    if run.is_empty() {
        return None;
    }
    let frame = facts.native_return_frame(ret)?;
    let mut builder = frame_builder(context, run, facts, dialect, frame.home.slot())?;
    // 单结果 CALL 与 RETURN 共用原槽时，完整帧可收回 callee 准备；固定返回包
    // 仍生成括号截断，不能将普通调用改成 TAILCALL 或扩成多返回值。
    let single_call = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let value = match value {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map_or(value, |(_, value)| value),
                value => value,
            };
            matches!(value, HirExpr::Call(_))
        });
    let single_concat = ret.values.fixed.first().is_some_and(|value| {
        let value = match value {
            HirExpr::LocalRef(local) => builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .map(|(_, value)| value),
            value => Some(value),
        };
        matches!(value, Some(HirExpr::Binary(binary))
            if binary.op == crate::hir::common::HirBinaryOpKind::Concat)
    });
    let single_lookup = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let value = match value {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map(|(_, value)| value),
                value => Some(value),
            };
            matches!(value, Some(HirExpr::TableAccess(_)))
        });
    let single_global = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let value = match value {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map(|(_, value)| value),
                value => Some(value),
            };
            matches!(value, Some(HirExpr::GlobalRef(global))
                if facts.global_read_frame(global, dialect) == Some(frame.home))
        });
    // 算术 RETURN 与参数语境共用原结果槽；操作数读取由共享 builder 验证，
    // 不能因为运算已经树化就把它之前仍需消费的 lookup 声明留在准备区。
    let single_arithmetic = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let value = match value {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map(|(_, value)| value),
                value => Some(value),
            };
            use crate::hir::common::HirBinaryOpKind::{Add, Div, Mod, Mul, Pow, Sub};
            matches!(value, Some(HirExpr::Binary(binary))
                if matches!(binary.op, Add | Sub | Mul | Div | Mod | Pow))
        });
    // 比较同样可以直接写原 RETURN 槽；共享 builder 核对操作数 scratch 和
    // Boolean 写入，不把字段读取后的临时结果误认成必须保留的源码声明。
    let single_comparison = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let value = match value {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map_or(value, |(_, value)| value),
                value => value,
            };
            matches!(value, HirExpr::Binary(binary)
                if facts.comparison_result_temp(binary).is_some())
        });
    // 单值字段返回仍须在原 GETTABLE 输出槽求值，特别是 base 被闭包捕获时，
    // 不能用通用 local 内联绕过原读取帧和声明前缀证明。
    if single_lookup && !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) {
        builder.register_operand = true;
    }
    // 裸全局读取没有环境/base 准备，仍须在原 RETURN 槽执行；不是任意低槽快照的代换。
    if single_global {
        builder.register_operand = true;
    }
    // GETUPVAL 直接准备单值 RETURN 时也有原生返回帧；保留读取，只收回同槽临时声明。
    // FrameBuilder 和整批 preview 仍须证明准备顺序与返回槽，不能把已有低槽快照搬过来。
    let single_upvalue = ret.values.fixed.first().is_some_and(|value| {
        let HirExpr::LocalRef(local) = value else {
            return false;
        };
        builder
            .definition(*local, run.len())
            .and_then(|index| scalar_local(run[index]))
            .is_some_and(|(_, value)| matches!(value, HirExpr::UpvalueRef(_)))
    });
    // 匿名 CLOSURE 与 RETURN 共用原结果槽；原创建身份及低槽 capture 由 builder
    // 核对。显式 debug 声明、递归捕获自身和额外 COPY 仍不能借此消除。
    let single_closure = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let HirExpr::LocalRef(local) = value else {
                return false;
            };
            builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .is_some_and(|(_, value)| matches!(value, HirExpr::Closure(_)))
        });
    // 构造器同样可直接在 RETURN 槽完成分配；共享 builder 保留原布局、字段
    // 求值和结果身份，不能把先前已有的表或具名 debug 声明当成返回准备。
    let single_constructor = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let HirExpr::LocalRef(local) = value else {
                return false;
            };
            builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .is_some_and(|(_, value)| matches!(value, HirExpr::TableConstructor(_)))
        });
    // 先前的索引/CONCAT 帧可能退休同槽旧身份，再恢复出末尾字面量声明。
    // 单值 RETURN 同样需要消费这次原槽覆盖；不是任意 literal local 的代换许可。
    let single_literal = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let HirExpr::LocalRef(local) = value else {
                return false;
            };
            builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .is_some_and(|(_, value)| {
                    matches!(
                        value,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                            | HirExpr::String(_)
                    )
                })
        });
    // 短路值树仍在原 RETURN 槽写回；含读取的 Boolean 树逐叶核对准备帧，
    // 完整声明前缀与写域证明继续阻止消除额外 COPY。
    let single_selection = ret.values.fixed.len() == 1
        && ret.values.fixed.first().is_some_and(|value| {
            let HirExpr::LocalRef(local) = value else {
                return false;
            };
            builder
                .definition(*local, run.len())
                .and_then(|index| scalar_local(run[index]))
                .is_some_and(|(_, value)| {
                    matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                })
        });
    match frame.values {
        ValuePack::Fixed(pack)
            if ret.values.tail.is_none()
                && pack.len == ret.values.fixed.len()
                && (pack.len > 1
                    || single_call
                    || single_concat
                    || single_lookup
                    || single_global
                    || single_arithmetic
                    || single_comparison
                    || single_upvalue
                    || single_closure
                    || single_constructor
                    || single_literal
                    || single_selection) => {}
        ValuePack::Open(_)
            if ret
                .values
                .tail
                .as_ref()
                .is_some_and(|tail| tail.exact_width().is_none()) => {}
        _ => return None,
    }
    let fixed = ret
        .values
        .fixed
        .iter()
        .enumerate()
        .map(|(index, expr)| {
            if dialect == DecompileDialect::Luau
                && let HirExpr::TableAccess(access) = expr
            {
                return builder.luau_lookup(access, run.len(), frame.home.slot() + index);
            }
            // 每个固定返回槽都可承接原 CLOSURE，包含此前已树化的闭包。
            // 原创建 Def 仍交给 builder 核对 home、COPY 写域和 capture 可见性。
            let value = match expr {
                HirExpr::LocalRef(local) => builder
                    .definition(*local, run.len())
                    .and_then(|index| scalar_local(run[index]))
                    .map_or(expr, |(_, value)| value),
                value => value,
            };
            let producer = if let HirExpr::Closure(closure) = value {
                Some(facts.operation_result_temp(closure.source_site?)?)
            } else {
                facts.fixed_return_input(ret, index)
            };
            builder.expr(
                expr,
                run.len(),
                frame.home.slot() + index,
                None,
                false,
                true,
                producer,
            )
        })
        .collect::<Option<Vec<_>>>()?;
    let tail = match &ret.values.tail {
        Some(tail) => {
            let HirExpr::Call(call) = tail.as_expr() else {
                return None;
            };
            Some(HirPackTail::open(HirExpr::Call(Box::new(builder.call(
                call,
                run.len(),
                frame.home.slot() + fixed.len(),
                false,
                CallWidth::Open,
            )?))))
        }
        None => None,
    };
    if dialect == DecompileDialect::Luau
        && tail.is_none()
        && let Some(first) = fixed.first().and_then(|value| builder.direct_home(value))
        && fixed.iter().enumerate().all(|(index, value)| {
            builder.direct_home(value) == Some(HomeSlotKey::new(first.slot() + index, 0))
        })
        && first != frame.home
    {
        // Luau 直接返回连续的既有 local，不重发准备区 COPY；不能删掉原槽覆盖。
        return None;
    }
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base: frame.home,
        values: HirValuePack { fixed, tail },
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原 CALL 的连续写回仍以低槽赋值保留时，可由这些语句履行累积 MOVE 责任。
/// 声明不能领取此证明；整批 preview 后还须确认各依赖语句未被删除、改写或迁为声明。
#[expect(
    clippy::type_complexity,
    reason = "只在一次帧候选中返回原写槽和冻结的语句依赖"
)]
fn retained_result_copies(
    flat: &[Option<FlatStmt<'_>>],
    index: usize,
    call: &HirCallExpr,
    facts: &ProtoPromotionFacts,
) -> Option<(BTreeSet<HomeSlotKey>, Vec<(usize, RetainedCopy)>)> {
    let result = facts.operation_result_temp(call.source_site?)?;
    let home = facts.trusted_temp_home_slot(result)?;
    let steps = facts.trusted_immediate_moves(result)?;
    if steps.is_empty() {
        return None;
    }
    let mut homes = BTreeSet::new();
    let mut retained = Vec::new();
    let mut previous_temp = result;
    let mut previous_local = facts.promoted_local_for_temp(result)?;
    for (offset, step) in steps.iter().enumerate() {
        let entry = flat.get(index + offset)?.as_ref()?;
        if offset + 1 == steps.len() && step.source == Some(previous_temp) {
            let copy = RetainedCopy::MethodReceiver {
                result: step.target,
                source: previous_local,
            };
            if copy.matches(entry.stmt, facts) {
                // 原低槽写回后紧邻的 SELF 负责高槽 receiver 副本；它必须在预览后
                // 仍是同一次方法调用，不能把该覆盖要求丢弃或移回前一个 CALL。
                homes.insert(step.target_home);
                retained.push((entry.id, copy));
                continue;
            }
        }
        let HirStmt::Assign(assign) = entry.stmt else {
            return None;
        };
        let ([HirLValue::Local(target)], [HirExpr::LocalRef(source)], None) = (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) else {
            return None;
        };
        if step.target_home.slot() >= home.slot()
            || step.source != Some(previous_temp)
            || *source != previous_local
            || facts.trusted_local_home_slot(*target) != Some(step.target_home)
            || facts.trusted_local_home_slot(*source) != Some(step.source_home)
        {
            return None;
        }
        homes.insert(step.target_home);
        previous_temp = step.target;
        previous_local = *target;
        if offset != 0 {
            retained.push((
                entry.id,
                RetainedCopy::Local {
                    target: *target,
                    source: *source,
                },
            ));
        }
    }
    Some((homes, retained))
}

/// 原 LOADNIL 的整组成员必须仍以相同顺序保留；不能把部分组或 debug 声明
/// 当作参数准备。成员的调用位置、保留义务和原槽由 FrameBuilder 逐项核对。
fn nil_argument_group<'a>(stmt: &HirStmt, facts: &'a ProtoPromotionFacts) -> Option<&'a [TempId]> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let HirLValue::Temp(first) = assign.targets.first()? else {
        return None;
    };
    let group = facts.nil_write_temps(*first)?;
    (group.len() > 1
        && assign.targets.len() == group.len()
        && assign.values.tail.is_none()
        && assign.values.fixed.len() == group.len()
        && assign
            .values
            .fixed
            .iter()
            .all(|value| matches!(value, HirExpr::Nil))
        && assign
            .targets
            .iter()
            .zip(group)
            .all(|(target, temp)| *target == HirLValue::Temp(*temp))
        && assign.initializer_merge_transaction.is_none()
        && assign.generic_for_initializer_producer.is_none()
        && assign.generic_for_dispatch_release.is_none()
        && assign.method_rewrite_transaction.is_none())
    .then_some(group)
}

pub(super) fn frame_builder<'a>(
    context: NativeFrameContext<'a>,
    run: &'a [&'a HirStmt],
    facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
    base: usize,
) -> Option<FrameBuilder<'a>> {
    let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut expanded_inputs = BTreeMap::<HomeSlotKey, Vec<(usize, LocalId)>>::new();
    let mut temp_definitions = BTreeMap::new();
    let mut nil_group_members = BTreeMap::new();
    for (index, stmt) in run.iter().enumerate() {
        if let Some((local, value)) = scalar_local(stmt) {
            definitions.entry(local).or_default().push(index);
            if context.expanded_callees.is_some()
                && let HirExpr::TableConstructor(table) = value
                && let Some(home) = facts.trusted_local_home_slot(local)
                && facts.allocation_result_home(table) == Some(home)
            {
                expanded_inputs
                    .entry(home)
                    .or_default()
                    .push((index, local));
            }
        } else if let Some((HirBinding::Temp(temp), _)) = scalar_binding(stmt) {
            if temp_definitions.insert(temp, index).is_some() {
                return None;
            }
        } else if let Some(group) = nil_argument_group(stmt, facts) {
            for (offset, &temp) in group.iter().enumerate() {
                if temp_definitions.insert(temp, index).is_some() {
                    return None;
                }
                nil_group_members.insert(temp, (offset, group.len()));
            }
        } else if !(super::super::table_constructors::constructor_write(stmt).is_some()
            || matches!(stmt, HirStmt::LocalRootRelease(_))
            // 空声明不提供值定义，但可以留在本次候选之前。事件游标不会跳过
            // 窗口内部的声明；不能因无关前缀含空声明而拒绝后面的完整调用帧。
            || matches!(stmt, HirStmt::LocalDecl(decl) if decl.values.is_empty()))
        {
            return None;
        }
    }
    let constructors = tables::index(run, &definitions);
    Some(FrameBuilder {
        run,
        definitions,
        constructors,
        expanded_inputs,
        constructor_depth: 0,
        declaration_reserved_top: None,
        indexed_key_base: None,
        register_operand: false,
        facts,
        dialect,
        base,
        next_event: 0,
        first_event: None,
        methods: 0,
        native: Some(context),
        result_move: None,
        temp_definitions,
        nil_group_members,
        pending_nil_group: None,
        deferred_method_events: BTreeSet::new(),
        boolean_frame: None,
    })
}

/// 空声明只能连同原帧退休；真实 nil、源码调试身份和显式保留义务不可过滤。
fn removable_empty_declaration(
    proto: &HirProto,
    original_nil: &BTreeSet<LocalId>,
    decl: &HirLocalDecl,
) -> bool {
    !decl.bindings.is_empty()
        && decl.values.is_empty()
        && decl.initializer_merge_transaction.is_none()
        && decl.bindings.iter().all(|local| {
            !original_nil.contains(local)
                && proto.local_debug_hints[local.index()].is_none()
                && proto.local_debug_scopes[local.index()].is_none()
                && !proto.inline_dispositions.local(*local).must_preserve()
        })
}

/// 每个直线构造区只选择最后一个符合原分配形状的终点，不逐字段重建候选树。
fn constructor_ends(
    flat: &[Option<FlatStmt<'_>>],
    empty: &BTreeSet<usize>,
) -> BTreeMap<usize, usize> {
    let mut ends = BTreeMap::new();
    let mut definitions = BTreeMap::new();
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            definitions.clear();
            continue;
        };
        if empty.contains(&entry.id) {
            continue;
        }
        if let Some((local, value)) = scalar_local(entry.stmt) {
            // initializer 之外的读取（含闭包捕获）结束该 seed 的待构造窗口。
            // 先前已收集的字段终点仍有效，后续普通写不能扩大它并遮挡独立子构造器。
            crate::hir::visit::visit_expr(
                value,
                &mut BindingReadCollector(|binding| {
                    if let HirBinding::Local(read) = binding {
                        definitions.remove(&read);
                    }
                }),
            );
            if let HirExpr::TableConstructor(table) = value {
                definitions.insert(local, (index, tables::ConstructorShape::new(table)));
            } else {
                definitions.remove(&local);
            }
            continue;
        }
        if let Some(write) = super::super::table_constructors::constructor_write(entry.stmt) {
            let super::super::table_constructors::TableBinding::Local(local) = write.binding()
            else {
                continue;
            };
            if let Some((seed, shape)) = definitions.get_mut(&local) {
                if !shape.push(&write) {
                    // 后续方法安装等普通写不能遮住已经完整的 initializer。
                    definitions.remove(&local);
                } else if shape.complete() {
                    ends.insert(*seed, index);
                }
            }
        } else {
            definitions.clear();
        }
    }
    ends
}
/// 独立构造器也由相同槽/事件 owner 消费 callee COPY，不能留下永久的临时根。
/// 原调用参数区中的表必须等待包含接收 CALL 的事务；拆掉它会抬高接收 caller top。
fn collect_constructor_plans(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt_count: &mut usize,
    plans: &mut Vec<Plan>,
) {
    use crate::hir::visit::HirVisitor;
    struct Arguments<'a> {
        facts: &'a ProtoPromotionFacts,
        owned: BTreeSet<LocalId>,
    }
    impl HirVisitor<'_> for Arguments<'_> {
        fn visit_call(&mut self, call: &HirCallExpr) {
            self.owned
                .extend(call.argument_roots.iter().filter_map(|root| {
                    let local = self.facts.promoted_local_for_temp(root.producer)?;
                    // 历史 COPY 的 Temp 可与后继构造 seed 共用 LocalId；只有当前
                    // 参数仍读取该 binding，才把其当前定义预留给 CALL 事务。
                    call.args
                        .fixed
                        .get(root.argument)
                        .is_some_and(|value| {
                            super::super::mention::expr_mentions_local(value, local)
                        })
                        .then_some(local)
                }));
            let Some(frame) = self.facts.native_call_layout(call) else {
                return;
            };
            let start = match frame.args {
                ValuePack::Fixed(pack) => pack.start,
                ValuePack::Open(start) => start,
            };
            let implicit_receiver = usize::from(call.method == HirMethodCall::Implicit);
            for (offset, value) in call.args.fixed.iter().enumerate() {
                if let HirExpr::LocalRef(local) = value
                    && self.facts.trusted_local_home_slot(*local)
                        == Some(HomeSlotKey::new(
                            start.index() + implicit_receiver + offset,
                            0,
                        ))
                {
                    self.owned.insert(*local);
                }
            }
        }
    }
    let mut arguments = Arguments {
        facts,
        owned: BTreeSet::new(),
    };
    let mut flat = Vec::new();
    flatten_scope(&context.proto.body, stmt_count, &mut flat);
    // LocalId 可承接后续值版本；只给 CALL 实际读取的定义预留参数事务，
    // 后面复用同槽的参数不能反向占有前面已写入外部表的构造器。
    let mut definitions = BTreeMap::new();
    let mut argument_definitions = BTreeSet::new();
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            definitions.clear();
            continue;
        };
        arguments.owned.clear();
        crate::hir::visit::visit_stmt_header(entry.stmt, &mut arguments);
        argument_definitions.extend(
            arguments
                .owned
                .iter()
                .filter_map(|local| definitions.get(local).copied()),
        );
        crate::hir::visit::visit_stmt_header(
            entry.stmt,
            &mut BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    definitions.insert(local, index);
                }
            }),
        );
    }
    let original_nil_locals = facts
        .nil_write_groups()
        .flat_map(|group| {
            group
                .iter()
                .filter_map(|temp| facts.promoted_local_for_temp(*temp))
        })
        .collect::<BTreeSet<_>>();
    let empty = flat
        .iter()
        .filter_map(|entry| {
            let entry = entry.as_ref()?;
            let HirStmt::LocalDecl(decl) = entry.stmt else {
                return None;
            };
            removable_empty_declaration(context.proto, &original_nil_locals, decl)
                .then_some(entry.id)
        })
        .collect::<BTreeSet<_>>();
    // 每个直线构造区只在最后一次 record 写审理，避免对逐渐增长的字段前缀重复建树。
    let rk_prefix_end = tables::rk_prefix_end(context.proto);
    let ends = constructor_ends(&flat, &empty);
    let mut grouped = declarations::collect(
        context,
        facts,
        dialect,
        &flat,
        &empty,
        &ends,
        &argument_definitions,
    );
    grouped.extend(declarations::collect_calls(
        context, facts, dialect, &flat, &empty,
    ));
    grouped.extend(declarations::collect_comparisons(
        context, facts, dialect, &flat,
    ));
    let debug_groups = declarations::collect_debug_groups(context, facts, dialect, &flat);
    let debug_statements = debug_groups
        .iter()
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    grouped.retain(|plan| {
        !debug_statements.contains(&plan.sink)
            && plan
                .removed
                .iter()
                .all(|index| !debug_statements.contains(index))
    });
    grouped.extend(debug_groups);
    let grouped_statements = grouped
        .iter()
        .flat_map(|plan| plan.removed.iter().copied().chain([plan.sink]))
        .collect::<BTreeSet<_>>();
    plans.extend(grouped);
    let mut first_seed = None;
    let mut start = 0;
    for (index, entry) in flat.iter().enumerate() {
        let Some(entry) = entry else {
            first_seed = None;
            start = index + 1;
            continue;
        };
        if empty.contains(&entry.id) {
            continue;
        }
        if grouped_statements.contains(&entry.id) {
            first_seed = None;
            start = index + 1;
            continue;
        }
        if first_seed.is_none()
            && ends.contains_key(&index)
            && let Some((local, HirExpr::TableConstructor(_))) = scalar_local(entry.stmt)
        {
            first_seed = Some((index, local));
        }
        if let Some(write) = super::super::table_constructors::constructor_write(entry.stmt)
            && let super::super::table_constructors::TableBinding::Local(local) = write.binding()
            && let Some((seed, owner)) = first_seed
            && owner == local
            && ends.get(&seed) == Some(&index)
        {
            let context = NativeFrameContext {
                constants_fit_rk: context.constants_fit_rk
                    || flat
                        .get(index + 1)
                        .and_then(|entry| *entry)
                        .is_some_and(|next| next.id < rk_prefix_end),
                ..context
            };
            if !argument_definitions.contains(&seed)
                && let Some(base) = facts.trusted_local_home_slot(owner)
            {
                // 构造器 owner 留下的空声明没有求值事件；只从 builder 输入过滤，
                // 原坐标仍进入 removed，由整批 preview 核对后续每个 read/capture/重新声明。
                let run = flat[start..=index]
                    .iter()
                    .filter(|entry| !empty.contains(&entry.as_ref().unwrap().id))
                    .map(|entry| entry.as_ref().unwrap().stmt)
                    .collect::<Vec<_>>();
                let seed_in_run = flat[start..seed]
                    .iter()
                    .filter(|entry| !empty.contains(&entry.as_ref().unwrap().id))
                    .count();
                if let Some(next) = flat.get(index + 1).and_then(|entry| *entry)
                    && let Some(mut plan) = conditional_value_initializer(
                        context,
                        &run,
                        facts,
                        dialect,
                        seed_in_run,
                        next.stmt,
                    )
                {
                    plan.start = flat[seed].unwrap().id;
                    plan.sink = next.id;
                    plan.removed = flat[seed..=index]
                        .iter()
                        .map(|entry| entry.unwrap().id)
                        .collect();
                    plans.push(plan);
                    first_seed = None;
                    start = index + 2;
                    continue;
                }
                if let Some(mut builder) = frame_builder(context, &run, facts, dialect, base.slot())
                    && let HirExpr::TableConstructor(table) =
                        scalar_local(run[seed_in_run]).unwrap().1
                    && (!matches!(table.allocation, HirTableAllocation::PucBatched(_))
                        || facts.allocation_result_home(table) == Some(base))
                    && let Some(value) = builder.constructor(seed_in_run, table, base.slot())
                    && builder.next_event == run.len()
                {
                    let global_sink = flat.get(index + 1).and_then(|entry| {
                        let next = (*entry)?;
                        let HirStmt::Assign(assign) = next.stmt else {
                            return None;
                        };
                        let (
                            [target @ HirLValue::Global(global)],
                            [HirExpr::LocalRef(source)],
                            None,
                        ) = (
                            assign.targets.as_slice(),
                            assign.values.fixed.as_slice(),
                            &assign.values.tail,
                        )
                        else {
                            return None;
                        };
                        (*source == owner
                            && (context.constants_fit_rk || dialect == DecompileDialect::Lua51)
                            && facts.global_write_value_home(global, dialect) == Some(base)
                            && context.proto.local_debug_hints[owner.index()].is_none()
                            && context.proto.local_debug_scopes[owner.index()].is_none()
                            && !assign.is_phi_transfer
                            && assign.initializer_merge_transaction.is_none()
                            && assign.generic_for_initializer_producer.is_none()
                            && assign.generic_for_dispatch_release.is_none()
                            && assign.method_rewrite_transaction.is_none())
                        .then_some((next.id, target.clone()))
                    });
                    let removed_end = index + usize::from(global_sink.is_some());
                    // 原匿名槽可被下一构造器复用；旧声明必须由整批事务退休，
                    // 前缀预览未证明新声明正好落回原 allocation home 时拒绝。
                    // 紧邻环境写没有左值准备区；连同该写提交，避免先保留 seed 声明
                    // 抬高后继 CALL 的基址。后缀每次覆盖仍由同一 preview 验证。
                    plans.push(Plan {
                        prefix_at_sink: false,
                        luau_function_declaration: false,
                        start: flat[seed].unwrap().id,
                        sink: global_sink.as_ref().map_or(entry.id, |(id, _)| *id),
                        base,
                        values: vec![value].into(),
                        result_locals: if global_sink.is_some() {
                            Vec::new()
                        } else {
                            vec![owner]
                        },
                        discarded_result: None,
                        assignment_targets: global_sink
                            .into_iter()
                            .map(|(_, target)| target)
                            .collect(),
                        luau_compound_global: false,
                        indexed_target: None,
                        continuing_root: None,
                        retained_copies: Vec::new(),
                        replayed_effects: Vec::new(),
                        removed: flat[seed..removed_end]
                            .iter()
                            .map(|entry| entry.unwrap().id)
                            .collect(),
                    });
                }
            }
            first_seed = None;
            start = index + 1;
        } else if scalar_local(entry.stmt).is_none()
            && super::super::table_constructors::constructor_write(entry.stmt).is_none()
        {
            first_seed = None;
            start = index + 1;
        }
    }
}

/// 短路 CALL 树共同重发准备区与结果声明；右臂没有无条件事件可消费。
/// Luau initializer 消费保留的原结果身份，按值/条件位置分别核对叶 CALL；
/// 后继异槽 Phi/COPY 仍由独立返回事务消费，不能从首个 predicate CALL 推测结果 home。
fn logical_call_result_frame(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt: &HirStmt,
    prewrite: Option<(TempId, TempId, HomeSlotKey, bool)>,
    split_initializer: bool,
) -> Option<Plan> {
    let (target, value) = scalar_local(stmt)?;
    let assignment = dialect == DecompileDialect::Luau && matches!(stmt, HirStmt::Assign(_));
    if assignment
        && matches!(stmt, HirStmt::Assign(assign)
        if assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.generic_for_dispatch_release.is_some()
            || assign.method_rewrite_transaction.is_some())
    {
        return None;
    }
    let mut first = value;
    while let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = first {
        first = &logical.lhs;
    }
    let first_value = if let HirExpr::LocalRef(local) = first {
        run.iter()
            .rev()
            .find_map(|stmt| {
                scalar_local(stmt)
                    .filter(|(written, _)| written == local)
                    .map(|(_, value)| value)
            })
            .unwrap_or(first)
    } else {
        first
    };
    let lookup_initializer = matches!(stmt, HirStmt::LocalDecl(_))
        && matches!(first_value, HirExpr::TableAccess(_) | HirExpr::GlobalRef(_));
    let base = if assignment {
        // 已有目标在完整 RHS 求值后才写回。最右叶被选中时直接产出表达式的值，
        // 取其原 CALL 帧作为候选结果槽；builder 再核对全部值叶、谓词叶和实际前缀。
        // 不能拿首个只用于真假测试的 CALL 槽当结果槽，也不能把现存目标当 initializer。
        let mut result = value;
        while let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = result {
            result = &logical.rhs;
        }
        let HirExpr::Call(result) = result else {
            return None;
        };
        facts.native_call_frame(result)?.home
    } else if dialect == DecompileDialect::Luau {
        facts.trusted_local_home_slot(target)?
    } else {
        match first_value {
            HirExpr::Call(call) => facts.native_call_frame(call)?.home,
            HirExpr::TableAccess(access) if lookup_initializer => {
                facts.table_read_result_home(access)?
            }
            HirExpr::GlobalRef(global) if lookup_initializer => {
                facts.global_read_frame(global, dialect)?
            }
            HirExpr::Unary(unary) if unary.op == crate::hir::common::HirUnaryOpKind::Neg => {
                facts.unary_result_home(unary)?
            }
            _ => return None,
        }
    };
    // 候选拒绝[ProofIncomplete]：异槽结果需要保留逐路径的原 COPY 写回，不能只凭值相等合并。
    if (context.barred.contains(&base) && !split_initializer)
        || context.closed.contains(&base)
        || if assignment {
            // 原目标声明和写入位置都保留，允许它是 debug 或 captured cell；这里只
            // 消费 RHS 的高槽准备。目标必须已经位于候选帧以下，不能借此创建身份。
            facts.trusted_local_home_slot(target)?.slot() >= base.slot()
        } else {
            facts.trusted_local_home_slot(target) != Some(base)
                || (!matches!(stmt, HirStmt::LocalDecl(_))
                    && (context.proto.local_debug_hints[target.index()].is_some()
                        || context.proto.local_debug_scopes[target.index()].is_some()
                        || context
                            .proto
                            .inline_dispositions
                            .local(target)
                            .must_preserve()))
                || !facts
                    .complete_local_definition_write_homes(target)
                    .iter()
                    .copied()
                    .eq(std::iter::once(base))
        }
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let value = if dialect == DecompileDialect::Luau {
        if let Some(prewrite) = prewrite {
            // 外层预写先于内部比较操作数的准备；整棵 initializer 一起消费，
            // 不能只寻找紧邻结果的最后一个 Boolean 声明。
            builder.consume_boolean_prewrite(
                prewrite,
                facts.temp_definition_reference_unaliased(prewrite.0),
                value,
                run.len(),
                base.slot(),
            )?;
        }
        builder.luau_logical_value(value, run.len(), base)?
    } else {
        builder.comparison_tree(value, run.len(), base.slot(), lookup_initializer)?
    };
    // 空声明与紧邻赋值的合并也有实际消费项；表达式本身已经完整时无需
    // 强求额外准备事件。caller 仍将该声明纳入同一 prefix preview。
    if context.barred.contains(&base) && builder.first_event.is_some() {
        return None;
    }
    let start = builder
        .first_event
        .or_else(|| split_initializer.then_some(run.len()))?;
    if builder.first_event.is_some() && builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: if assignment { Vec::new() } else { vec![target] },
        discarded_result: None,
        assignment_targets: if assignment {
            vec![HirLValue::Local(target)]
        } else {
            Vec::new()
        },
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

fn operation_call_input<'a>(
    value: &'a HirExpr,
    facts: &ProtoPromotionFacts,
) -> Option<(crate::hir::common::HirSourceSite, &'a HirExpr, bool)> {
    match value {
        HirExpr::Binary(binary) if numeric_rk_arithmetic(binary) => {
            Some((binary.source_site?, &binary.lhs, false))
        }
        HirExpr::Binary(binary) => {
            use crate::hir::common::HirBinaryOpKind::{Add, Div, Mod, Mul, Pow, Sub};
            if !matches!(binary.op, Add | Sub | Mul | Div | Mod | Pow) {
                return None;
            }
            let source = binary.source_site?;
            let result = facts.operation_result_home(source)?;
            let layout = facts.native_binary_layout(binary)?;
            // 原地累计读取已有低槽，只有右操作数在高槽准备；不交换两侧求值。
            (layout.lhs == Some(result) && layout.rhs.is_some_and(|rhs| rhs.slot() > result.slot()))
                .then_some((source, &binary.rhs, true))
        }
        HirExpr::Unary(unary)
            if matches!(
                unary.op,
                crate::hir::HirUnaryOpKind::Neg | crate::hir::HirUnaryOpKind::Not
            ) =>
        {
            let source = unary.source_site?;
            let result = facts.operation_result_home(source)?;
            // 这里只恢复高槽准备写回低结果；普通低槽输入不是候选，不能抢占
            // 同一区间中后继 NOT/NEG 的尝试额度。
            (facts.unary_operand_home(unary)?.slot() > result.slot()).then_some((
                source,
                &unary.expr,
                false,
            ))
        }
        _ => None,
    }
}

fn operation_target(stmt: &HirStmt) -> Option<(HirLValue, &HirExpr)> {
    if matches!(stmt, HirStmt::Assign(assign)
        if assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.generic_for_dispatch_release.is_some()
            || assign.method_rewrite_transaction.is_some())
    {
        return None;
    }
    if let Some((local, value)) = scalar_local(stmt) {
        return Some((HirLValue::Local(local), value));
    }
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    match (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) {
        ([target @ HirLValue::Param(_)], [value], None) => Some((target.clone(), value)),
        _ => None,
    }
}

/// SETUPVAL/直接环境写不占用左值准备槽；完整 RHS 在原结果槽求值后写回。
fn external_operation_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt: &HirStmt,
) -> Option<Plan> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let (
        [target @ (HirLValue::Upvalue(_) | HirLValue::Global(_))],
        [value @ HirExpr::Binary(binary)],
        None,
    ) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    )
    else {
        return None;
    };
    let base = facts.operation_result_home(binary.source_site?)?;
    if let HirLValue::Global(global) = target
        && facts.global_write_value_home(global, dialect) != Some(base)
    {
        return None;
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let value = builder.expr(value, run.len(), base.slot(), None, false, true, None)?;
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![target.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 声明 initializer 在原结果槽计算整棵运算树；保留声明本身及 debug 身份，
/// 只消费共享 builder 已证明的操作数准备，不能把原 CALL 跨过左侧算术事件。
fn operation_initializer_plan(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt: &HirStmt,
    following_floor: Option<usize>,
    split_initializer: bool,
) -> Option<Plan> {
    if matches!(stmt, HirStmt::Assign(_)) && operation_target(stmt).is_none() {
        return None;
    }
    let (target, value) = scalar_local(stmt)?;
    let source = match value {
        HirExpr::Binary(binary) => binary.source_site?,
        HirExpr::Unary(unary) => unary.source_site?,
        _ => return None,
    };
    let base = match value {
        HirExpr::Binary(binary) if facts.comparison_result_temp(binary).is_some() => {
            let result = facts.comparison_result_temp(binary)?;
            if facts.promoted_local_for_temp(result) != Some(target) {
                return None;
            }
            facts.trusted_temp_home_slot(result)?
        }
        _ => facts.operation_result_home(source)?,
    };
    if facts.trusted_local_home_slot(target) != Some(base) {
        return None;
    }
    if following_floor.is_some_and(|floor| base.slot() >= floor)
        && context.proto.local_debug_hints[target.index()].is_none()
        && context.proto.local_debug_scopes[target.index()].is_none()
        && !context.barred.contains(&base)
    {
        // 匿名运算结果仍可能是后继低槽 CALL 的参数；先独立提交会截断完整准备区。
        // debug/capture 的既有身份必须保留，其余结果留给外层帧共同消费。
        return None;
    }
    if split_initializer && let Some(scope) = context.proto.local_debug_scopes[target.index()] {
        let scope = context.proto.debug_scopes[scope]?;
        let HirExpr::Binary(binary) = value else {
            return None;
        };
        let result = facts.comparison_result_temp(binary)?;
        if scope.initializer_temp != Some(result) && scope.initializer_phi != Some(result) {
            // 候选拒绝[SemanticBarrier:DebugScope]：真实空声明的后续赋值不能伪装成原 initializer。
            return None;
        }
    }
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    // 比较结果低于后继帧时已经有独立的源码槽，匿名 binding 也可保留它；
    // 位于后继准备区的结果仍留给外层帧。展开 owner 则另验证全部后缀。
    // 同槽计算结果即使因后续槽复用进入 barred，也不代表独立源码身份；
    // 仍须后继帧下界或实际 debug 绑定，不能先截断 assert(call() == value)。
    if let HirExpr::Binary(binary) = value
        && facts.comparison_result_temp(binary).is_some()
        && !(builder.in_place_comparison_input(binary, run.len(), base.slot())
            && (following_floor.is_some_and(|floor| base.slot() < floor)
                || context.proto.local_debug_hints[target.index()].is_some()
                || context.proto.local_debug_scopes[target.index()].is_some()))
        && !builder.low_left_comparison_rhs(binary, run.len(), base.slot(), true)
        && builder
            .luau_arithmetic_comparison_operand(binary, run.len(), base.slot())
            .is_none()
        && !(builder
            .luau_comparison_preparations(binary, run.len(), base.slot())
            .is_some()
            && (context.expanded_callees.is_some()
                || following_floor.is_some_and(|floor| base.slot() < floor)
                || context.proto.local_debug_hints[target.index()].is_some()
                || context.proto.local_debug_scopes[target.index()].is_some()))
    {
        return None;
    }
    let value = builder.expr(value, run.len(), base.slot(), None, false, true, None)?;
    // 输入已完整树化时仍可消费相邻的合成空声明；没有声明事务则必须有准备事件。
    let start = builder
        .first_event
        .or_else(|| split_initializer.then_some(run.len()))?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: vec![target],
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原输入在高槽求值，算术或一元运算随后写低结果槽；参数和现存 local 不新增声明。
/// 两侧输入保持原顺序与 Def，Luau initializer 另保持预留结果槽的入口。
fn operation_input_frame(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    stmt: &HirStmt,
    following_floor: Option<usize>,
) -> Option<Plan> {
    let (target, value) = operation_target(stmt)?;
    let (source, operand, right_input) = operation_call_input(value, facts)?;
    let base = facts.operation_result_home(source)?;

    if let HirLValue::Local(local) = target
        && matches!(stmt, HirStmt::LocalDecl(_))
        && context.proto.local_debug_hints[local.index()].is_none()
        && context.proto.local_debug_scopes[local.index()].is_none()
        && following_floor.is_some_and(|floor| base.slot() >= floor)
    {
        // 候选拒绝[PolicyBoundary]：匿名算术结果仍在后继完整帧的准备区，
        // 不能先冻结声明并截断 CALL → 算术 → Boolean 的共同求值事务。
        return None;
    }
    let result = facts.operation_result_temp(source)?;
    let input_home = match value {
        HirExpr::Binary(binary) => {
            let layout = facts.native_binary_layout(binary)?;

            if right_input {
                layout.rhs?
            } else {
                let sources = crate::hir::common::HirOperationSources::Single(source);
                if layout.rhs.is_some()
                    || !(dialect == DecompileDialect::Luau && context.constants_fit_rk
                        || context.literal_uses_rk(&binary.rhs, Some((&sources, true)), dialect)
                            == Some(true))
                {
                    return None;
                }
                layout.lhs?
            }
        }
        HirExpr::Unary(unary) => facts.unary_operand_home(unary)?,
        _ => return None,
    };
    // Luau initializer 预留低结果槽；已有 local 赋值从空闲高槽准备，再写低目标。
    // 后者不能新增目标声明，否则会把 CALL 的临时身份永久留给后续 table allocation。
    // JIT 的 FR2 间隙仍由共享 call builder 核对，不由算术消费方另外计算。
    let boolean_not = matches!(value, HirExpr::Unary(unary)
        if unary.op == crate::hir::HirUnaryOpKind::Not);
    let assignment =
        dialect != DecompileDialect::Luau || right_input || matches!(stmt, HirStmt::Assign(_));
    if (assignment && (!matches!(stmt, HirStmt::Assign(_)) || base.slot() >= input_home.slot()))
        || (!assignment && input_home != HomeSlotKey::new(base.slot() + 1, 0))
    {
        return None;
    }
    let frame_base = if assignment { input_home } else { base };
    let target_home = match target {
        HirLValue::Local(local) => {
            // 赋值保留低槽目标的声明和 debug 身份；只有新 initializer 才消费目标声明。
            if !assignment
                && (context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some()
                    || context
                        .proto
                        .inline_dispositions
                        .local(local)
                        .must_preserve())
            {
                return None;
            }
            facts.trusted_local_home_slot(local)?
        }
        HirLValue::Param(param) if assignment => facts.trusted_param_home_slot(param)?,
        _ => return None,
    };
    if target_home != base || context.closed.contains(&base) {
        return None;
    }
    let mut complete = run.to_vec();
    let local_target = matches!(target, HirLValue::Local(_));
    // Local 的当前写参与 definition 索引；参数已有固定身份，只核对原结果 Def，
    // 不把参数写伪装成可以消费的临时定义。两者都保留在 sink 原位提交。
    if local_target {
        complete.push(stmt);
    }
    let mut builder = frame_builder(context, &complete, facts, dialect, frame_base.slot())?;
    if right_input {
        let HirExpr::Binary(binary) = value else {
            return None;
        };
        if builder.direct_home(&binary.lhs) != Some(base) {
            return None;
        }
    }
    let input = match operand {
        HirExpr::LocalRef(local) => scalar_local(run[builder.definition(*local, run.len())?])?.1,
        value => value,
    };
    // NOT 不调用元方法；两个原 NOT 按原高槽准备、低槽写回重发，期间没有回调
    // 能观察捕获 cell。其它运算仍保留捕获屏障，不能借此提前其写回。
    let not_pair = boolean_not
        && matches!(input, HirExpr::Unary(unary)
        if unary.op == crate::hir::HirUnaryOpKind::Not);
    if context.barred.contains(&base) && !not_pair {
        return None;
    }
    if !matches!(input, HirExpr::Call(_))
        && !not_pair
        && !(assignment
            && dialect != DecompileDialect::Luajit
            && matches!(input, HirExpr::Binary(_) | HirExpr::TableAccess(_)))
    {
        return None;
    }
    let (producer, home) = facts.operation_input_preparation(source, input)?;

    if home != input_home
        || if assignment {
            // 既有目标可由循环 Phi 绑定；原运算 Def 不必被提升为同一个 LocalId。
            // 此处保留原赋值，只核对该 Def 的全部写仍落在已验证的目标 home。
            !facts
                .complete_temp_definition_write_homes(result)
                .iter()
                .copied()
                .eq([base])
        } else {
            match target {
                HirLValue::Local(local) => {
                    !builder.homes_match(local, run.len(), base.slot(), None, Some(result))
                }
                HirLValue::Param(_) => !facts
                    .complete_temp_definition_write_homes(result)
                    .iter()
                    .copied()
                    .eq([base]),
                _ => return None,
            }
        }
    {
        return None;
    }
    let input = builder.expr(
        operand,
        run.len(),
        home.slot(),
        None,
        false,
        true,
        Some(producer),
    )?;

    if local_target {
        builder.finish_event(run.len())?;
    }
    let first = builder.first_event?;
    if first == run.len() || builder.next_event != complete.len() {
        return None;
    }
    let value = match value {
        HirExpr::Binary(binary) => {
            let mut rebuilt = binary.as_ref().clone();
            if right_input {
                rebuilt.rhs = input;
            } else {
                rebuilt.lhs = input;
            }
            HirExpr::Binary(Box::new(rebuilt))
        }
        HirExpr::Unary(unary) => HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
            expr: input,
            ..unary.as_ref().clone()
        })),
        _ => return None,
    };
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: first,
        sink: run.len(),
        base: frame_base,
        values: vec![value].into(),
        result_locals: if assignment {
            Vec::new()
        } else {
            let HirLValue::Local(local) = target else {
                unreachable!();
            };
            vec![local]
        },
        discarded_result: None,
        assignment_targets: if assignment { vec![target] } else { Vec::new() },
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原退化 TEST 在完整 initializer 中重发；只穿过其空臂自己的边界，不能跨外层作用域。
fn conditional_initializer_tail<'a>(
    flat: &[Option<FlatStmt<'a>>],
    seed: usize,
    owner: LocalId,
) -> Option<(usize, FlatStmt<'a>)> {
    let next = flat.get(seed + 1).copied().flatten()?;
    let HirStmt::If(branch) = next.stmt else {
        return Some((seed + 1, next));
    };
    let test = match &branch.cond {
        HirExpr::Unary(unary) if unary.op == crate::hir::HirUnaryOpKind::Not => &unary.expr,
        expr => expr,
    };
    if !branch.preserves_empty_test
        || *test != HirExpr::LocalRef(owner)
        || !branch.then_block.stmts.is_empty()
        || branch
            .else_block
            .as_ref()
            .is_some_and(|arm| !arm.stmts.is_empty())
    {
        return None;
    }
    let result = seed + 3 + usize::from(branch.else_block.is_some());
    if flat.get(seed + 2..result)?.iter().any(Option::is_some) {
        return None;
    }
    Some((result, flat.get(result).copied().flatten()?))
}

/// 原表或 CALL 测试后写入标量结果，才恢复完整条件表达式帧。
/// 当前声明和值版本必须同时匹配；无事件叶的原写证明由 Promotion 提供。
fn conditional_value_initializer(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    seed: usize,
    result_stmt: &HirStmt,
) -> Option<Plan> {
    let (owner, input) = scalar_local(run[seed])?;
    let (target, value) = scalar_local(result_stmt)?;
    let original = match input {
        HirExpr::TableConstructor(table) => facts.table_value_result(table)?,
        HirExpr::Call(call) => facts.conditional_value_result(call.source_site?)?,
        _ => return None,
    };
    let base = facts.trusted_temp_home_slot(original.result)?;
    let home = facts.trusted_temp_home_slot(original.input)?;
    let same_slot = home == base;
    if !original.value.matches_hir_expr(value)
        || if dialect == DecompileDialect::Luau {
            home != HomeSlotKey::new(base.slot() + 1, 0)
        } else {
            !same_slot || original.writes != [Some(original.result), None]
        }
        || facts.promoted_local_for_temp(original.input) != Some(owner)
        || facts.promoted_local_for_temp(original.result) != Some(target)
        || facts.trusted_local_home_slot(target) != Some(base)
        || [base, home]
            .iter()
            .any(|home| context.barred.contains(home) || context.closed.contains(home))
        || context.proto.local_debug_hints[owner.index()].is_some()
        || context.proto.local_debug_scopes[owner.index()].is_some()
        || context
            .proto
            .inline_dispositions
            .local(owner)
            .must_preserve()
        || context
            .proto
            .inline_dispositions
            .local(target)
            .must_preserve()
        || ((context.proto.local_debug_hints[target.index()].is_some()
            || context.proto.local_debug_scopes[target.index()].is_some())
            && context.proto.local_debug_scopes[target.index()]
                .and_then(|scope| context.proto.debug_scopes.get(scope).copied().flatten())
                .and_then(|scope| scope.initializer_temp)
                != Some(original.result))
    {
        return None;
    }
    let mut complete = run.to_vec();
    complete.push(result_stmt);
    let mut builder = frame_builder(context, &complete, facts, dialect, base.slot())?;
    if !builder.homes_match(owner, seed, home.slot(), None, Some(original.input))
        || !builder.homes_match(target, run.len(), base.slot(), None, Some(original.result))
    {
        return None;
    }
    let input = match input {
        HirExpr::TableConstructor(table) => builder.constructor(seed, table, home.slot())?,
        HirExpr::Call(call) if seed + 1 == run.len() => {
            let call = builder.call(call, seed, home.slot(), false, CallWidth::Single)?;
            builder.finish_event(seed)?;
            HirExpr::Call(Box::new(call))
        }
        _ => return None,
    };
    builder.finish_event(run.len())?;
    if builder.next_event != complete.len() {
        return None;
    }
    let value = value.clone();
    let selected = HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: input,
        // PUC/JIT 的退化 TEST 与结果覆盖共用一槽，false 叶不产生额外写；
        // Luau 的高槽谓词则沿原双叶协议，输入根继续由后缀事务保持。
        rhs: if same_slot {
            HirExpr::Boolean(false)
        } else {
            value.clone()
        },
    }));
    let value = HirExpr::LogicalOr(Box::new(crate::hir::common::HirLogicalExpr {
        preserves_boolean_prewrite: false,
        lhs: selected,
        rhs: value,
    }));
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: builder.first_event?,
        sink: run.len(),
        base,
        values: vec![value].into(),
        result_locals: vec![target],
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: (!same_slot).then_some(original),
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 原 table 临时位于新标量声明之上；整个 initializer 重放 table/SETLIST/GETTABLE，
/// 不给 scratch 留下永久声明。旧身份的其它 read/capture 仍由同一 preview 拒绝。
/// 低于后续原 CALL 或作为后继 SETTABLE 的稳定低槽表，可成为独立索引声明；
/// 中间 base/key 由同一读取帧完整消费，原唯一目标快照则留给 indexed 事务。
fn lookup_initializer(
    context: NativeFrameContext<'_>,
    run: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    target: Option<LocalId>,
    access: &crate::hir::common::HirTableAccess,
    home: HomeSlotKey,
) -> Option<Plan> {
    let mut builder = frame_builder(context, run, facts, dialect, home.slot())?;
    let value = if dialect == DecompileDialect::Luau {
        builder.luau_lookup(access, run.len(), home.slot())?
    } else {
        builder.register_lookup(access, run.len(), home.slot())?
    };
    let start = builder.first_event?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink: run.len(),
        base: home,
        values: vec![value].into(),
        result_locals: target.into_iter().collect(),
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

fn scalar_array_lookup_plan(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
    producer: &HirStmt,
    sink: &HirStmt,
    original_call_floor: Option<usize>,
) -> Option<Plan> {
    let (source, HirExpr::TableConstructor(table)) = scalar_local(producer)? else {
        return None;
    };
    let HirStmt::LocalDecl(decl) = sink else {
        return None;
    };
    let ([target], [HirExpr::TableAccess(access)], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let base = facts.trusted_local_home_slot(*target)?;
    // 与普通 CALL initializer 共用后续原调用下界；无已证窗口时保留 scratch。
    // 参数/操作数区必须等待包含接收 CALL 的完整事务，不能先冻结一个永久 local。
    if base.slot() >= original_call_floor? {
        return None;
    }
    let source_home = facts.trusted_local_home_slot(source)?;
    let homes = facts.complete_local_definition_write_homes(source);
    if !matches!(access.base, HirExpr::LocalRef(local) if local == source)
        || source == *target
        || context
            .proto
            .local_debug_hints
            .get(source.index())
            .is_some_and(Option::is_some)
        || context
            .proto
            .local_debug_scopes
            .get(source.index())
            .is_some_and(Option::is_some)
        || context
            .proto
            .inline_dispositions
            .local(source)
            .must_preserve()
        || (context.barred.contains(&source_home)
            && !facts.allocation_result_reference_unaliased(table))
        || homes.iter().any(|home| *home != source_home)
        || !homes.is_disjoint(context.closed)
        || facts.allocation_result_home(table) != Some(source_home)
    {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start: 0,
        sink: 0,
        base,
        values: vec![tables::scalar_array_lookup(facts, table, access, base)?].into(),
        result_locals: vec![*target],
        discarded_result: None,
        assignment_targets: Vec::new(),
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

struct ConcatAssignment<'a> {
    target: &'a HirLValue,
    binary: &'a crate::hir::common::HirBinaryExpr,
    target_home: HomeSlotKey,
    base: HomeSlotKey,
    separate_result: bool,
}

fn concat_assignment_source<'a>(
    stmt: &'a HirStmt,
    previous: Option<&'a HirStmt>,
    facts: &ProtoPromotionFacts,
) -> Option<ConcatAssignment<'a>> {
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let ([target], [value], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let target_home = match target {
        HirLValue::Local(local) => facts.trusted_local_home_slot(*local)?,
        HirLValue::Param(param) => facts.trusted_param_home_slot(*param)?,
        _ => return None,
    };
    let separate_result = matches!(value, HirExpr::LocalRef(_));
    let value = if let HirExpr::LocalRef(source) = value {
        let (local, value) = scalar_local(previous?)?;
        if local != *source {
            return None;
        }
        value
    } else {
        value
    };
    let HirExpr::Binary(binary) = value else {
        return None;
    };
    if binary.op != crate::hir::common::HirBinaryOpKind::Concat {
        return None;
    }
    let buffer = facts.native_concat_buffer(binary)?;
    let base = HomeSlotKey::new(buffer.start.index(), 0);
    (target_home.slot() < base.slot()).then_some(ConcatAssignment {
        target,
        binary,
        target_home,
        base,
        separate_result,
    })
}

/// CONCAT 输入区先完整求值，再更新既有低槽；PUC 5.4 的独立结果 COPY 同批提交。
fn concat_assignment(
    context: NativeFrameContext<'_>,
    stmts: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    assignment: ConcatAssignment<'_>,
) -> Option<Plan> {
    let ConcatAssignment {
        target,
        binary,
        target_home,
        base,
        separate_result,
    } = assignment;
    let sink = stmts.len().checked_sub(1)?;
    let producer = sink.checked_sub(usize::from(separate_result))?;
    let site = binary.source_site?;
    let result = facts.operation_result_home(site)?;
    let temp = facts.operation_result_temp(site)?;
    if (result != target_home && result != base)
        || facts
            .complete_temp_definition_write_homes(temp)
            .iter()
            .any(|home| *home != result && *home != target_home)
    {
        return None;
    }
    let run = &stmts[..producer];
    let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
    let value = builder.concat_in_frame(binary, run.len(), base.slot(), result)?;
    let start = builder
        .first_event
        .or(separate_result.then_some(producer))?;
    if builder.next_event != run.len() {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink,
        base,
        values: vec![value].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![target.clone()],
        luau_compound_global: false,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 完整分配、运算或直接全局/上值读取在 freereg 求值，再写入原目标；只消除紧邻声明。
/// upvalue 安装和无左值准备的全局安装也在原 freereg 分配，再直接写入目标；收回临时声明后，
/// 后续同槽新值由 preview 重新声明，避免把其 SETLIST 初始化误接到旧 table 身份。
fn completed_value_assignment(
    context: NativeFrameContext<'_>,
    stmts: &[&HirStmt],
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    sink: usize,
    following_floor: Option<usize>,
    following_read: Option<HomeSlotKey>,
) -> Option<Plan> {
    let HirStmt::Assign(assign) = &stmts[sink] else {
        return None;
    };
    let ([target], [HirExpr::LocalRef(source)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let mut start = sink.checked_sub(1)?;
    let (producer, value) = scalar_local(stmts[start])?;
    let base = facts.trusted_local_home_slot(producer)?;
    let target_home = match target {
        HirLValue::Local(target) => Some(facts.trusted_local_home_slot(*target)?),
        HirLValue::Param(target) => Some(facts.trusted_param_home_slot(*target)?),
        HirLValue::Global(_) if dialect == DecompileDialect::Lua51 => None,
        HirLValue::Global(global)
            if context.constants_fit_rk
                && facts.global_write_value_home(global, dialect) == Some(base) =>
        {
            None
        }
        // SETUPVAL 不建立新的源码槽；RHS 仍在原 freereg 分配，写入在原位置保留。
        HirLValue::Upvalue(_) => None,
        _ => return None,
    };
    let mut rebuilt = None;
    let mut luau_compound_global = false;
    let (allocation_home, write_homes, unaliased) = match value {
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) if dialect == DecompileDialect::Luau => {
            // 原高槽 phi 已持有完整短路值，紧邻 COPY 才写入已有低槽 cell。
            // 逐叶核对原比较/读取及结果槽，整批 preview 保留写回后的闭包创建位置。
            let mut builder = frame_builder(context, &[], facts, dialect, base.slot())?;
            builder.boolean_frame = Some(base.slot());
            rebuilt = Some(builder.comparison_tree(value, 0, base.slot(), false)?);
            (
                base,
                facts.complete_local_definition_write_homes(producer),
                facts.local_definitions_reference_unaliased(producer),
            )
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
            if dialect == DecompileDialect::Lua51 =>
        {
            let HirLValue::Global(global) = target else {
                return None;
            };
            let (temp, home) = facts.global_write_value_preparation(global, value)?;
            if facts.global_write_value_home(global, dialect) != Some(home)
                || facts.promoted_local_for_temp(temp) != Some(producer)
            {
                return None;
            }
            // Lua 5.1 SETGLOBAL 必须从寄存器取值，直接赋值仍在原 freereg
            // 重发字面量加载；不能推广到会消除显式准备的 RK 写入。证书仅接受
            // 单次原 Def，批量 LOADNIL 不拆开，后继闭包等槽复用交由整批 preview。
            rebuilt = Some(value.clone());
            (
                home,
                facts.complete_temp_definition_write_homes(temp),
                facts.temp_definition_reference_unaliased(temp),
            )
        }
        HirExpr::Binary(binary) if facts.comparison_result_temp(binary).is_some() => {
            // 原结果仍可构成后继帧的低槽前缀；未知控制后缀不能只验证本次 RHS
            // 就退休声明。连续后继帧确已复用该槽时，再消费写回。
            if dialect == DecompileDialect::Luau
                && following_floor.is_none_or(|floor| floor > base.slot())
            {
                return None;
            }
            // 比较指令本身没有值结果；Boolean 写回属于冻结的 phi，不能向
            // operation_result_temp 索取它，也不能把稍后同槽 capture 当成本次捕获。
            let result = facts.comparison_result_temp(binary)?;
            if facts.promoted_local_for_temp(result) != Some(producer) {
                return None;
            }
            let mut builder = frame_builder(context, &[], facts, dialect, base.slot())?;
            builder.boolean_frame = Some(base.slot());
            rebuilt = Some(builder.comparison_tree(value, 0, base.slot(), true)?);
            (
                facts.trusted_temp_home_slot(result)?,
                facts.complete_temp_definition_write_homes(result),
                facts.temp_definition_reference_unaliased(result),
            )
        }
        HirExpr::Binary(binary)
            if !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
                || (dialect == DecompileDialect::Luajit && numeric_rk_arithmetic(binary))
                || (dialect == DecompileDialect::Luau
                    && matches!(target, HirLValue::Upvalue(_) | HirLValue::Global(_))
                    && (binary.op == crate::hir::common::HirBinaryOpKind::Concat
                        || numeric_rk_arithmetic(binary))) =>
        {
            let source = binary.source_site?;
            let result = facts.operation_result_temp(source)?;
            if facts.promoted_local_for_temp(result) != Some(producer) {
                return None;
            }
            // 完整运算必须仍在原 freereg 产生结果；共享 builder 核对每个操作数
            // 的准备和求值顺序，随后在原 sink 写回，不把结果提升为新的源码身份。
            // Luau SETUPVAL 与已核对布局的全局写都不预留左值槽，已完整树化的
            // CONCAT 同样可按原缓冲区重发；后续复用结果槽的值版本仍由整批
            // preview 独立核对，不能因结果曾被发布就提前结束其物理根。
            luau_compound_global = dialect == DecompileDialect::Luau
                && assignments::compound_global(context, facts, target, binary, base);
            rebuilt = Some(if luau_compound_global {
                value.clone()
            } else {
                // 普通 Luau 全局赋值保留高一槽的原读取；它可与结果分别被物化。
                // 只消费紧邻的单次输入准备，不把既有 debug local 或更早快照搬进 RHS。
                let prepared = dialect == DecompileDialect::Luau
                    && matches!(target, HirLValue::Global(_))
                    && start > 0
                    && matches!(&binary.lhs, HirExpr::LocalRef(input)
                        if scalar_local(stmts[start - 1]).is_some_and(|(local, value)|
                            local == *input && matches!(value, HirExpr::GlobalRef(_))));
                let run = if prepared {
                    &stmts[start - 1..start]
                } else {
                    &[]
                };
                let mut builder = frame_builder(context, run, facts, dialect, base.slot())?;
                let value = builder.expr(value, run.len(), base.slot(), None, false, true, None)?;
                if builder.next_event != run.len() {
                    return None;
                }
                start -= run.len();
                value
            });
            (
                facts.operation_result_home(source)?,
                facts.complete_temp_definition_write_homes(result),
                facts.operation_result_reference_unaliased(source),
            )
        }
        HirExpr::UpvalueRef(_)
            if !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
        {
            // GETUPVAL 没有表达式级来源，保守核对整个 local 的写域；任何额外 scratch
            // 写或捕获都会拒绝。读取与目标写入相邻，仍在原 freereg 发出同一次读取。
            (
                base,
                facts.complete_local_definition_write_homes(producer),
                false,
            )
        }
        HirExpr::GlobalRef(global)
            if !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
        {
            let crate::hir::common::HirOperationSources::Single(source) = global.sources else {
                return None;
            };
            let result = facts.operation_result_temp(source)?;
            if facts.promoted_local_for_temp(result) != Some(producer) {
                return None;
            }
            // 原读与写之间没有求值；RHS 仍写入同一 freereg，环境 cell 仍在写入点读取。
            // 不能合并寄存器环境或动态 key，那些操作另有必须保留的左值准备。
            (
                facts.global_read_frame(global, dialect)?,
                facts.complete_temp_definition_write_homes(result),
                facts.operation_result_reference_unaliased(source),
            )
        }
        HirExpr::TableAccess(access) => {
            // 候选拒绝[ProofIncomplete:Lifetime]：唯一读取不等于根已死亡。
            // 后继完整帧必须覆盖这个原 scratch，不能让存入弱表/全局后的快照提前退休。
            if target_home != Some(base)
                && following_floor != Some(base.slot())
                && following_read != Some(base)
            {
                return None;
            }
            let crate::hir::common::HirOperationSources::Single(site) = access.sources else {
                return None;
            };
            let result = facts.operation_result_temp(site)?;
            if facts.promoted_local_for_temp(result) != Some(producer) {
                return None;
            }
            // 同槽读取链可直接成为最终写回的 RHS；完整 builder 消费前面的 base
            // 准备，避免留下仅为链式 GETTABLE 存在的机械 local 前缀。
            let mut builder = frame_builder(context, &stmts[..start], facts, dialect, base.slot())?;
            rebuilt =
                Some(builder.expr(value, start, base.slot(), None, true, true, Some(result))?);
            if let Some(first) = builder.first_event {
                if builder.next_event != start {
                    return None;
                }
                start = first;
            }
            (
                facts.table_read_result_home(access)?,
                facts.complete_temp_definition_write_homes(result),
                facts.operation_result_reference_unaliased(site),
            )
        }
        HirExpr::Closure(closure)
            if closure.creation.is_some()
                && !matches!(dialect, DecompileDialect::Luau | DecompileDialect::Luajit) =>
        {
            let source = closure.source_site?;
            let result = facts.operation_result_temp(source)?;
            // 原 CLOSURE 版本独立于同 Local 后续的 callee 复用；捕获只能指向
            // 已存在的低槽或上值，递归捕获本次 scratch 不属于这个赋值事务。
            if facts.promoted_local_for_temp(result) != Some(producer)
                || !frame_builder(context, &[], facts, dialect, base.slot())?
                    .constructor_field_is_preserved(value)
            {
                return None;
            }
            (
                facts.operation_result_home(source)?,
                facts.complete_temp_definition_write_homes(result),
                facts.operation_result_reference_unaliased(source),
            )
        }
        HirExpr::TableConstructor(table) => {
            // 赋值 RHS 仍在原 freereg 构造，低槽/全局/upvalue 目标只在完成后写入。
            // 与嵌套字段共用原 SETLIST/SETTABLE 布局证明，再核对字段求值槽和捕获。
            let mut builder = frame_builder(context, &[], facts, dialect, base.slot())?;
            if !matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                || table.trailing_multivalue.is_some()
            {
                builder.completed_constructor_layout(table, base)?;
            }
            rebuilt = Some(builder.complete_constructor(table, 0, base.slot())?);
            // 开放尾仍由 complete_constructor 在原高一槽重放；构造结果留在
            // allocation home，随后这次低槽 MOVE 不改变 CALL 的开放结果宽度。
            // 同一 scratch local 可依次承接 table、closure 和 callee；本次分配只
            // 核对其原 Def 的 COPY 写域，后续版本由 preview 的 epoch 恢复核对。
            let mut write_homes = BTreeSet::new();
            table.sources.try_for_each_known(|source| {
                let result = facts.operation_result_temp(source)?;
                write_homes.extend(
                    facts
                        .complete_temp_definition_write_homes(result)
                        .iter()
                        .copied(),
                );
                Some(())
            })?;
            (
                facts.allocation_result_home(table)?,
                std::borrow::Cow::Owned(write_homes),
                facts.allocation_result_reference_unaliased(table),
            )
        }
        _ => return None,
    };
    if producer != *source
        || allocation_home != base
        || target_home.is_some_and(|target| target.slot() >= base.slot())
        || context.proto
            .local_debug_hints
            .get(producer.index())
            .is_some_and(Option::is_some)
        || context.proto
            .local_debug_scopes
            .get(producer.index())
            .is_some_and(Option::is_some)
        // 完整 builder 已重建 RHS 帧时，旧机械声明仅承担的前缀义务由
        // 同批 prefix/epoch preview 接管；其它保留原因仍然是屏障。
        || matches!(context.proto.inline_dispositions.local(producer),
            crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason|
                    *reason != HirInlineRetentionReason::PhysicalFramePrefix || rebuilt.is_none()))
        // 透明 MOVE 的低槽目标可能已被捕获；该写在 sink 原位保留。这里只删除
        // scratch 身份，不删目标 cell 写，额外隐藏写仍不属于本事务。
        || (context.barred.contains(&base) && !unaliased)
        || write_homes.iter().any(|home| *home != base && Some(*home) != target_home)
        || !facts
            .complete_local_definition_write_homes(producer)
            .is_disjoint(context.closed)
    {
        return None;
    }
    Some(Plan {
        prefix_at_sink: false,
        luau_function_declaration: false,
        start,
        sink,
        base,
        values: vec![rebuilt.unwrap_or_else(|| value.clone())].into(),
        result_locals: Vec::new(),
        discarded_result: None,
        assignment_targets: vec![target.clone()],
        luau_compound_global,
        indexed_target: None,
        continuing_root: None,
        retained_copies: Vec::new(),
        replayed_effects: Vec::new(),
        removed: Vec::new(),
    })
}

/// 每次预览只克隆一次树，所有剩余读写/capture 共用一次扫描；不为每个 LocalId 扫后缀。
fn build_preview(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    plans: &[Plan],
    stmt_count: usize,
) -> Result<Preview, BTreeSet<usize>> {
    let mut failures = BTreeSet::new();
    apply_preview(proto.clone(), facts, plans, stmt_count, &mut failures).ok_or_else(|| {
        if failures.is_empty() {
            failures.extend(plans.iter().map(|plan| plan.start));
        }
        failures
    })
}

/// 原 nil 批次可同时覆盖旧 owner 并声明新的槽。Locals 已原位绑定整个组；
/// 若旧声明被本次帧消费，紧邻的 empty 新成员与全 nil 写可一起成为完整声明。
/// DFS 相邻还须是同一块的语句相邻，不能越过透明 block 的入口或出口。
fn adjacent_nil_declarations(
    proto: &HirProto,
    removed: &[bool],
) -> BTreeMap<usize, (usize, BTreeSet<LocalId>)> {
    let mut flat = Vec::new();
    flatten_scope(&proto.body, &mut 0, &mut flat);
    flat.windows(2)
        .filter_map(|pair| {
            let (previous, next) = (pair[0]?, pair[1]?);
            if previous.id + 1 != next.id || removed[previous.id] {
                return None;
            }
            let (HirStmt::LocalDecl(decl), HirStmt::Assign(assign)) = (previous.stmt, next.stmt)
            else {
                return None;
            };
            let targets = assign
                .targets
                .iter()
                .map(|target| {
                    let HirLValue::Local(local) = target else {
                        return None;
                    };
                    Some(*local)
                })
                .collect::<Option<BTreeSet<_>>>()?;
            (!decl.bindings.is_empty()
                && targets.len() == assign.targets.len()
                && decl.bindings.iter().all(|local| targets.contains(local))
                && decl.values.is_empty()
                && decl.initializer_merge_transaction.is_none()
                && assign.initializer_merge_transaction.is_none()
                && assign.values.tail.is_none()
                && assign.targets.len() == assign.values.fixed.len()
                && assign
                    .values
                    .fixed
                    .iter()
                    .all(|value| matches!(value, HirExpr::Nil)))
            .then(|| {
                (
                    next.id,
                    (previous.id, decl.bindings.iter().copied().collect()),
                )
            })
        })
        .collect()
}

fn apply_preview(
    mut preview: HirProto,
    facts: &ProtoPromotionFacts,
    plans: &[Plan],
    stmt_count: usize,
    failures: &mut BTreeSet<usize>,
) -> Option<Preview> {
    let mut removed = vec![false; stmt_count];
    let mut origins = vec![usize::MAX; stmt_count];
    for plan in plans {
        origins[plan.sink] = origins[plan.sink].min(plan.start);
        for &index in &plan.removed {
            removed[index] = true;
            origins[index] = origins[index].min(plan.start);
        }
    }
    let mut sinks = plans.iter().peekable();
    visit_scope_mut(&mut preview.body, &mut 0, &mut |index, _, stmt| {
        let Some(plan) = sinks.peek().filter(|plan| plan.sink == index) else {
            return Some(());
        };
        if plan.only_preserves_call_prefix() {
            // 只签声明前缀，不重发已有 CALL 或重新消费其根协议。
            sinks.next();
            return Some(());
        }
        if plan.discarded_result.is_some() {
            let [HirExpr::Call(call)] = plan.values.fixed.as_slice() else {
                unreachable!()
            };
            *stmt = HirStmt::CallStmt(Box::new(crate::hir::common::HirCallStmt {
                call: call.as_ref().clone(),
            }));
            sinks.next();
            return Some(());
        }
        if !plan.result_locals.is_empty()
            && (super::super::table_constructors::constructor_write(stmt).is_some()
                || plan.result_locals.len() > 1)
        {
            // record/Batch 与并列 CALL 的末次写都是整组事务终点。
            // 从计划恢复全部声明身份，不能沿用最后一条写的单个左值。
            *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: plan.result_locals.clone(),
                values: plan.values.clone(),
                initializer_merge_transaction: None,
            }));
            sinks.next();
            return Some(());
        }
        match stmt {
            HirStmt::CallStmt(sink) => {
                let [HirExpr::Call(call)] = plan.values.fixed.as_slice() else {
                    unreachable!()
                };
                sink.call = call.as_ref().clone();
            }
            HirStmt::LocalDecl(sink) => {
                if !plan.result_locals.is_empty() {
                    sink.bindings = plan.result_locals.clone();
                }
                sink.values = plan.values.clone();
            }
            HirStmt::GlobalDecl(sink) => {
                sink.values = plan.values.clone();
            }
            HirStmt::Assign(sink) => {
                sink.luau_compound_global = plan.luau_compound_global;
                sink.luau_function_declaration = plan.luau_function_declaration;
                if let Some(target) = &plan.indexed_target {
                    sink.targets = vec![HirLValue::TableAccess(Box::new(target.clone()))];
                } else if !plan.assignment_targets.is_empty() {
                    sink.targets = plan.assignment_targets.clone();
                }
                sink.values = plan.values.clone();
                sink.is_phi_transfer = false;
                sink.parallel_nil_frame = (sink.targets.len() > 1
                    && sink.values.tail.is_none()
                    && sink.values.fixed.len() == sink.targets.len()
                    && sink
                        .values
                        .fixed
                        .iter()
                        .all(|value| matches!(value, HirExpr::Nil)))
                .then_some(plan.base);
            }
            HirStmt::Return(sink) => {
                sink.values = plan.values.clone();
            }
            HirStmt::GenericFor(sink) => {
                sink.rewrite_iterator(|iterator| *iterator = plan.values.clone());
            }
            HirStmt::NumericFor(sink) => {
                let [start, limit, step] = plan.values.fixed.as_slice() else {
                    unreachable!("numeric header plan has three fixed values")
                };
                sink.start = start.clone();
                sink.limit = limit.clone();
                sink.step = step.clone();
            }
            HirStmt::If(sink) => {
                let [condition] = plan.values.fixed.as_slice() else {
                    unreachable!("comparison plan has one condition")
                };
                sink.cond = condition.clone();
            }
            HirStmt::Repeat(sink) => {
                let [condition] = plan.values.fixed.as_slice() else {
                    unreachable!("repeat condition plan has one condition")
                };
                sink.cond = condition.clone();
            }
            _ => unreachable!(),
        }
        sinks.next();
        Some(())
    })?;
    let nil_declarations = adjacent_nil_declarations(&preview, &removed);
    // 每个 owner 的最后一条直接语句仍在该词法块内；用这个保守边界允许整个后缀
    // 都留在子块的声明下沉。索引只建一次，不逐候选重扫后缀或复制累计绑定集合。
    // local f=g; f(); if c then f=1 else f=0 end; use(f) 的某一臂重声明
    // 不能恢复合流后的身份；只有剩余使用全部留在子块时才允许在该块恢复。
    let mut owner_last_stmt = vec![0; stmt_count];
    let mut last_mentions = BTreeMap::new();
    let mut reads = BTreeSet::new();
    let mut writes = BTreeMap::<HirBinding, usize>::new();
    visit_scope_mut(&mut preview.body, &mut 0, &mut |index, owner, stmt| {
        owner_last_stmt[owner] = index;
        if !removed[index] && !matches!(stmt, HirStmt::Block(_)) {
            let mut mentions = BindingReadCollector(|binding| {
                reads.insert(binding);
                last_mentions.insert(binding, index);
            });
            if matches!(
                stmt,
                HirStmt::GenericFor(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::If(_)
                    | HirStmt::While(_)
                    | HirStmt::Repeat(_)
            ) {
                crate::hir::visit::visit_stmt_header(stmt, &mut mentions);
            } else {
                visit_stmts(std::slice::from_ref(stmt), &mut mentions);
            }
            let mut mentions = BindingWriteCollector(|binding| {
                *writes.entry(binding).or_default() += 1;
                last_mentions.insert(binding, index);
            });
            if matches!(
                stmt,
                HirStmt::GenericFor(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::If(_)
                    | HirStmt::While(_)
                    | HirStmt::Repeat(_)
            ) {
                crate::hir::visit::visit_stmt_header(stmt, &mut mentions);
            } else {
                visit_stmts(std::slice::from_ref(stmt), &mut mentions);
            }
        }
        Some(())
    })?;
    // 标记被消费的 value epoch，而非从函数入口把所有同名 local 都看作未声明。
    // 已有声明上的 Assign 也必须等到下一次独立写才允许重新读取。
    let mut missing = BTreeMap::<HirBinding, MissingEpoch>::new();
    let owner_ends = prefix::coordinates::owner_ends(&preview.body, stmt_count);
    let mut scoped_epochs = Vec::<(usize, HirBinding, MissingEpoch)>::new();
    let replayed_effects = plans
        .iter()
        .flat_map(|plan| plan.replayed_effects.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut orphaned_homes = BTreeMap::new();
    let mut recovered = Vec::new();
    let discarded = plans
        .iter()
        .filter_map(|plan| plan.discarded_result.map(|local| (plan.sink, local)))
        .collect::<BTreeMap<_, _>>();
    visit_scope_mut(&mut preview.body, &mut 0, &mut |index, owner, stmt| {
        while scoped_epochs
            .last()
            .is_some_and(|(end, _, _)| *end <= index)
        {
            let (_, binding, epoch) = scoped_epochs.pop().unwrap();
            missing.insert(binding, epoch);
        }
        let mut failure = None;
        let mut affected = BTreeSet::new();
        let accepted = (|| {
            if let HirStmt::LocalRootRelease(local) = stmt
                && missing.contains_key(&HirBinding::Local(*local))
            {
                // 完整帧已撤销该 epoch 的额外源码根；对应 release 不再有 local 可清。
                // 保留 missing 到下一次独立定义，不能借删除 release 允许后续悬空读取。
                removed[index] = true;
                return Some(());
            }
            if removed[index] {
                if let HirStmt::If(branch) = stmt
                    && branch.preserves_empty_test
                    && branch.then_block.stmts.is_empty()
                    && branch
                        .else_block
                        .as_ref()
                        .is_none_or(|arm| arm.stmts.is_empty())
                {
                    // conditional initializer 已签证在 RHS 重发该 TEST；空臂没有需要
                    // 退休的写入身份，后续仍核对输入声明的消费与复用。
                    return Some(());
                }
                if replayed_effects.contains(&index) {
                    // 写回或调用在同一原子事务的 sink 重发；新 RHS 明确读取写前版本。
                    // 只跳过已签证的效果，快照声明仍须经过 missing/后缀复用验证。
                    return Some(());
                }
                if super::super::table_constructors::constructor_write(stmt).is_some() {
                    return Some(());
                }
                if let HirStmt::LocalDecl(decl) = stmt {
                    for &local in &decl.bindings {
                        if !last_mentions.contains_key(&HirBinding::Local(local))
                            && preview
                                .local_debug_hints
                                .get(local.index())
                                .is_none_or(Option::is_none)
                            && preview
                                .local_debug_scopes
                                .get(local.index())
                                .is_none_or(Option::is_none)
                            && let Some(home) = facts.trusted_local_home_slot(local)
                        {
                            orphaned_homes
                                .entry((owner, home))
                                .and_modify(|local| *local = None)
                                .or_insert(Some(local));
                        }
                        missing.insert(
                            HirBinding::Local(local),
                            MissingEpoch {
                                needs_declaration: true,
                                owner,
                                start: origins[index],
                                contributors: BTreeSet::from([origins[index]]),
                            },
                        );
                    }
                } else if let HirStmt::Assign(assign) = stmt {
                    // 完整 generic-for initializer 可同时消费多个控制 Temp；后缀仍逐身份查悬空读取。
                    for target in &assign.targets {
                        let binding = match target {
                            HirLValue::Param(param) => HirBinding::Param(*param),
                            HirLValue::Temp(temp) => HirBinding::Temp(*temp),
                            HirLValue::Local(local) => HirBinding::Local(*local),
                            _ => return None,
                        };
                        missing
                            .entry(binding)
                            .and_modify(|epoch| {
                                epoch.contributors.insert(origins[index]);
                            })
                            .or_insert(MissingEpoch {
                                needs_declaration: false,
                                owner,
                                start: origins[index],
                                contributors: BTreeSet::from([origins[index]]),
                            });
                    }
                } else {
                    let (binding, _) = scalar_binding(stmt)?;
                    missing
                        .entry(binding)
                        .and_modify(|epoch| {
                            epoch.contributors.insert(origins[index]);
                        })
                        .or_insert(MissingEpoch {
                            needs_declaration: false,
                            owner,
                            start: origins[index],
                            contributors: BTreeSet::from([origins[index]]),
                        });
                }
                return Some(());
            }
            if matches!(stmt, HirStmt::Block(_)) {
                return Some(());
            }
            // 被消费的匿名前缀还可能由另一个未提升的 Temp 版本覆盖。只接回单写、
            // 无读取且没有额外 COPY 写域的原常量写；旧身份必须已无剩余使用。
            // 这不是插入占位声明：初始化与原槽均来自现存定义，事实随整个帧事务提交。
            if let Some((temp, value)) = stmt.scalar_temp_assignment()
                && matches!(
                    value,
                    HirExpr::Nil
                        | HirExpr::Boolean(_)
                        | HirExpr::Integer(_)
                        | HirExpr::Number(_)
                        | HirExpr::String(_)
                )
                && !reads.contains(&HirBinding::Temp(temp))
                && writes.get(&HirBinding::Temp(temp)) == Some(&1)
                && preview
                    .temp_debug_locals
                    .get(temp.index())
                    .is_none_or(Option::is_none)
                && preview
                    .temp_debug_scopes
                    .get(temp.index())
                    .is_none_or(Option::is_none)
                && let Some(home) = facts.trusted_temp_home_slot(temp)
                && facts
                    .complete_temp_definition_write_homes(temp)
                    .iter()
                    .copied()
                    .eq(std::iter::once(home))
                && let Some(Some(local)) = orphaned_homes.remove(&(owner, home))
                && let Some(epoch) = missing.get(&HirBinding::Local(local))
                && epoch.needs_declaration
            {
                recovered.push(RecoveredDeclaration {
                    index,
                    owner,
                    origin: epoch.start,
                    temp,
                    local,
                });
                let HirStmt::Assign(assign) = stmt else {
                    unreachable!()
                };
                assign.targets = vec![HirLValue::Local(local)];
            }
            let mut read_missing = None::<usize>;
            let mut written_missing = BTreeSet::new();
            let mut mentions = (
                BindingReadCollector(|binding| {
                    if let Some(epoch) = missing.get(&binding) {
                        affected.insert(binding);
                        read_missing =
                            Some(read_missing.map_or(epoch.start, |old| old.min(epoch.start)));
                    }
                }),
                BindingWriteCollector(|binding| {
                    if missing.contains_key(&binding) {
                        written_missing.insert(binding);
                    }
                }),
            );
            if matches!(
                stmt,
                HirStmt::GenericFor(_)
                    | HirStmt::NumericFor(_)
                    | HirStmt::If(_)
                    | HirStmt::While(_)
                    | HirStmt::Repeat(_)
            ) {
                crate::hir::visit::visit_stmt_header(stmt, &mut mentions);
            } else {
                visit_stmts(std::slice::from_ref(stmt), &mut mentions);
            }
            if let Some(start) = read_missing {
                failure = Some(start);
                return None;
            }
            affected.extend(written_missing.iter().copied());
            // 以下恢复失败只能归到当前写涉及的缺失 epoch；不能截在失败语句之后保留坏事务。
            failure = written_missing
                .iter()
                .map(|binding| missing[binding].start)
                .min();
            // 候选拒绝[SemanticBarrier]：子块或兄弟臂内的写既不支配原 owner 的后缀，
            // 也不能在原声明被消费后给它提供词法绑定；DFS 的访问先后不是路径证明。
            // 同 owner 的独立写仍沿用已有恢复协议，不为每个候选重建控制流分析。
            if written_missing.iter().any(|binding| {
                missing
                    .get(binding)
                    .is_none_or(|epoch| epoch.owner != owner)
                    && last_mentions
                        .get(binding)
                        .is_none_or(|last| *last > owner_last_stmt[owner])
                    && !(written_missing.len() == 1
                        && matches!(binding, HirBinding::Local(_))
                        && scalar_binding(stmt).is_some()
                        && missing
                            .get(binding)
                            .is_some_and(|epoch| epoch.needs_declaration))
            }) {
                return None;
            }
            if matches!(stmt, HirStmt::Assign(assign) if assign.generic_for_dispatch_release.is_some())
                && !written_missing.is_empty()
            {
                // 外层构造器不能独自删除或另造 dispatch endpoint 的声明；须由循环头联合消费。
                return None;
            }
            if let Some(&local) = discarded.get(&index) {
                // CALL 与紧邻常量写之间没有观察；结束结果绑定，并在下一次原槽写重建声明。
                missing.insert(
                    HirBinding::Local(local),
                    MissingEpoch {
                        needs_declaration: true,
                        owner,
                        start: origins[index],
                        contributors: BTreeSet::from([origins[index]]),
                    },
                );
            }
            if written_missing.is_empty() {
                return Some(());
            }
            if let HirStmt::LocalDecl(decl) = stmt {
                for local in &decl.bindings {
                    missing.remove(&HirBinding::Local(*local));
                }
                return Some(());
            }
            if let HirStmt::Assign(assign) = stmt
                && assign.targets.len() > 1
            {
                if written_missing.iter().all(|binding| {
                    missing
                        .get(binding)
                        .is_some_and(|epoch| !epoch.needs_declaration)
                }) {
                    // 原声明仍在，仅当前值版本的 COPY 被消费；多结果 RHS 已先查悬空读。
                    // 整组写原位重新定义这些已有身份，不应把它们变成新的 local 声明。
                    for binding in &written_missing {
                        missing.remove(binding);
                    }
                    return Some(());
                }
                let nil_declaration = nil_declarations.get(&index);
                let bindings = assign
                    .targets
                    .iter()
                    .map(|target| {
                        let HirLValue::Local(local) = target else {
                            return None;
                        };
                        (missing
                            .get(&HirBinding::Local(*local))
                            .is_some_and(|epoch| epoch.needs_declaration)
                            || nil_declaration
                                .is_some_and(|(_, bindings)| bindings.contains(local)))
                        .then_some(*local)
                    })
                    .collect::<Option<Vec<_>>>()?;
                if let Some((declaration, declared)) = nil_declaration {
                    let targets = bindings.iter().copied().collect::<BTreeSet<_>>();
                    if targets.len() != bindings.len() || !declared.is_subset(&targets) {
                        return None;
                    }
                    removed[*declaration] = true;
                }
                for local in &bindings {
                    missing.remove(&HirBinding::Local(*local));
                }
                *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                    bindings,
                    values: std::mem::take(&mut assign.values),
                    initializer_merge_transaction: None,
                }));
                return Some(());
            }
            let (binding, _) = scalar_binding(stmt)?;
            if written_missing.len() != 1 {
                return None;
            }
            let epoch = missing.remove(&binding)?;
            let needs_declaration = epoch.needs_declaration;
            if needs_declaration && epoch.owner != owner {
                // 子块首个独立写可恢复该块的声明；离开它时恢复外层缺失状态。
                // 因此兄弟分支必须各自先写，合流后的读取仍会拒绝，不能把 DFS 当支配。
                scoped_epochs.push((owner_ends[owner], binding, epoch));
            }
            if !needs_declaration || matches!(stmt, HirStmt::LocalDecl(_)) {
                return Some(());
            }
            let HirStmt::Assign(assign) = stmt else {
                return None;
            };
            let HirBinding::Local(local) = binding else {
                return None;
            };
            // 原匿名定义已完整消费；后缀首个独立写成为同一身份的新声明起点。
            *stmt = HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values: std::mem::take(&mut assign.values),
                initializer_merge_transaction: None,
            }));
            Some(())
        })();
        if accepted.is_none() {
            // 同一绑定可能由多个候选依次消费；一次撤回全部依赖，不能只记首个
            // epoch 后在下一轮预览才发现其余消费。取走集合避免重复失败反复扫描。
            for binding in affected {
                if let Some(epoch) = missing.get_mut(&binding) {
                    failures.append(&mut epoch.contributors);
                }
            }
            let origin =
                failure.or_else(|| (origins[index] != usize::MAX).then_some(origins[index]));
            if let Some(origin) = origin {
                failures.insert(origin);
            } else {
                failures.extend(plans.iter().map(|plan| plan.start));
            }
            // 本预览已拒绝；失败 RHS 不使其独立新声明也消失。保留这次定义的
            // 诊断边界，避免后续读取把无关构造器误报成丢失值的生产者。
            // 修订后的整批仍从原 IR 重建并完整验证，不提交本次失败预览。
            if let HirStmt::LocalDecl(decl) = stmt {
                for local in &decl.bindings {
                    missing.remove(&HirBinding::Local(*local));
                }
            }
        }
        Some(())
    })?;
    if !failures.is_empty() {
        return None;
    }
    restore_adjacent_nil_owner(&mut preview, facts, &mut removed, &mut recovered);
    Some(Preview {
        proto: preview,
        removed,
        recovered,
    })
}

/// 控制头准备退休后，原 NIL 与结果空声明可能才变为相邻；初始化仍留在原写点。
fn restore_adjacent_nil_owner(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    removed: &mut [bool],
    recovered: &mut [RecoveredDeclaration],
) {
    let mut read = (0..proto.local_count).map(LocalId).filter(|local| {
        matches!(proto.inline_dispositions.local(*local), crate::hir::common::HirInlineDisposition::Preserve(reasons)
            if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
    }).collect::<BTreeSet<_>>();
    let mut flat = Vec::new();
    flatten_scope(&proto.body, &mut 0, &mut flat);
    for entry in flat.iter().flatten().filter(|entry| !removed[entry.id]) {
        let mut mentions = BindingReadCollector(|binding| {
            if let HirBinding::Local(local) = binding {
                read.insert(local);
            }
        });
        crate::hir::visit::visit_stmt_header(entry.stmt, &mut mentions);
        if !matches!(entry.stmt, HirStmt::LocalDecl(_)) {
            crate::hir::visit::visit_stmt_header(
                entry.stmt,
                &mut BindingWriteCollector(|binding| {
                    if let HirBinding::Local(local) = binding {
                        read.insert(local);
                    }
                }),
            );
        }
    }
    let mut previous = None;
    let mut replacements = BTreeMap::new();
    let mut merges = BTreeMap::new();
    for entry in flat {
        let Some(entry) = entry else {
            previous = None;
            continue;
        };
        if removed[entry.id] {
            continue;
        }
        if let HirStmt::LocalDecl(decl) = entry.stmt
            && decl.initializer_merge_transaction.is_none()
            && let [local] = decl.bindings.as_slice()
            && proto.local_debug_hints[local.index()].is_none()
            && proto.local_debug_scopes[local.index()].is_none()
        {
            if decl.values.is_empty()
                && let Some((index, seed, home)) = previous
                && facts.trusted_local_home_slot(*local) == Some(home)
            {
                replacements.insert(index, *local);
                removed[entry.id] = true;
                merges.insert(seed, *local);
                previous = None;
                continue;
            }
            if decl.values.fixed.as_slice() == [HirExpr::Nil]
                && decl.values.tail.is_none()
                && !read.contains(local)
                && let Some(home) = facts.trusted_local_home_slot(*local)
            {
                previous = Some((entry.id, *local, home));
                continue;
            }
        }
        previous = None;
    }
    visit_scope_mut(&mut proto.body, &mut 0, &mut |index, _, stmt| {
        if let Some(&target) = replacements.get(&index) {
            let HirStmt::LocalDecl(decl) = stmt else {
                unreachable!()
            };
            decl.bindings[0] = target;
        }
        Some(())
    });
    for declaration in recovered {
        if let Some(&target) = merges.get(&declaration.local) {
            declaration.local = target;
        }
    }
    for (seed, target) in merges {
        if proto.physical_root_locals.remove(&seed) {
            proto.physical_root_locals.insert(target);
        }
        if let crate::hir::common::HirInlineDisposition::Preserve(reasons) =
            proto.inline_dispositions.local(seed).clone()
        {
            for reason in reasons {
                proto.inline_dispositions.preserve_local(target, reason);
            }
        }
    }
}

fn publish_recovered_declarations(preview: &mut Preview, facts: &mut ProtoPromotionFacts) {
    for declaration in &preview.recovered {
        facts.record_temp_to_local_merge(declaration.temp, declaration.local);
        preview
            .proto
            .inline_dispositions
            .promote_temp_to_local(declaration.temp, declaration.local);
        preview.proto.inline_dispositions.preserve_local(
            declaration.local,
            HirInlineRetentionReason::PhysicalFramePrefix,
        );
    }
}
