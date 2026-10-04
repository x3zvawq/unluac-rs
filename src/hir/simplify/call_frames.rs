//! 将完整原调用帧恢复为 HIR 表达式，统一普通调用与方法链的帧证明。
//!
//! 消费 Promotion 的定义、参数、结果及方法协议，并与源码声明前缀 owner 协作提交。

mod fastcalls;
mod interpolation;
mod logical;
mod lookups;
mod native;
mod parameter_returns;
mod tables;

pub(super) use native::deferred_lookup_decisions;
pub(super) use native::expanded::preserve_seeded_predicate_outputs;
pub(super) use native::prepare_source_frames;
pub(super) use native::preserve_existing_call_prefixes;
pub(super) use native::restore_expanded_frames;
pub(super) use native::restore_lookup_decision_frames;
pub(super) use native::restore_tbc_initializer_frames;
pub(super) use parameter_returns::restore as restore_parameter_return_frames;
pub(super) use tables::{RkLiterals, constants_fit_rk, rk_prefix_end};

use crate::transformer::{ResultPack, ValuePack};
use std::collections::{BTreeMap, BTreeSet};

/// 仅延后已有完整操作帧证明的候选；Final 重新验证当前声明前缀。
#[derive(Default)]
pub(in crate::hir) struct DeferredLookupDecisions {
    pub(super) locals: BTreeSet<LocalId>,
    pub(super) calls: BTreeSet<crate::hir::common::HirSourceSite>,
}

use super::mention::{CaptureCollector, ProtectedLocalCollector, ToBeClosedHomeCollector};
use super::source_frames as prefix;
use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBinding, HirBlock, HirCallExpr, HirCallRootHandoff, HirCaptureMode, HirExpr, HirLValue,
    HirMethodCall, HirPackTail, HirProto, HirStmt, HirTableAllocation, HirTableField, HirValuePack,
    LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

struct FrameRestrictions {
    barred: BTreeSet<HomeSlotKey>,
    closed: BTreeSet<HomeSlotKey>,
    protected: BTreeSet<LocalId>,
    callee_aliases: fastcalls::CalleeAliases,
}

/// 数值与位运算都按原单结果指令重发输入；比较的分支写回和 CONCAT 的连续缓冲另行证明。
fn is_scalar_binary_operation(op: crate::hir::common::HirBinaryOpKind) -> bool {
    use crate::hir::common::HirBinaryOpKind;
    matches!(
        op,
        HirBinaryOpKind::Add
            | HirBinaryOpKind::Sub
            | HirBinaryOpKind::Mul
            | HirBinaryOpKind::Div
            | HirBinaryOpKind::FloorDiv
            | HirBinaryOpKind::Mod
            | HirBinaryOpKind::Pow
            | HirBinaryOpKind::BitAnd
            | HirBinaryOpKind::BitOr
            | HirBinaryOpKind::BitXor
            | HirBinaryOpKind::Shl
            | HirBinaryOpKind::Shr
    )
}

fn numeric_rk_arithmetic(binary: &crate::hir::common::HirBinaryExpr) -> bool {
    is_scalar_binary_operation(binary.op)
        && [&binary.lhs, &binary.rhs]
            .iter()
            .any(|value| matches!(value, HirExpr::Integer(_) | HirExpr::Number(_)))
}

fn frame_restrictions(proto: &HirProto, facts: &ProtoPromotionFacts) -> FrameRestrictions {
    let mut collectors = (
        (
            CaptureCollector::new(HirCaptureMode::ByReference),
            CaptureCollector::new(HirCaptureMode::ByValue),
        ),
        (
            ProtectedLocalCollector::default(),
            ToBeClosedHomeCollector {
                facts,
                homes: BTreeSet::new(),
            },
        ),
    );
    crate::hir::visit::visit_stmts(&proto.body.stmts, &mut collectors);
    let ((reference, value), (protected, closed)) = collectors;
    let mut barred = reference.bindings.complete_home_slots(facts);
    barred.extend(value.bindings.complete_home_slots(facts));
    FrameRestrictions {
        callee_aliases: fastcalls::CalleeAliases::collect(proto, &reference.bindings.locals),
        barred,
        closed: closed.homes,
        protected: protected.locals,
    }
}

pub(super) fn restore_native_call_frames(
    module: &mut crate::hir::HirModule,
    promotion: &mut [ProtoPromotionFacts],
    values: &super::object_flow::ReturnValueFacts,
    dialect: DecompileDialect,
) -> bool {
    // 所有候选先消费同一模块快照，再统一提交；子函数 body 改写后，后一个 proto
    // 不能继续把旧返回值摘要当成新快照。nil 准备或上值写可不经 local，不能按无 local 跳过。
    let mut prepared = Vec::new();
    let terminal = native::terminal_closure_facts(module, promotion, values, dialect);
    for proto in &module.protos {
        let Some(facts) = promotion.get(proto.id.index()) else {
            continue;
        };
        // 条件准备可以始终保持 Temp；没有 Local 不代表没有待恢复的原操作帧。
        if proto.local_count == 0
            && proto.temp_count == 0
            && !facts.has_nil_writes()
            && !facts.has_upvalue_writes()
            && !(dialect == DecompileDialect::Luau && facts.has_environment_writes())
        {
            continue;
        }
        let constraints = frame_restrictions(proto, facts);
        prepared.push((
            proto.id,
            native::prepare(
                proto,
                facts,
                dialect,
                &constraints.barred,
                &constraints.closed,
                &constraints.callee_aliases,
                &terminal,
            ),
        ));
    }
    let mut changed = false;
    for (id, plans) in prepared {
        changed |= plans.commit(
            &mut module.protos[id.index()],
            &mut promotion[id.index()],
            dialect,
            id == module.entry,
        );
    }
    changed
}

pub(super) fn restore_terminal_method_frames(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) {
    if matches!(dialect, DecompileDialect::Luajit | DecompileDialect::Luau) {
        return;
    }
    let FrameRestrictions {
        mut barred,
        closed,
        protected,
        ..
    } = frame_restrictions(proto, facts);
    barred.extend(closed);
    for local in protected {
        barred.extend(facts.complete_local_home_slots(local).iter().copied());
    }
    let mut body = std::mem::take(&mut proto.body);
    rewrite_terminal(&mut body, proto, facts, dialect, &barred);
    proto.body = body;
}

fn terminal_index(block: &HirBlock) -> Option<usize> {
    let index = block.stmts.len().checked_sub(1)?;
    if matches!(&block.stmts[index], HirStmt::Return(ret) if ret.values.is_empty()) {
        index.checked_sub(1)
    } else {
        Some(index)
    }
}

fn rewrite_terminal(
    block: &mut HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
) {
    let Some(end) = terminal_index(block) else {
        return;
    };
    if let HirStmt::Block(child) = &mut block.stmts[end] {
        rewrite_terminal(child, proto, facts, dialect, barred);
        return;
    }
    let Some((start, end, call)) = plan(block, proto, facts, dialect, barred) else {
        return;
    };
    let HirStmt::CallStmt(sink) = &mut block.stmts[end] else {
        unreachable!()
    };
    sink.call = call;
    block.stmts.drain(start..end);
}

pub(super) fn scalar_binding(stmt: &HirStmt) -> Option<(HirBinding, &HirExpr)> {
    if let Some((local, value)) = scalar_local(stmt) {
        return Some((HirBinding::Local(local), value));
    }
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    match (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) {
        ([HirLValue::Temp(temp)], [value], None) => Some((HirBinding::Temp(*temp), value)),
        _ => None,
    }
}

fn scalar_local(stmt: &HirStmt) -> Option<(LocalId, &HirExpr)> {
    match stmt {
        HirStmt::LocalDecl(decl) => match (
            decl.bindings.as_slice(),
            decl.values.fixed.as_slice(),
            &decl.values.tail,
        ) {
            ([local], [value], None) => Some((*local, value)),
            _ => None,
        },
        HirStmt::Assign(assign) => match (
            assign.targets.as_slice(),
            assign.values.fixed.as_slice(),
            &assign.values.tail,
        ) {
            ([HirLValue::Local(local)], [value], None) => Some((*local, value)),
            _ => None,
        },
        _ => None,
    }
}

fn plan(
    block: &HirBlock,
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    barred: &BTreeSet<HomeSlotKey>,
) -> Option<(usize, usize, HirCallExpr)> {
    let end = terminal_index(block)?;
    let HirStmt::CallStmt(sink) = &block.stmts[end] else {
        return None;
    };
    if sink.call.is_method() || sink.call.fastcall.is_some() {
        return None;
    }
    let HirExpr::LocalRef(callee) = sink.call.callee else {
        return None;
    };
    let start = (0..end).rfind(|index| {
        scalar_local(&block.stmts[*index]).is_some_and(|(local, _)| local == callee)
    })?;
    if !matches!(scalar_local(&block.stmts[start])?.1, HirExpr::GlobalRef(_)) {
        return None;
    }
    let base = facts.trusted_local_home_slot(callee)?;
    let run = block.stmts[start..end].iter().collect::<Vec<_>>();
    let mut definitions = BTreeMap::<LocalId, Vec<usize>>::new();
    let mut declared = BTreeSet::new();
    for (index, stmt) in run.iter().enumerate() {
        let (local, _) = scalar_local(stmt)?;
        if matches!(stmt, HirStmt::LocalDecl(_)) {
            if !declared.insert(local) {
                return None;
            }
        } else if !declared.contains(&local) {
            return None;
        }
        if proto
            .local_debug_hints
            .get(local.index())
            .is_some_and(Option::is_some)
            || proto
                .local_debug_scopes
                .get(local.index())
                .is_some_and(Option::is_some)
            || proto.inline_dispositions.local(local).must_preserve()
        {
            return None;
        }
        let homes = facts.complete_local_definition_write_homes(local);
        if homes.is_empty() || !homes.is_disjoint(barred) {
            return None;
        }
        definitions.entry(local).or_default().push(index);
    }
    let mut builder = FrameBuilder {
        run: &run,
        definitions,
        constructors: BTreeMap::new(),
        expanded_inputs: BTreeMap::new(),
        constructor_depth: 0,
        declaration_reserved_top: None,
        indexed_key_base: None,
        register_operand: false,
        facts,
        dialect,
        base: base.slot(),
        next_event: 0,
        methods: 0,
        first_event: Some(0),
        native: None,
        result_move: None,
        temp_definitions: BTreeMap::new(),
        nil_group_members: BTreeMap::new(),
        pending_nil_group: None,
        deferred_method_events: BTreeSet::new(),
        boolean_frame: None,
        boolean_condition: None,
        parameter_copy: None,
    };
    let call = builder.call(&sink.call, run.len(), base.slot(), true, CallWidth::Ignore)?;
    // 每个原 producer 必须恰好求值一次，且位置顺序相同；同时排除捕获、自更新和遗漏写入。
    if builder.methods == 0 || builder.next_event != run.len() {
        return None;
    }
    Some((start, end, call))
}

struct FrameBuilder<'a> {
    run: &'a [&'a HirStmt],
    definitions: BTreeMap<LocalId, Vec<usize>>,
    constructors: BTreeMap<usize, Vec<(usize, super::table_constructors::ConstructorWrite<'a>)>>,
    expanded_inputs: BTreeMap<HomeSlotKey, Vec<(usize, LocalId)>>,
    constructor_depth: usize,
    // Luau 声明和 CALL 末参数的已预留上界；内部 scratch 不能覆盖尚待消费的槽。
    declaration_reserved_top: Option<usize>,
    // PUC 上值索引先为 base 保留一槽，key 中间结果可以暂用该槽。
    indexed_key_base: Option<usize>,
    /// 寄存器输入的递归树必须逐层保留原准备写，不能借普通叶子表达式入口跳过布局。
    register_operand: bool,
    facts: &'a ProtoPromotionFacts,
    dialect: DecompileDialect,
    base: usize,
    next_event: usize,
    methods: usize,
    first_event: Option<usize>,
    native: Option<NativeFrameContext<'a>>,
    result_move: Option<(LocalId, usize, BTreeSet<HomeSlotKey>)>,
    temp_definitions: BTreeMap<crate::hir::common::TempId, usize>,
    nil_group_members: BTreeMap<(usize, HirBinding), (usize, usize)>,
    // 多槽 LOADNIL 是一个事件；必须顺序消费所有成员后才能结束。
    pending_nil_group: Option<(usize, usize, crate::hir::common::TempId)>,
    // Luau 的 receiver 先求值，参数后才执行 COPY/方法查找；递归只预留后两事件。
    deferred_method_events: BTreeSet<usize>,
    /// 外层已核对的完整值结果身份；比较叶复用它，不能重新假定 epoch 为零。
    boolean_frame: Option<HomeSlotKey>,
    /// 确切布尔结果帧内的原上值读取，每个来源只消费一次。
    boolean_condition: Option<UpvalueFrameUse>,
    /// 当前参数准备 COPY 的原输入绑定；嵌套表达式只可用确切目标 Def 消费这次读取。
    parameter_copy: Option<(crate::hir::TempId, crate::hir::ParamId, HomeSlotKey)>,
}

struct UpvalueFrameUse {
    result: crate::hir::TempId,
    expected: usize,
    reads: BTreeSet<crate::hir::UpvalueId>,
}

#[derive(Clone, Copy)]
struct NativeFrameContext<'a> {
    proto: &'a HirProto,
    barred: &'a BTreeSet<HomeSlotKey>,
    closed: &'a BTreeSet<HomeSlotKey>,
    callee_aliases: &'a fastcalls::CalleeAliases,
    constants_fit_rk: bool,
    rk_literals: Option<&'a tables::RkLiterals>,
    expanded_callees: Option<&'a native::expanded::Callees>,
    compared_choices: Option<&'a native::expanded::ComparedCallees<'a>>,
    value_expressions: Option<&'a native::expanded::ValueExpressionFrames<'a>>,
    constant_controls: Option<&'a native::expanded::ConstantControlFrames<'a>>,
    calling_values: Option<&'a native::expanded::CallingValueFrames<'a>>,
    seeded_predicates: Option<&'a native::expanded::SeededPredicateFrames>,
    /// 同一连续区内，前序计划已消费的值版本；只供本批 release 交接。
    retired_roots: Option<&'a BTreeSet<LocalId>>,
    /// 仅完整 native 事务可联合消费的 scope holder→原 COPY；提交仍须核对完整交接。
    root_seed_sources: Option<&'a BTreeMap<crate::hir::common::TempId, crate::hir::common::TempId>>,
}

#[derive(Clone, Copy)]
enum CallWidth {
    Ignore,
    Single,
    Fixed(usize),
    Open,
    Tail,
}

impl NativeFrameContext<'_> {
    fn literal_uses_rk(
        &self,
        expr: &HirExpr,
        operand: Option<(&crate::hir::common::HirOperationSources, bool)>,
        dialect: DecompileDialect,
    ) -> Option<bool> {
        if dialect == DecompileDialect::Luau && operand.is_some() {
            return Some(!operand?.1);
        }
        if dialect == DecompileDialect::Luajit
            && matches!(expr, HirExpr::Integer(0..=255))
            && operand.is_some_and(|(_, value)| !value)
        {
            return Some(true);
        }
        if self.constants_fit_rk {
            Some(true)
        } else {
            self.rk_literals?.in_rk(expr, operand)
        }
    }
}

impl FrameBuilder<'_> {
    fn boolean_operand_start(&self, result: usize) -> usize {
        self.declaration_reserved_top.unwrap_or(0).max(result + 1)
    }
    /// LOADNIL 的一次写仍作为一个事件，且每个结果必须来自同一原批次的对应成员。
    /// 声明形状只形成候选；当前消费点的原输入 Def 才授权退休该准备组。
    fn consume_nil_group(
        &mut self,
        index: usize,
        offset: usize,
        width: usize,
        producer: crate::hir::common::TempId,
    ) -> Option<HirExpr> {
        let first = if offset == 0 {
            if self.pending_nil_group.is_some() {
                return None;
            }
            producer
        } else {
            let (pending, next, first) = self.pending_nil_group?;
            if pending != index || next != offset {
                return None;
            }
            first
        };
        let group = self.facts.nil_write_temps(first)?;
        if group.len() != width || group.get(offset) != Some(&producer) {
            return None;
        }
        if offset + 1 == width {
            self.pending_nil_group = None;
            self.finish_event(index)?;
        } else {
            self.pending_nil_group = Some((index, offset + 1, first));
        }
        Some(HirExpr::Nil)
    }

    fn finish_event(&mut self, index: usize) -> Option<()> {
        if self.deferred_method_events.contains(&index) {
            return Some(());
        }
        if self.pending_nil_group.is_some() {
            return None;
        }
        if self.first_event.is_none() {
            self.first_event = Some(index);
            self.next_event = index;
        }
        if index != self.next_event {
            return None;
        }
        self.next_event += 1;
        if let Some(context) = self.native {
            while let Some(HirStmt::LocalRootRelease(local)) = self.run.get(self.next_event) {
                // 整帧已消费的声明不再建立额外源码根，其 release 也须在同一事务退休。
                // 原有低槽声明不在消费段内时仍是屏障；preview 再核对删除后的值版本。
                let declared_inside = self
                    .definitions
                    .get(local)
                    .and_then(|definitions| definitions.first())
                    .is_some_and(|&definition| {
                        self.first_event.is_some_and(|first| definition >= first)
                            && definition < self.next_event
                            && matches!(self.run[definition], HirStmt::LocalDecl(_))
                    });
                if context.expanded_callees.is_none()
                    && !declared_inside
                    && !context
                        .retired_roots
                        .is_some_and(|roots| roots.contains(local))
                {
                    break;
                }
                self.next_event += 1;
            }
        }
        Some(())
    }

    /// 原字面量参数覆盖 COPY 根时没有 RHS 观察；完整 CALL 在同一准备槽重发它。
    /// marker 只连接原覆盖指令与释放身份，不能授权其它形状跳过尚未消费的事件。
    fn consume_argument_root_release(
        &mut self,
        call: &HirCallExpr,
        argument: usize,
        value: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<()> {
        if self.native.is_none() || self.first_event.is_none() || self.next_event >= before {
            return Some(());
        }
        let Some(HirStmt::Assign(assign)) = self.run.get(self.next_event) else {
            return Some(());
        };
        let Some(crate::hir::common::HirRootRelease::CopyOverwrite { source, .. }) =
            &assign.root_release
        else {
            return Some(());
        };
        if !matches!(
            value,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        ) || call
            .source_site
            .is_none_or(|call_source| call_source.proto != source.proto)
            || self
                .facts
                .call_argument_preparation_instruction(call, argument, value)
                != Some(source.instr)
        {
            return Some(());
        }
        let home = self
            .facts
            .call_argument_preparation(call, argument, value)?;
        if home.slot() != slot {
            return None;
        }
        self.consume_copy_root_release(home)
    }

    /// 调用参数及循环控制值共用释放身份校验；调用方先证明自己重发原覆盖端点。
    fn consume_copy_root_release(&mut self, home: HomeSlotKey) -> Option<()> {
        let context = self.native?;
        let HirStmt::Assign(assign) = self.run.get(self.next_event)? else {
            return None;
        };
        let Some(crate::hir::common::HirRootRelease::CopyOverwrite {
            source, released, ..
        }) = &assign.root_release
        else {
            return None;
        };
        if source.proto != context.proto.id
            || context.closed.contains(&home)
            || assign.values.tail.is_some()
            || released.len() != assign.targets.len()
            || released.is_empty()
            || assign.values.fixed.len() != released.len()
            || assign
                .values
                .fixed
                .iter()
                .any(|value| *value != HirExpr::Nil)
        {
            return None;
        }
        let original = self
            .facts
            .copy_root_before_releases(source.instr)
            .iter()
            .copied()
            .collect::<BTreeSet<_>>();
        for (temp, target) in released.iter().zip(&assign.targets) {
            let handoff_source = context
                .root_seed_sources
                .and_then(|sources| sources.get(temp))
                .copied();
            let physical_root = handoff_source.unwrap_or(*temp);
            if !original.contains(temp)
                || self.facts.trusted_temp_home_slot(physical_root) != Some(home)
                || (context.barred.contains(&home)
                    && !self
                        .facts
                        .temp_definition_reference_unaliased(physical_root))
                || !match target {
                    HirLValue::Temp(current) => {
                        current == temp
                            && handoff_source.is_none()
                            && context
                                .proto
                                .temp_debug_locals
                                .get(temp.index())
                                .is_none_or(Option::is_none)
                    }
                    HirLValue::Local(local) => {
                        self.facts.promoted_local_for_temp(*temp) == Some(*local)
                            && if handoff_source.is_some() {
                                self.facts.local_has_no_physical_home(*local)
                            } else {
                                self.facts.trusted_local_home_slot(*local) == Some(home)
                            }
                            && context.proto.local_debug_hints[local.index()].is_none()
                            && context.proto.local_debug_scopes[local.index()].is_none()
                    }
                    _ => false,
                }
            {
                return None;
            }
        }
        // 保留完整前缀/后缀 preview；即使旧根已无读取，也不能独立移除端点。
        self.finish_event(self.next_event)
    }

    fn definition(&self, local: LocalId, before: usize) -> Option<usize> {
        let indices = self.definitions.get(&local)?;
        indices
            .get(
                indices
                    .partition_point(|index| *index < before)
                    .checked_sub(1)?,
            )
            .copied()
    }

    /// 当前定义的原操作结果身份；同名 Local 的后续覆盖不属于这一值版本。
    fn definition_producer(&self, definition: usize) -> Option<crate::hir::common::TempId> {
        let (_, value) = scalar_local(self.run[definition])?;
        let source = match value {
            HirExpr::Call(call) => {
                if let Some(result) = self.expanded_call_result(call) {
                    return Some(result);
                }
                call.source_site?
            }
            HirExpr::Binary(binary) => binary.source_site?,
            HirExpr::Unary(unary) => unary.source_site?,
            HirExpr::GlobalRef(global) => match global.sources {
                crate::hir::common::HirOperationSources::Single(source) => source,
                _ => return None,
            },
            HirExpr::TableAccess(access) => match access.sources {
                crate::hir::common::HirOperationSources::Single(source) => source,
                _ => return None,
            },
            HirExpr::TableConstructor(table) => match table.sources {
                crate::hir::common::HirOperationSources::Single(source) => source,
                _ => return None,
            },
            _ => return None,
        };
        self.facts.operation_result_temp(source)
    }

    fn homes_match(
        &self,
        local: LocalId,
        definition: usize,
        slot: usize,
        receiver: Option<HomeSlotKey>,
        original_producer: Option<crate::hir::common::TempId>,
    ) -> bool {
        if let Some((_, HirExpr::Call(call))) = scalar_local(self.run[definition])
            && self.expanded_scalar_home(call) == Some(HomeSlotKey::new(slot, 0))
            && let Some(producer) = call
                .source_site
                .and_then(|site| self.facts.operation_result_temp(site))
            && self
                .facts
                .trusted_immediate_moves(producer)
                .and_then(|moves| moves.first())
                .and_then(|copy| self.facts.promoted_local_for_temp(copy.target))
                == Some(local)
            && original_producer.is_none_or(|original| original == producer)
        {
            // 这里只承认原高 CALL 与低 COPY 的写域；expr 仍须完整匹配现存函数体，
            // 整批 preview 再验证退休声明与后缀，不能将普通 CALL 单独移到低槽。
            return true;
        }
        let producer = original_producer.or_else(|| self.definition_producer(definition));
        // 编译位置只比较 slot；写入集合仍匹配该原值版本的完整 home，包括 epoch。
        // CALL+COPY 可能由低槽 local 承接，不能拿该 local 的展示 home 冒充 CALL 结果。
        let target_home = producer.map_or_else(
            || self.facts.trusted_local_home_slot(local),
            |producer| self.facts.trusted_temp_home_slot(producer),
        );
        let Some(target_home) = target_home else {
            return false;
        };
        if target_home.slot() != slot && receiver != Some(target_home) {
            return false;
        }
        let homes = if let Some(producer) = producer {
            if self.facts.promoted_local_for_temp(producer) != Some(local) {
                return false;
            }
            if self
                .result_move
                .as_ref()
                .is_some_and(|(owner, index, _)| *owner == local && *index == definition)
                && self
                    .facts
                    .complete_temp_non_move_write_homes(producer)
                    .iter()
                    .any(|home| {
                        *home != target_home && !receiver.is_some_and(|receiver| *home == receiver)
                    })
            {
                return false;
            }
            // 一个匿名 LocalId 可承接多个值版本。CALL、读取、分配和运算的原来源给出
            // 精确 Def；不能把别的 value epoch 的隐藏写归到当前操作。
            self.facts.complete_temp_definition_write_homes(producer)
        } else {
            self.facts.complete_local_definition_write_homes(local)
        };
        !homes.is_empty()
            && homes.iter().all(|home| {
                *home == target_home
                    || receiver.is_some_and(|receiver| *home == receiver)
                    || self
                        .result_move
                        .as_ref()
                        .is_some_and(|(owner, index, targets)| {
                            *owner == local && *index == definition && targets.contains(home)
                        })
            })
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "共享帧递归同时携带原槽、receiver/参数角色及当前 producer Def，不能把时点事实合并成布尔许可"
    )]
    fn expr(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        receiver: Option<HomeSlotKey>,
        callee_chain: bool,
        argument_home: bool,
        original_producer: Option<crate::hir::common::TempId>,
    ) -> Option<HirExpr> {
        if self.native.is_some()
            && self.dialect != DecompileDialect::Luau
            && let HirExpr::Unary(unary) = expr
            && unary.op == crate::hir::common::HirUnaryOpKind::Not
            && self.facts.unary_result_home(unary).is_some_and(|home| {
                home.slot() == slot && self.facts.unary_operand_home(unary) == Some(home)
            })
        {
            return self.inplace_not_chain(expr, before, slot);
        }
        if matches!(
            expr,
            HirExpr::Binary(_) | HirExpr::Integer(_) | HirExpr::Number(_)
        ) && let Some(result) = original_producer
            && self.has_constant_control(result)
        {
            return self.expanded_constant_control(expr, before, slot, result);
        }
        if matches!(expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            && let Some(result) = original_producer
            && self.has_value_expression(result)
        {
            return self.expanded_value_expression(expr, before, slot, result);
        }
        if self
            .native
            .is_some_and(|context| context.compared_choices.is_some())
            && matches!(expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            && let Some(result) = original_producer
            && self.has_compared_choice(result)
        {
            return self.expanded_compared_choice(expr, before, slot, result);
        }
        if let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = expr
            && self.native.is_some()
            && argument_home
            && let Some(layout) = self.scalar_selection_layout(
                logical,
                before,
                matches!(expr, HirExpr::LogicalAnd(_)),
            )
        {
            return self.scalar_selection(
                logical,
                before,
                slot,
                matches!(expr, HirExpr::LogicalAnd(_)),
                layout,
            );
        }
        if (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
            && let HirExpr::Binary(binary) = expr
            && let Some(restored) = self.expanded_captured_comparison(binary, before, slot)
        {
            return Some(restored);
        }
        match expr {
            HirExpr::Decision(decision) if self.native.is_some() && argument_home => {
                self.lookup_decision_value(decision, before, slot)
            }
            HirExpr::TempRef(temp)
                if self.native.is_some()
                    && self.facts.is_phi_carrier_temp(*temp)
                    && self.facts.trusted_temp_home_slot(*temp)
                        .is_some_and(|home| home.slot() < self.base) =>
            {
                // 低槽合流值已经由原控制域物化；这里只读取其 binding，
                // 不把各臂写入吸收到当前准备帧，也不退休 phi 的声明。
                Some(expr.clone())
            }
            HirExpr::TempRef(temp) if self.native.is_some() && original_producer == Some(*temp) => {
                let index = *self.temp_definitions.get(temp)?;
                let target_home = self.facts.trusted_temp_home_slot(*temp)?;
                if index >= before
                    || index < self.next_event
                    || target_home.slot() != slot
                    || self.native.is_some_and(|context| {
                        (context.closed.contains(&target_home)
                            && !self.facts.temp_definition_tbc_unprotected(*temp))
                            || context
                                .proto
                                .inline_dispositions
                                .temp(*temp)
                                .must_preserve()
                    })
                    || self
                        .facts
                        .complete_temp_definition_write_homes(*temp)
                        .iter()
                        .any(|home| *home != target_home)
                {
                    return None;
                }
                if let Some(&(offset, width)) = self.nil_group_members.get(&(index, HirBinding::Temp(*temp))) {
                    if !argument_home
                        || self.native.is_some_and(|context|
                            context.proto.temp_debug_locals[temp.index()].is_some()
                            || context.proto.temp_debug_scopes[temp.index()].is_some())
                    { return None; }
                    return self.consume_nil_group(index, offset, width, *temp);
                }
                let HirStmt::Assign(assign) = self.run[index] else {
                    return None;
                };
                let [value] = assign.values.fixed.as_slice() else {
                    return None;
                };
                // 尚未提升的 Temp 与 Local 使用同一帧角色；参数中的表仍在原参数槽
                // 分配，不能递归时误改成 callee 语境并丢失已有的原参数 Def。
                let value = self.expr(
                    value, index, slot, receiver, callee_chain, argument_home,
                    matches!(value, HirExpr::Closure(_) | HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Complex { .. } | HirExpr::VarArg).then_some(*temp),
                )?;
                self.finish_event(index)?;
                Some(value)
            }
            HirExpr::LocalRef(local) => {
                if self.interpolation_source(*local, before).is_some_and(|(_, _, _, target)|
                    self.facts.trusted_temp_home_slot(target).is_some_and(|home| home.slot() == slot)) {
                    return self.interpolation_local(*local, before, slot, original_producer, false);
                }
                if self.scalar_copy_source(*local, before).is_some_and(|(call, _, _)| {
                    self.expanded_scalar_home(call) == Some(HomeSlotKey::new(slot, 0))
                }) {
                    return self.expanded_scalar_local(*local, before, slot, original_producer);
                }
                if self.native.is_some()
                    && self.facts.trusted_local_home_slot(*local)
                        .is_some_and(|home| home.slot() < self.base)
                {
                    return Some(expr.clone());
                }
                // 匿名 Local 可被异槽 CALL+COPY 复用而没有统一 home；当前 producer
                // 仍可在 homes_match 中提供精确 Def，不能在此提前拒绝它。
                if let Some(index) = self.definition(*local, before) {
                    // 参数/返回之外的完整赋值帧也有原操作 Def。沿用 home 证明的
                    // 同一身份，避免未来版本的前缀保留要求冻结当前匿名准备值。
                    let original_producer = original_producer
                        .or_else(|| self.definition_producer(index));
                    if index < self.next_event
                        || !self.homes_match(*local, index, slot, receiver, original_producer)
                    {
                         return None;
                    }
                    let nil_group = self.nil_group_members.get(&(index, HirBinding::Local(*local))).copied();
                    let value = if nil_group.is_some() { &HirExpr::Nil } else { scalar_local(self.run[index])?.1 };
                    let constructor_result_unaliased = self.constructor_depth > 0
                        && (original_producer.is_some_and(|producer| {
                            self.facts.temp_definition_reference_unaliased(producer)
                                && self.facts.trusted_temp_home_slot(producer)
                                    .is_some_and(|home| home.slot() == slot)
                                && self.facts.promoted_local_for_temp(producer) == Some(*local)
                        }) || {
                            let accepts = |source| {
                                self.facts.operation_result_reference_unaliased(source)
                                && self.facts.operation_result_home(source)
                                    .is_some_and(|home| home.slot() == slot)
                                && self.facts.operation_result_temp(source).is_some_and(|temp| {
                                    self.facts.promoted_local_for_temp(temp) == Some(*local)
                                })
                            };
                            match value {
                                HirExpr::Call(call) => call.source_site.is_some_and(accepts),
                                HirExpr::Closure(closure) => closure.source_site.is_some_and(accepts),
                                HirExpr::TableConstructor(table) => table.sources
                                    .try_for_each_known(|source| accepts(source).then_some(())).is_some(),
                                _ => false,
                            }
                        });
                    if let Some(native) = self.native {
                        let tbc_unprotected_home = original_producer
                            .filter(|producer| self.facts.temp_definition_tbc_unprotected(*producer))
                            .and_then(|producer| self.facts.trusted_temp_home_slot(producer));
                        // callee 原 home 已在 NativeCallFrame 的 CALL 时点证明没有
                        // 打开的 ByRef；整链逐步核对同 home，未来 capture 不回溯生效。
                        if native
                            .proto
                            .local_debug_hints
                            .get(local.index())
                            .is_some_and(Option::is_some)
                            || native
                                .proto
                                .local_debug_scopes
                                .get(local.index())
                                .is_some_and(Option::is_some)
                            // 完整帧仍在值语境重发 NOT/比较，不把 Boolean 覆盖改为
                            // 分支极性；Unary 下方还核对原输出槽。其它保留理由不能消费。
                            || matches!(native.proto.inline_dispositions.local(*local),
                                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                                    if reasons.iter().any(|reason| match reason {
                                        crate::hir::common::HirInlineRetentionReason::BooleanValueContext => false,
                                        // 完整帧仍在原 callee/参数/返回或数组缓冲槽写入该版本，覆盖
                                        // 依赖的前缀；只退休声明，不提前释放原槽。
                                        crate::hir::common::HirInlineRetentionReason::RootOverwrite
                                        | crate::hir::common::HirInlineRetentionReason::PhysicalFramePrefix =>
                                            !((callee_chain || argument_home || self.constructor_depth > 0)
                                                && original_producer.is_some()),
                                        _ => true,
                                    }))
                            || (!callee_chain
                                && !argument_home
                                // SETLIST 输入 Def 或原 CALL/CLOSURE/分配签发当前缓冲值的
                                // 未捕获证明；未来复用此槽的 capture 不回溯到旧值版本。
                                // 后续读取与实际 capture 仍由整帧 preview 核对。
                                && !constructor_result_unaliased
                                && !self
                                    .facts
                                    .complete_local_definition_write_homes(*local)
                                    .is_disjoint(native.barred))
                            // 未来同 home 的 TBC 不保护此前的普通 Def；确切输入身份及
                            // 准备区边界已核对，资源初始化值和活动槽写入仍须保留。
                            || self
                                .facts
                                .complete_local_definition_write_homes(*local)
                                .iter()
                                .any(|home| native.closed.contains(home)
                                    && Some(*home) != tbc_unprotected_home)
                            || (native.proto.physical_root_locals.contains(local)
                                && self.constructor_depth == 0
                                // 闭包作为完整帧 RHS 仍在原槽创建；下方逐 Def 核对
                                // 创建、低槽 capture 与全部写域，不能提前释放原根。
                                && !(argument_home && original_producer.is_some()
                                    && matches!(value, HirExpr::Closure(_)))
                                && !(callee_chain
                                    && matches!(
                                        value,
                                        HirExpr::GlobalRef(_)
                                            | HirExpr::TableAccess(_)
                                            // 原 GETUPVAL callee 也在同一准备槽写入；
                                            // 下一次 CALL 的 callee Def 核对这一次覆盖。
                                            | HirExpr::UpvalueRef(_)
                                            | HirExpr::LocalRef(_)
                                            | HirExpr::ParamRef(_)
                                            | HirExpr::Closure(_)
                                            // 原 LOADK 的字符串 receiver 在此同槽重发；
                                            // 该 Local 先前作为循环根不冻结后来的常量版本。
                                            | HirExpr::String(_)
                                            // 完整 callee 链的每个 CALL 在下方核对同槽固定单结果，
                                            // 不把原结果作为独立快照删掉，也不改变下一次调用时点。
                                            | HirExpr::Call(_)
                                    )
                                    // CALL 参数语境总会写入该参数槽，区别于 SETTABLE 的 RK/
                                    // 现成寄存器语境；完整帧已经核对其原 home 和事件顺序。
                                    || argument_home
                                    || (receiver.is_some()
                                        && matches!(value, HirExpr::Call(call) if call.is_method()))
                                    || self.constructors.contains_key(&index)
                                    || crate::hir::value_facts::value_facts(value).is_boolean()))
                        {
                             return None;
                        }
                    }
                    if let Some((offset, width)) = nil_group {
                        if !argument_home { return None; }
                        return self.consume_nil_group(index, offset, width, original_producer?);
                    }
                    if self.constructors.contains_key(&index)
                        && let HirExpr::TableConstructor(table) = value
                    {
                        return self.constructor(index, table, slot);
                    }
                    // 本次短路参数 Def 已通过 homes_match 的完整写域及前述
                    // 保留约束；把整棵值树的结果槽传给叶比较，而非为每个谓词猜一个 phi。
                    // 末叶可返回任意值，其读取仍须匹配同一结果槽。homes_match 已核对
                    // 完整 epoch 身份；将它一起传递，避免比较叶把循环后的合法版本当作零 epoch。
                    let previous_boolean_frame = self.boolean_frame;
                    if matches!(self.dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                        && argument_home
                        && (crate::hir::value_facts::value_facts(value).is_boolean()
                            || matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)))
                        && let homes = original_producer.map_or_else(
                            || self.facts.complete_local_definition_write_homes(*local),
                            |producer| self.facts.complete_temp_definition_write_homes(producer),
                        )
                        && homes.len() == 1
                        && let Some(&home) = homes.first().filter(|home| home.slot() == slot)
                    {
                        self.boolean_frame = Some(home);
                    }
                    let condition = (!matches!(self.dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
                        && argument_home)
                        .then_some(original_producer)
                        .flatten()
                        .and_then(|result| {
                            let (home, expected) = self.facts.boolean_condition_frame(result)?;
                            (home.slot() == slot && crate::hir::value_facts::value_facts(value).is_boolean())
                                .then_some(UpvalueFrameUse { result, expected, reads: BTreeSet::new() })
                        });
                    let has_condition = condition.is_some();
                    let previous_condition = if has_condition {
                        std::mem::replace(&mut self.boolean_condition, condition)
                    } else { None };
                    let result = if self.dialect == DecompileDialect::Luau
                        && self.register_operand
                        && matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                        && let Some((initial, home)) = original_producer.and_then(|result| self.facts.copy_value_prewrite(result))
                        && {
                            let mut head = value;
                            while let HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) = head {
                                head = &logical.lhs;
                            }
                            // 已重建的值树不再读取原预写 local；后续外层帧沿正常
                            // 表达式证明消费它，不能再次索取已经退休的 MOVE。
                            matches!(head, HirExpr::LocalRef(local)
                                if self.facts.promoted_local_for_temp(initial) == Some(*local))
                        }
                    {
                        self.luau_copy_value(value, index, initial, home)
                    } else {
                        self.expr(
                            value,
                            index,
                            slot,
                            receiver,
                            callee_chain,
                            argument_home,
                            (matches!(value, HirExpr::Closure(_) | HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Complex { .. } | HirExpr::VarArg | HirExpr::ParamRef(_))
                                || matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                                    && original_producer.is_some_and(|result| self.has_compared_choice(result) || self.has_value_expression(result))
                                || matches!(value, HirExpr::Call(call) if self.expanded_call_result(call) == original_producer && original_producer.is_some()))
                                .then_some(original_producer)
                                .flatten(),
                        )
                    };
                    let condition_complete = if has_condition {
                        let consumed = self.boolean_condition.take().expect("active Boolean result frame");
                        self.boolean_condition = previous_condition;
                        consumed.reads.len() == consumed.expected
                    } else { true };
                    self.boolean_frame = previous_boolean_frame;
                    // 当前树必须承接该结果的所有原上值测试；少读或重复读取均不领整帧许可。
                    let result = result.filter(|_| condition_complete)?;
                    self.finish_event(index)?;
                    Some(result)
                } else {
                    let home = self.facts.trusted_local_home_slot(*local)?;
                    (home.slot() < self.base).then(|| expr.clone())
                }
            }
            HirExpr::ParamRef(param) => {
                let home = self.facts.trusted_param_home_slot(*param).or_else(|| {
                    let (copy, source, home) = self.parameter_copy?;
                    (source == *param && original_producer == Some(copy)).then_some(home)
                })?;
                (home.slot() < self.base).then(|| expr.clone())
            },
            HirExpr::VarArg
                if self.native.is_some()
                    && original_producer.and_then(|producer| self.facts.scalar_vararg_home(producer))
                        == Some(HomeSlotKey::new(slot, 0)) =>
            {
                // scalar expr 的省略号只重发一个结果；事件游标和原槽由外层准备帧核对。
                Some(HirExpr::VarArg)
            }
            HirExpr::Call(call) => {
                if call.interpolation.is_some()
                    || self.is_interpolation_copy(call, before, slot, original_producer) {
                    return self.interpolation_call(call, before, slot).map(|call| HirExpr::Call(Box::new(call)));
                }
                // 外层寄存器操作只限定 CALL 的结果槽；callee/参数由调用自己的
                // 原帧验证，不能把外层 RK 读取限制泄漏到 GETUPVAL 等调用准备。
                let previous = std::mem::replace(&mut self.register_operand, false);
                let rebuilt = self.expanded_seeded_predicate(call, before, slot, original_producer)
                    .or_else(|| self.expanded_calling_value(call, before, slot, original_producer))
                    .or_else(|| self.expanded_scalar_call(call, before, slot))
                    .or_else(|| self.call(call, before, slot, false, CallWidth::Single));
                self.register_operand = previous;
                rebuilt.map(|call| HirExpr::Call(Box::new(call)))
            }
            HirExpr::Closure(_)
                if self.constructor_depth > 0 && self.constructor_field_is_preserved(expr) =>
            {
                Some(expr.clone())
            }
            HirExpr::Closure(closure)
                if self.native.is_some()
                    && (argument_home || callee_chain)
                    && closure.creation.is_some()
                    && closure
                        .source_site
                        .and_then(|source| self.facts.operation_result_temp(source))
                        .is_some_and(|producer| {
                            Some(producer) == original_producer
                                && self
                                    .facts
                                    .trusted_temp_home_slot(producer)
                                    .is_some_and(|home| {
                                        home.slot() == slot
                                            && self
                                                .facts
                                                .complete_temp_definition_write_homes(producer)
                                                .iter()
                                                .copied()
                                                .eq(std::iter::once(home))
                                    })
                        })
                    && self.constructor_field_is_preserved(expr) =>
            {
                // 原 callee/参数/返回 CLOSURE 仍在同一槽创建；只消费对应帧的精确 Def 和低槽
                // capture，不按匿名函数外形或子 proto 猜测原分配。合成 factory 无此来源。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if (self.boolean_frame.is_some_and(|home| home.slot() == slot)
                    || (self.native.is_some() && argument_home
                        && [&binary.lhs, &binary.rhs].iter().all(|value| {
                            self.direct_home(value).is_some_and(|home| home.slot() < self.base)
                        })))
                    && self.luau_boolean_comparison(binary, slot) =>
            {
                // 已在低槽完成的比较可原样保留；CALL subject 仍由后面的完整帧分支逐事件证明。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
                    && (self.jit_lookup_comparison(binary, slot)
                        || self.jit_scalar_comparison(binary, slot)) =>
            {
                // 已嵌入的比较按原 operand 和 Boolean scratch 求值，不另提升声明。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
                    && let Some(preparations) = self.jit_cdata_comparison_preparations(binary, before, slot) =>
            {
                let mut scratch = slot;
                let mut values = [binary.lhs.clone(), binary.rhs.clone()];
                for (value, producer) in values.iter_mut().zip(preparations) {
                    if let Some(producer) = producer {
                        let previous = std::mem::replace(&mut self.register_operand, false);
                        let rebuilt = self.expr(value, before, scratch, None, false, true, Some(producer));
                        self.register_operand = previous;
                        scratch += 1;
                        *value = rebuilt?;
                    }
                }
                // 比较仍在两侧准备完成后执行，可能调用元方法；不提前缓存后续字段读取。
                let [lhs, rhs] = values;
                Some(HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
                    lhs, rhs, ..binary.as_ref().clone()
                })))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
                    && let Some(preparations) = self.luau_comparison_preparations(binary, before, slot) =>
            {
                // 比较值也可成为下一次比较的操作数；逐层保留 Boolean 结果槽，
                // 而字段读取只消费其原 GETTABLE Def，不从 Local 名称猜临时布局。
                let mut values = Vec::with_capacity(2);
                for (value, preparation) in [&binary.lhs, &binary.rhs].into_iter().zip(preparations) {
                    values.push(if let Some((home, producer)) = preparation {
                        if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
                            if self.has_value_expression(producer) {
                                self.expanded_value_expression(value, before, home.slot(), producer)?
                            } else if self.has_compared_choice(producer) {
                                self.expanded_compared_choice(value, before, home.slot(), producer)?
                            } else if let Some((initial, copy_home)) = self.facts.copy_value_prewrite(producer) {
                                if home != copy_home { return None }
                                self.luau_copy_value(value, before, initial, home)?
                            } else {
                            if let Some(prewrite) = self.facts.boolean_value_prewrite(producer) {
                                self.consume_boolean_prewrite(
                                    prewrite,
                                    self.facts.temp_definition_reference_unaliased(prewrite.0),
                                    value, before, home.slot(),
                                )?;
                            }
                            // 原内部 phi 已固定结果槽；只作真假测试的 CALL 使用其
                            // 上一槽，不能把 predicate 与真正的值叶都按结果槽重放。
                            self.luau_logical_value(value, before, home, Some(producer))?
                            }
                        } else {
                            self.expr(value, before, home.slot(), None, false, true, Some(producer))?
                        }
                    } else { value.clone() });
                }
                let rhs = values.pop().unwrap();
                let lhs = values.pop().unwrap();
                Some(HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
                    source_site: binary.source_site,
                    op: binary.op,
                    lhs,
                    rhs,
                })))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && argument_home
                    && self.low_left_comparison_rhs(binary, before, slot, true) =>
            {
                // 已选 Luau 内部 phi 优先由上方消费其预写。其余 RHS 仍按原 operand
                // scratch 重发，Luau 另保留其下的 Boolean 结果槽。
                let rhs_slot = if self.dialect == DecompileDialect::Luau {
                    self.boolean_operand_start(slot)
                } else { slot };
                let rhs = self.expr(&binary.rhs, before, rhs_slot, None, false, true, None)?;
                Some(HirExpr::Binary(Box::new(crate::hir::common::HirBinaryExpr {
                    rhs,
                    ..binary.as_ref().clone()
                })))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
                    && let Some((left, producer)) = self.luau_prepared_comparison_operand(binary, before, slot) =>
            {
                let operand = if left { &binary.lhs } else { &binary.rhs };
                let home = self.boolean_frame.filter(|home| home.slot() == slot)
                    .or_else(|| self.facts.comparison_result_temp(binary)
                        .and_then(|temp| self.facts.trusted_temp_home_slot(temp))
                        .filter(|home| home.slot() == slot))?;
                let previous_boolean_frame = self.boolean_frame.replace(home);
                let value = self.expr(operand, before, self.boolean_operand_start(slot), None, false, true, producer);
                self.boolean_frame = previous_boolean_frame;
                let value = value?;
                let mut rebuilt = binary.as_ref().clone();
                if left {
                    rebuilt.lhs = value;
                } else if self
                    .direct_home(&binary.lhs)
                    .is_some_and(|home| home.slot() < self.base)
                {
                    // 既有低槽不分配准备区，右侧操作数仍按原顺序求值；无需反转比较。
                    rebuilt.rhs = value;
                } else {
                    // HIR 的 Le/Lt 可以来自反向源码；重发时必须先计算原 scratch 的
                    // 操作数，再准备常量，否则 compileExprAuto 会交换两个暂存槽。
                    use crate::hir::common::HirBinaryOpKind::{Ge, Gt, Le, Lt};
                    rebuilt.op = match binary.op {
                        Le => Ge,
                        Lt => Gt,
                        Ge => Le,
                        Gt => Lt,
                        _ => return None,
                    };
                    rebuilt.lhs = value;
                    rebuilt.rhs = binary.lhs.clone();
                }
                Some(HirExpr::Binary(Box::new(rebuilt)))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && argument_home
                    && self.luau_boolean_comparison(binary, slot)
                    && self.facts.direct_binary_operand_home(binary, 0).is_some_and(|lhs| {
                        lhs.slot() < self.base
                            && self
                                .facts
                                .native_binary_layout(binary)
                                .is_some_and(|layout| {
                                    layout.lhs == Some(lhs)
                                        && layout
                                            .rhs
                                            .is_none_or(|rhs| rhs == HomeSlotKey::new(slot + 1, 0))
                                })
                    }) =>
            {
                // 低槽与字面量比较：原 RHS 是内嵌常量或 Boolean 目标上一槽的准备值。
                // Luau O0 重发该 LOADK，优化配置可用常量比较指令；不能接任意来源槽。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && argument_home
                    && binary.op == crate::hir::common::HirBinaryOpKind::Concat =>
            {
                self.concat(binary, before, slot)
            }
            HirExpr::Binary(binary)
                if self.dialect == DecompileDialect::Luau
                    && self.native.is_some()
                    && (argument_home || self.boolean_frame.is_some_and(|home| home.slot() == slot))
                    && binary.op == crate::hir::common::HirBinaryOpKind::Eq
                    && [&binary.lhs, &binary.rhs].iter().all(|value| match value {
                        HirExpr::Call(_) => true,
                        HirExpr::LocalRef(local) => {
                            self.definition(*local, before).is_some_and(|index| {
                                matches!(scalar_local(self.run[index]), Some((_, HirExpr::Call(_))))
                            })
                        }
                        _ => false,
                    }) =>
            {
                // Luau Boolean 参数预留目标槽，两个 CALL operand 各占其上的暂存槽。
                // CALL 仍从左到右且各取一个结果；比较可触发元方法，不能按 Boolean 结果判纯。
                let lhs = self.expr(&binary.lhs, before, slot + 1, None, false, true, None)?;
                let rhs = self.expr(&binary.rhs, before, slot + 2, None, false, true, None)?;
                Some(HirExpr::Binary(Box::new(
                    crate::hir::common::HirBinaryExpr {
                        source_site: binary.source_site,
                        op: binary.op,
                        lhs,
                        rhs,
                    },
                )))
            }
            HirExpr::Binary(binary)
                if self.dialect == DecompileDialect::Luau
                    && self.native.is_some()
                    && argument_home
                    && binary.op == crate::hir::common::HirBinaryOpKind::Eq
                    && [&binary.lhs, &binary.rhs].iter().all(|value| {
                        self.direct_home(value)
                            .is_some_and(|home| home.slot() < self.base)
                    }) =>
            {
                // 两个既有低槽直接比较，不创建 operand scratch；原参数 Def 的 home
                // 已由完整 CALL 核对。Boolean 仍写入同一参数槽，不转为谓词语境。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if matches!(self.dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                    && self.native.is_some()
                    && argument_home
                    && self.constructor_depth == 0
                    && self.indexed_key_base.is_none()
                    && (numeric_rk_arithmetic(binary)
                        || (self.dialect == DecompileDialect::Luau
                            && is_scalar_binary_operation(binary.op))) =>
            {
                // 算术按原低槽读取、结果槽及常量准备重发；RETURN 首项 COPY 与
                // 声明前缀仍由完整帧消费，不能凭算术外形单独退休前面的快照。
                self.direct_numeric_arithmetic(binary, slot)
                    .or_else(|| match self.dialect {
                        DecompileDialect::Luajit => self.register_arithmetic(binary, before, slot),
                        DecompileDialect::Luau => self.luau_prepared_arithmetic(binary, before, slot),
                        _ => None,
                    })
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && argument_home
                    && self.constructor_depth == 0
                    && self.indexed_key_base.is_none()
                    && self.dialect != DecompileDialect::Luau
                    && is_scalar_binary_operation(binary.op) =>
            {
                self.register_arithmetic(binary, before, slot)
            }
            // 数组里的比较仍使用下方完整 operand 证明；只有 Boolean 原结果恰为该元素槽
            // 才绕过算术入口，不能用 Branch 的 source site 冒充单指令结果 Def。
            HirExpr::Binary(binary)
                if (self.constructor_depth > 0 || self.indexed_key_base.is_some())
                    && !(self.constructor_depth > 0
                        && !matches!(self.dialect, DecompileDialect::Luau | DecompileDialect::Luajit)
                        && self.facts.comparison_result_temp(binary).is_some_and(|temp|
                            self.facts.trusted_temp_home_slot(temp) == Some(HomeSlotKey::new(slot, 0)))) =>
            {
                // 字段算术也可直接读取低槽，常量位于任一侧时沿用共享原槽证明。
                // 不交换操作数；RK 容量、结果写及可能的常量准备仍由同一 query 核对。
                if self.constructor_depth > 0 && numeric_rk_arithmetic(binary)
                    && let Some(value) = self.direct_numeric_arithmetic(binary, slot)
                {
                    return Some(value);
                }
                if (self.constructor_depth > 0
                    || (self.indexed_key_base.is_some()
                        && self.dialect != DecompileDialect::Luau
                        && self.facts.native_binary_layout(binary).is_some_and(|layout| {
                            layout.lhs.is_some()
                                && layout.lhs == binary.source_site
                                    .and_then(|source| self.facts.operation_result_home(source))
                        })))
                    && is_scalar_binary_operation(binary.op)
                {
                    // 同 home 索引与数组、record scratch 共用算术证明，保留 CLOSE 后的
                    // epoch；结果与左输入分槽的索引仍由下方原布局证明处理。
                    // 不改变左右读取、元方法与结果覆盖的顺序。
                    return if self.dialect == DecompileDialect::Luau {
                        self.luau_prepared_arithmetic(binary, before, slot)
                    } else {
                        self.register_arithmetic(binary, before, slot)
                    };
                }
                let layout = self.facts.native_binary_layout(binary)?;
                if let Some(input) = layout.lhs
                    && let Some(result) = self.facts.operation_result_home(binary.source_site?)
                    && self.indexed_key_base == Some(input.slot())
                    && input.slot() + 1 == slot
                    && result.slot() == slot
                    && self.dialect != DecompileDialect::Luau
                    && is_scalar_binary_operation(binary.op)
                {
                    // 动态 key 在低槽求值、高槽写回；低槽可复用已经 CLOSE 的 cell。
                    // 输入与结果各保留原 epoch，由共享算术 owner 验证完整准备和覆盖。
                    return self.register_arithmetic_inputs(binary, before, input, result);
                }
                if self.dialect == DecompileDialect::Luajit
                    && self.constructor_depth > 0
                    && self.facts.direct_comparison_result_temp(expr).is_some_and(|temp| {
                        self.facts.trusted_temp_home_slot(temp) == Some(HomeSlotKey::new(slot, 0))
                    })
                    && self.direct_home(&binary.lhs) == layout.lhs
                    && self.direct_home(&binary.rhs) == layout.rhs
                {
                    // Indexed 数组逐字段复用同一 scratch；比较后两路 Boolean 写必须
                    // 仍落在该槽，不能把 predicate 本身误当成结果写回。
                    return Some(expr.clone());
                }
                if self.facts.operation_result_home(binary.source_site?)
                    != Some(HomeSlotKey::new(slot, 0))
                    || !matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
                    || !is_scalar_binary_operation(binary.op)
                {
                    return None;
                }
                // 宽常量池的键算术在相邻槽 LOADK；它与普通寄存器算术共享
                // use→Def/RK 证明，不能套用只接受 Luau 高槽输入的布局。
                if self.indexed_key_base.is_some()
                    && self.dialect != DecompileDialect::Luau
                    && layout.lhs == Some(HomeSlotKey::new(slot, 0))
                    && layout.rhs == Some(HomeSlotKey::new(slot + 1, 0))
                {
                    return self.register_arithmetic(binary, before, slot);
                }
                let lhs_home = layout.lhs?;
                if let Some(rhs_home) = layout.rhs {
                    // Luau O0 不使用数字 RK：先在结果槽上方计算左侧，再在相邻槽
                    // 加载右侧常量。按原 use→Def 重发该写入，不能把任意寄存器视作常量。
                    if self.dialect != DecompileDialect::Luau
                        || self.indexed_key_base != Some(slot)
                        || lhs_home != HomeSlotKey::new(slot + 1, 0)
                        || rhs_home != HomeSlotKey::new(slot + 2, 0)
                        || self.facts.operation_input_preparation(binary.source_site?, &binary.rhs)
                            .map(|(_, home)| home) != Some(rhs_home)
                    {
                        return None;
                    }
                }
                // Luau 为 key 保留结果槽，在其上一槽计算复合左操作数；该 scratch
                // 随后可成为 RHS callee，必须在求 key 的事务内先完成并释放。
                if lhs_home != HomeSlotKey::new(slot, 0)
                    && self.direct_home(&binary.lhs) != Some(lhs_home)
                    && !(self.indexed_key_base == Some(lhs_home.slot())
                        && lhs_home == HomeSlotKey::new(lhs_home.slot(), 0)
                        && slot == lhs_home.slot() + 1)
                    && !(self.dialect == DecompileDialect::Luau
                        && self.indexed_key_base == Some(slot)
                        && lhs_home == HomeSlotKey::new(slot + 1, 0))
                {
                    return None;
                }
                // 索引操作数仍在原 scratch 槽求值，随后才写 key 与 RHS；
                // 完整赋值帧重发这次覆盖，不把物理根声明单独提前退休。
                let lhs = self.expr(
                    &binary.lhs,
                    before,
                    lhs_home.slot(),
                    None,
                    false,
                    self.indexed_key_base.is_some(),
                    None,
                )?;
                Some(HirExpr::Binary(Box::new(
                    crate::hir::common::HirBinaryExpr {
                        source_site: binary.source_site,
                        op: binary.op,
                        lhs,
                        rhs: binary.rhs.clone(),
                    },
                )))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && !matches!(
                        self.dialect,
                        DecompileDialect::Luajit | DecompileDialect::Luau
                    )
                    && matches!(
                        binary.op,
                        crate::hir::common::HirBinaryOpKind::Eq
                            | crate::hir::common::HirBinaryOpKind::Lt
                            | crate::hir::common::HirBinaryOpKind::Le
                    )
                    && self.direct_home(&binary.lhs).is_some_and(|home| {
                        home.slot() < self.base
                            && self
                                .facts
                                .native_binary_layout(binary)
                                .is_some_and(|layout| {
                                    layout.lhs == Some(home)
                                        && layout.rhs == Some(HomeSlotKey::new(slot, 0))
                                })
                    })
                    && (self.puc_comparison_prepared_rhs(&binary.rhs, before)
                        || matches!(binary.rhs, HirExpr::UpvalueRef(_))
                            && self.facts.binary_operand_preparation(binary, 1, &binary.rhs)
                                .is_some_and(|(_, home)| home == HomeSlotKey::new(slot, 0))) =>
            {
                // 左侧直接读取既有低槽，只有右侧计算需要 scratch，复用 Boolean 结果槽。
                // 不能套用左侧 CALL 已占一槽时的 RHS +1 规则，也不提前读取右侧字段。
                let rhs = if matches!(binary.rhs, HirExpr::UpvalueRef(_)) {
                    // 上方已核对原单次 GETUPVAL 的输入 Def 和 scratch；重发读取不走低槽 operand 路径。
                    binary.rhs.clone()
                } else {
                    self.register_operand(&binary.rhs, before, slot)?
                };
                Some(HirExpr::Binary(Box::new(
                    crate::hir::common::HirBinaryExpr {
                        rhs,
                        ..binary.as_ref().clone()
                    },
                )))
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && matches!(
                        binary.op,
                        crate::hir::common::HirBinaryOpKind::Eq
                            | crate::hir::common::HirBinaryOpKind::Lt
                            | crate::hir::common::HirBinaryOpKind::Le
                            | crate::hir::common::HirBinaryOpKind::Gt
                            | crate::hir::common::HirBinaryOpKind::Ge
                    )
                    && (matches!(binary.lhs, HirExpr::Call(_) | HirExpr::Unary(_))
                        || matches!(&binary.lhs, HirExpr::LocalRef(local)
                        if self.definition(*local, before).is_some_and(|index| {
                            matches!(scalar_local(self.run[index]),
                                Some((_, HirExpr::Call(_) | HirExpr::Unary(_))))
                        }))
                        || self.global_comparison_subject(binary, before, slot)
                        || self.comparison_lookup_subject(binary, before, slot)
                        || self.comparison_value_subject(binary, before, slot)
                        || self.in_place_arithmetic_comparison_subject(binary, before, slot)
                        || self.puc_comparison_value_subject(binary, before, slot)
                        || !matches!(
                            self.dialect,
                            DecompileDialect::Luajit | DecompileDialect::Luau
                        )
                            && match &binary.lhs {
                                HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => {
                                    self.facts.direct_binary_operand_home(binary, 0).is_some_and(|home| {
                                        home.slot() < self.base
                                            && (self.dialect == DecompileDialect::Lua51
                                                || self
                                                    .facts
                                                    .native_binary_layout(binary)
                                                    .is_some_and(|layout| {
                                                        layout.lhs == Some(home)
                                                            && (layout.rhs.is_none()
                                                                || self.facts.direct_binary_operand_home(binary, 1).is_some_and(|rhs|
                                                                    rhs.slot() < self.base && layout.rhs == Some(rhs)))
                                                    }))
                                    })
                                }
                                // 左侧 GETUPVAL 的准备独立于 RHS 是否使用 RK；右侧
                                // 低槽读取或相邻准备仍由 comparison_rhs_is_supported 核对。
                                HirExpr::UpvalueRef(_) => self
                                    .facts
                                    .binary_operand_preparation(binary, 0, &binary.lhs)
                                    .is_some_and(|(_, home)| home == HomeSlotKey::new(slot, 0)),
                                HirExpr::TableAccess(access) => self
                                    .facts
                                    .table_read_result_home(access)
                                    .is_some_and(|home| {
                                        home == HomeSlotKey::new(slot, 0)
                                            && (self
                                                .facts
                                                .native_table_read_layout(access)
                                                .is_some_and(|layout| {
                                                    (layout.key.is_none()
                                                        || self.facts.native_binary_layout(binary)
                                                            .is_some_and(|binary_layout| binary_layout.lhs == Some(home)))
                                                        && self.facts.table_read_base_home(access)
                                                            == Some(layout.base)
                                                        && layout.base.slot() < self.base
                                                })
                                                // 连续 GETTABLE 也可原位准备 Boolean subject；
                                                // 原比较的 RHS 可内嵌或直接读低槽；逐层读取的 base、
                                                // key 和事件顺序仍交下方 expr 的完整 register_lookup。
                                                // GETTABUP 不准备额外 base，仍可在原 Boolean 槽读取。
                                                || self.facts.upvalue_table_read_frame(access) == Some(home)
                                                || self.prepared_upvalue_lookup_base(access, before)
                                                    == Some(home)
                                                || matches!(access.base, HirExpr::TableAccess(_))
                                                    && self.facts.native_binary_layout(binary)
                                                        .is_some_and(|layout| layout.lhs == Some(home)
                                                            && (layout.rhs.is_none()
                                                                || self.direct_home(&binary.rhs).is_some_and(|rhs|
                                                                    rhs.slot() < self.base && layout.rhs == Some(rhs)))))
                                    }),
                                _ => false,
                            })
                    && self.comparison_rhs_is_supported(
                        binary, before,
                        slot + usize::from(self.dialect == DecompileDialect::Luau)
                            + usize::from(!self.direct_home(&binary.lhs).is_some_and(|home| home.slot() < self.base)),
                    ) =>
            {
                // Gt/Ge 是原 Lt/Le 的操作数方向恢复，native_binary_layout 已映射其输入；
                // 不能因展示方向改变而把同一 Boolean 参数永久留成独立 callee 帧。
                // 参数已有比较值语境；CALL/Unary/GETTABLE/算术 subject 保持原参数暂存槽，
                // 低槽 local/param 直接参与比较。比较本身可执行元方法，不据值类型判纯。
                // Luau 先保留 Boolean 目标，再在其上方求值 subject；PUC 复用目标槽。
                // 每个原 CALL/Unary 仍核对自己的精确结果 home，不按语法猜测已经移动成功。
                let subject_slot = slot + usize::from(self.dialect == DecompileDialect::Luau);
                let rhs_slot = subject_slot + usize::from(!self.direct_home(&binary.lhs).is_some_and(|home| home.slot() < self.base));
                let input = match &binary.lhs {
                    HirExpr::LocalRef(local) => self.definition(*local, before)
                        .and_then(|index| scalar_local(self.run[index]))
                        .map_or(&binary.lhs, |(_, value)| value),
                    value => value,
                };
                // RHS 的分支准备可跨过左侧 CALL 的结果；原 use→Def 证书仍约束
                // 本次读取。把该身份交给完整帧，避免把先前的前缀保留误当成永久屏障。
                let producer = self.facts.binary_operand_preparation(binary, 0, input)
                    .filter(|(_, home)| *home == HomeSlotKey::new(subject_slot, 0))
                    .map(|(producer, _)| producer)
                    .or_else(|| self.facts.binary_phi_operand(binary, 0)
                        .filter(|&temp| self.facts.trusted_temp_home_slot(temp)
                            .is_some_and(|home| home.slot() == subject_slot)));
                let lhs = self.expr(&binary.lhs, before, subject_slot, None, false, true, producer)?;
                let rhs = if self.dialect != DecompileDialect::Luau
                    && matches!(&binary.rhs, HirExpr::Binary(rhs) if rhs.op == crate::hir::common::HirBinaryOpKind::Concat)
                {
                    // CONCAT 的连续输入区在 lhs 结果之后；复用原 buffer 证明，而不是
                    // 把已拆出的 COPY 当成比较直接读取的既有低槽。
                    self.expr(&binary.rhs, before, rhs_slot, None, false, true, None)?
                } else if self.dialect == DecompileDialect::Lua51
                    && matches!(binary.rhs, HirExpr::LocalRef(local)
                        if self.definition(local, before).and_then(|index| scalar_local(self.run[index]))
                            .is_some_and(|(_, value)| tables::literal_rk(value)))
                {
                    let producer = self.facts.binary_phi_operand(binary, 1)?;
                    self.expr(&binary.rhs, before, rhs_slot, None, false, true, Some(producer))?
                } else if self.dialect != DecompileDialect::Luau
                    && (matches!(binary.rhs, HirExpr::LocalRef(_) | HirExpr::TableAccess(_))
                        || matches!(&binary.rhs, HirExpr::Binary(rhs)
                            if is_scalar_binary_operation(rhs.op)))
                {
                    // 已由比较布局签证的 RHS 是原寄存器操作数；读取须在 lhs 后原位重发。
                    self.register_operand(&binary.rhs, before, rhs_slot)?
                } else {
                    self.expr(&binary.rhs, before, rhs_slot, None, false, false, None)?
                };
                Some(HirExpr::Binary(Box::new(
                    crate::hir::common::HirBinaryExpr {
                        source_site: binary.source_site,
                        op: binary.op,
                        lhs,
                        rhs,
                    },
                )))
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && self.dialect != DecompileDialect::Luau
                    && unary.op == crate::hir::common::HirUnaryOpKind::Neg
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && self.facts.unary_operand_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && (matches!(unary.expr, HirExpr::Call(_))
                        || matches!(unary.expr, HirExpr::LocalRef(local)
                            if self.definition(local, before)
                                .and_then(|index| scalar_local(self.run[index]))
                                .is_some_and(|(_, value)| matches!(value, HirExpr::Call(_))))) =>
            {
                // CALL 的结果仍在原槽执行一元操作；输入 Def 必须属于
                // 当前运算，不能仅凭同槽把其它版本或 synthetic 极性包装收进帧。
                let input = match &unary.expr {
                    HirExpr::LocalRef(local) => scalar_local(self.run[self.definition(*local, before)?])?.1,
                    value => value,
                };
                let (producer, home) = self.facts.operation_input_preparation(unary.source_site?, input)?;
                if home != HomeSlotKey::new(slot, 0) {
                    return None;
                }
                let expr = self.expr(&unary.expr, before, slot, None, false, true, Some(producer))?;
                Some(HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                    expr,
                    ..unary.as_ref().clone()
                })))
            }
            HirExpr::Unary(unary)
                if self.native.is_some_and(|context| {
                    let Some(home) = self.facts.unary_result_home(unary) else { return false; };
                    (!context.barred.contains(&home)
                        || unary.source_site.is_some_and(|source|
                            self.facts.operation_result_reference_unaliased(source)))
                        && !context.closed.contains(&home)
                }) && self.dialect != DecompileDialect::Luau
                    && matches!(unary.expr, HirExpr::TableAccess(_) | HirExpr::LocalRef(_) | HirExpr::UpvalueRef(_) | HirExpr::Integer(_) | HirExpr::Number(_))
                    && self.facts.unary_operand_home(unary) == self.facts.unary_result_home(unary)
                    && self.facts.unary_result_home(unary).is_some_and(|home| home.slot() == slot) =>
            {
                // 原位一元操作复用原输入准备槽；读取与最终运算均在原 home 写回。
                let input = match &unary.expr {
                    HirExpr::LocalRef(local) => self.definition(*local, before)
                        .and_then(|index| scalar_local(self.run[index]))
                        .map_or(&unary.expr, |(_, value)| value),
                    value => value,
                };
                let value = if matches!(input, HirExpr::UpvalueRef(_) | HirExpr::Integer(_) | HirExpr::Number(_)) {
                    // 上值与数值字面量没有表达式 source_site；沿一元操作的原 use→Def 核对
                    // 该次准备及物理槽；物化为 Local 后仍沿同一证书消费，原一元运算不折叠。
                    let (producer, home) = self.facts.operation_input_preparation(unary.source_site?, input)?;
                    // 候选拒绝[ProofIncomplete]：原输入没有在本次一元结果槽准备，无法重发同一快照。
                    if Some(home) != self.facts.unary_result_home(unary) {
                        return None;
                    }
                    let previous = std::mem::replace(&mut self.register_operand, false);
                    let rebuilt = self.expr(&unary.expr, before, slot, None, false, true, Some(producer));
                    self.register_operand = previous;
                    rebuilt?
                } else {
                    self.register_operand(&unary.expr, before, slot)?
                };
                Some(HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                    source_site: unary.source_site,
                    op: unary.op,
                    expr: value,
                })))
            }
            HirExpr::Unary(unary)
                if matches!(self.dialect, DecompileDialect::Lua54 | DecompileDialect::Lua55)
                    && self.indexed_key_base == slot.checked_sub(1)
                    && matches!(unary.expr, HirExpr::UpvalueRef(_))
                    && self.facts.unary_result_home(unary).is_some_and(|home| home.slot() == slot)
                    && self.facts.operation_input_preparation(unary.source_site?, &unary.expr)
                        .is_some_and(|(_, home)| home.slot() + 1 == slot) =>
            {
                // 动态索引已预留高槽 key，一元输入借用尚未填充的低一槽 base。
                // 原独占 GETUPVAL Def 证明此次读取；后继 base 读取仍由索引 owner 重发。
                Some(expr.clone())
            }
            HirExpr::Unary(unary)
                if self.indexed_key_base.is_some()
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && self
                        .facts
                        .operation_input_preparation(unary.source_site?, &unary.expr)
                        .map(|(_, home)| home)
                        == Some(HomeSlotKey::new(
                            slot + usize::from(self.dialect == DecompileDialect::Luau),
                            0,
                        )) =>
            {
                // Luau 为一元结果预留一槽，在上一槽重新读取操作数；该 Def
                // 与 SETTABLE 的目标快照不同，不能合并两次上值读取。
                Some(expr.clone())
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && self.boolean_condition.is_some()
                    && unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not
                    && matches!(unary.expr, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) =>
            {
                // 极性包装不新增读取；整棵条件值树的原输入槽由结果身份签证。
                self.comparison_tree(expr, before, slot, argument_home)
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && matches!(unary.op, crate::hir::common::HirUnaryOpKind::Not | crate::hir::common::HirUnaryOpKind::Neg | crate::hir::common::HirUnaryOpKind::Length)
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && self.facts.unary_operand_home(unary) == Some(HomeSlotKey::new(
                        self.declaration_reserved_top.unwrap_or(0).max(slot + 1), 0)) =>
            {
                // Luau 在结果槽及已预留控制区上方求值复合操作数；原准备 Def 与 home
                // 同时匹配才消费其声明，让高槽的清根写仍由嵌套表达式实际执行。
                let input = match &unary.expr {
                    HirExpr::LocalRef(local) => {
                        let index = self.definition(*local, before)?;
                        scalar_local(self.run[index])?.1
                    }
                    value => value,
                };
                let operand_slot = self.declaration_reserved_top.unwrap_or(0).max(slot + 1);
                let logical = matches!(input, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_));
                let preparation = if logical { &unary.expr } else { input };
                let (producer, home) = self.facts.operation_input_preparation(unary.source_site?, preparation)?;
                if home != HomeSlotKey::new(operand_slot, 0) {
                    return None;
                }
                if logical && let Some(prewrite) = self.facts.boolean_value_prewrite(producer) {
                    // 原 NOT 读取合流值，Boolean 预写属于其输入准备区而非外层 CALL 参数。
                    // 按原 use→phi 身份消费预写，随后整棵值树仍逐事件核对原槽和求值顺序。
                    self.consume_boolean_prewrite(
                        prewrite,
                        self.facts.temp_definition_reference_unaliased(prewrite.0),
                        &unary.expr, before, operand_slot,
                    )?;
                }
                let expr = self.expr(&unary.expr, before, operand_slot, None, false, true, Some(producer))?;
                let mut rebuilt = unary.as_ref().clone();
                rebuilt.expr = expr;
                Some(HirExpr::Unary(Box::new(rebuilt)))
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && self.boolean_frame.is_some_and(|home| home.slot() == slot)
                    && unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not
                    && matches!(unary.expr, HirExpr::LogicalOr(_)) =>
            {
                // 原 false 预写属于合取值树。下推结构恢复引入的反形，使编译器
                // 在同一 Boolean 槽重发短路；叶的原 NOT/比较来源不得被取反 helper 消去。
                let HirExpr::LogicalOr(logical) = &unary.expr else { unreachable!() };
                let invert = |value: &HirExpr| match value {
                    HirExpr::Unary(inner) if inner.source_site.is_none()
                        && inner.op == crate::hir::common::HirUnaryOpKind::Not => inner.expr.clone(),
                    value => HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                        source_site: None,
                        op: crate::hir::common::HirUnaryOpKind::Not,
                        expr: value.clone(),
                    })),
                };
                let conjunction = HirExpr::LogicalAnd(Box::new(crate::hir::common::HirLogicalExpr { preserves_boolean_prewrite: false,
                    lhs: invert(&logical.lhs), rhs: invert(&logical.rhs),
                }));
                self.comparison_tree(&conjunction, before, slot, argument_home)
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not
                    && matches!(unary.expr, HirExpr::Binary(_)) =>
            {
                // 条件 owner 的反向分支用 synthetic Not 表示；保持 Boolean 比较语境，
                // 不借此移动一个原生 NOT 指令，也不增加可观察的求值事件。
                let expr = self.expr(&unary.expr, before, slot, None, false, true, None)?;
                let mut rebuilt = unary.as_ref().clone();
                rebuilt.expr = expr;
                Some(HirExpr::Unary(Box::new(rebuilt)))
            }
            HirExpr::Unary(unary)
                if self.native.is_some()
                    && self.facts.unary_result_home(unary).is_some_and(|home| home.slot() == slot)
                    && match unary.expr {
                        HirExpr::LocalRef(local) => self
                            .facts
                            .trusted_local_home_slot(local)
                            .is_some_and(|home| home.slot() < self.base),
                        HirExpr::ParamRef(param) => self
                            .facts
                            .trusted_param_home_slot(param)
                            .is_some_and(|home| home.slot() < self.base),
                        _ => false,
                    } =>
            {
                Some(expr.clone())
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
                if self.native.is_some()
                    && argument_home
                    && !matches!(self.dialect, DecompileDialect::Luajit | DecompileDialect::Luau)
                    && (matches!(logical.lhs, HirExpr::Call(_))
                        || matches!(logical.lhs, HirExpr::LocalRef(local)
                            if self.definition(local, before).is_some_and(|index|
                                matches!(scalar_local(self.run[index]), Some((_, HirExpr::Call(_)))))))
                    && self
                        .direct_home(&logical.rhs)
                        .is_some_and(|home| home.slot() < self.base) =>
            {
                // 普通值短路不同于 Boolean 比较树：CALL 先在原结果槽取一个值，
                // 仅选中右臂时读取既有低槽并写回该槽。rhs 不消费任何无条件 producer。
                // 外层原参数/CONCAT 帧及 Local 的完整写域仍核对最终结果和声明身份。
                // LocalId 可复用 callee、CALL 结果与合流值，左臂按 before 找上一值版本，
                // 不能把当前短路赋值自身当成 producer。
                let lhs = self.expr(&logical.lhs, before, slot, None, false, true, None)?;
                let rebuilt = Box::new(crate::hir::common::HirLogicalExpr { preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
                    lhs,
                    rhs: logical.rhs.clone(),
                });
                Some(if matches!(expr, HirExpr::LogicalAnd(_)) {
                    HirExpr::LogicalAnd(rebuilt)
                } else {
                    HirExpr::LogicalOr(rebuilt)
                })
            }
            HirExpr::LogicalOr(logical)
                if self.native.is_some() && self.dialect == DecompileDialect::Luau
                    && argument_home && matches!(logical.rhs, HirExpr::TableConstructor(_)) =>
            {
                self.luau_table_or_empty(logical, before, slot)
            }
            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
                if self.native.is_some() && self.dialect == DecompileDialect::Luau
                    && (argument_home || self.constructor_depth > 0) =>
            {
                // 参数、返回和数组元素都使用完整值树协议；仅作谓词的 CALL 在高槽
                // 准备，不能由逐叶比较证明把它压到结果槽，也不从右臂吸收无条件准备。
                // 外层参数/原 Def 已证明的结果身份包含生命周期 epoch；不能在进入
                // 值树时重建成零 epoch，否则同槽的末叶 CALL 会被误认为另一结果。
                let result = self.boolean_frame
                    .filter(|home| home.slot() == slot)
                    .unwrap_or_else(|| HomeSlotKey::new(slot, 0));
                self.luau_logical_value(expr, before, result, original_producer)
            }
            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
                if self.native.is_some() && self.pure_conditional_value(expr) =>
            {
                // 原 callee/参数的 phi home 已由调用布局与目标声明核对。这里只保留
                // 既有条件值表达式的低槽读取；不把无条件 producer 塞进短路分支。
                Some(expr.clone())
            }
            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) if self.native.is_some() => {
                self.comparison_tree(expr, before, slot, argument_home)
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && self.constructor_depth > 0
                    && matches!(table.allocation, HirTableAllocation::Luau(_)) =>
            {
                self.completed_luau_constructor(table, slot)
                    .or_else(|| self.complete_constructor(table, before, slot))
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && self.constructor_depth > 0
                    && matches!(table.allocation, HirTableAllocation::LuauTemplate { .. }) =>
            {
                self.complete_constructor(table, before, slot)
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && argument_home
                    && !matches!(table.allocation, HirTableAllocation::Synthetic)
                    && table.trailing_multivalue.is_none()
                    && table.fields.iter().all(|field| match field {
                        HirTableField::Array(value) => self.constructor_field_is_preserved(value),
                        HirTableField::Record(record) => {
                            self.constructor_field_is_preserved(&record.key)
                                && self.constructor_field_is_preserved(&record.value)
                        }
                    }) =>
            {
                // 原参数 Def 已签发 dispatch 交接，完整 CALL 保持原表 home、分配与字段
                // 顺序。只收回独立 binding，不在这里吸收字段 producer 或重建表布局。
                Some(expr.clone())
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && argument_home
                    && self.dialect == DecompileDialect::Luajit
                    && matches!(table.allocation, HirTableAllocation::Indexed { array_capacity, .. } if array_capacity > 0)
                    && table.fields.iter().all(|field| matches!(field, HirTableField::Array(_))) =>
            {
                self.completed_jit_array(table, slot)
                    .or_else(|| self.complete_constructor(table, before, slot))
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && argument_home
                    && self.dialect == DecompileDialect::Luau
                    && matches!(table.allocation, HirTableAllocation::Luau(_)) =>
            {
                self.completed_luau_constructor(table, slot)
                    .or_else(|| self.complete_constructor(table, before, slot))
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && argument_home
                    && (matches!(table.allocation, HirTableAllocation::PucBatched(_))
                        || self.dialect == DecompileDialect::Luau
                            && matches!(table.allocation, HirTableAllocation::LuauTemplate { .. })
                        || self.dialect == DecompileDialect::Luajit
                            && table.trailing_multivalue.is_none()
                            && (matches!(table.allocation, HirTableAllocation::Template { .. })
                                || matches!(table.allocation, HirTableAllocation::Indexed { array_capacity: 0, .. })
                                    && table.fields.iter().all(|field| matches!(field, HirTableField::Record(_))))) =>
            {
                // TDUP 的动态数组项已由字段 owner 放回原 nil 槽；与 record 一样，
                // 完整帧继续核对内部低槽读取、准备写和容量，不限于纯常量模板。
                self.complete_constructor(table, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && self.constructor_depth > 0
                    && self.facts.upvalue_table_read_frame(access)
                        == Some(HomeSlotKey::new(slot, 0)) =>
            {
                // 原 GETTABUP 直接读取 cell，不另占 base 槽；字段仍在原 scratch
                // 求值，保留原上值与键，不能按 GETTABLE 的低槽 base 合同拒绝。
                Some(expr.clone())
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && ((matches!(access.key, HirExpr::Binary(_) | HirExpr::Unary(_) | HirExpr::LocalRef(_))
                        && self.facts.native_table_read_layout(access).is_some_and(|layout| layout.key.is_some()))
                        || ((self.constructor_depth > 0 || callee_chain)
                            && matches!(access.base, HirExpr::TableAccess(_)))
                        || ((argument_home || self.constructor_depth > 0)
                            && (matches!(access.base, HirExpr::Call(_) | HirExpr::TableAccess(_))
                                || self.prepared_upvalue_lookup_base(access, before).is_some()
                                || matches!(access.base, HirExpr::LocalRef(local)
                                    if self.definition(local, before)
                                        .and_then(|index| scalar_local(self.run[index]))
                                        .is_some_and(|(_, value)| matches!(value,
                                            HirExpr::Call(_) | HirExpr::TableAccess(_))))
                                || self.native.is_some_and(|context| context.expanded_callees.is_some())
                                    && self.facts.native_table_read_layout(access).is_some_and(|layout|
                                        layout.base == HomeSlotKey::new(slot + 2, 0))))) =>
            {
                // 动态键可以尚未树化；原准备 Def 与当前值交给 lookup 共同核对。
                // 已树化的构造器字段或 callee 链逐层核对同槽读取，不另物化中间 base。
                self.luau_lookup(access, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && (self.register_operand
                        // 字段读取也可能在数组缓冲中准备 base，再同槽 GETTABLE。
                        // 共享寄存器 owner 同时核对现成低槽和同槽准备，不按 base 的外形分流。
                        || self.constructor_depth > 0
                        || self.dialect == DecompileDialect::Luau && (argument_home || callee_chain)
                            && self.facts.native_table_read_layout(access).is_some_and(|layout|
                                layout.base.slot() < self.base
                                    && layout.key.is_some_and(|key| key.slot() < self.base))
                        || self.dialect != DecompileDialect::Luau
                            && (matches!(access.base, HirExpr::Call(_) | HirExpr::TableAccess(_))
                        || self.prepared_upvalue_lookup_base(access, before).is_some()
                        || !matches!(
                            access.key,
                            HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                        ))) =>
            {
                // 寄存器操作数无论直接树化还是包在准备 local 中，都消费同一读取布局。
                // Luau 参数和 callee 只有 base/key 均在既有低槽时借用此入口，
                // GETTABLE 仍写入原准备槽，不套用高槽 base 的布局。
                // JIT 的 FR2 参数偏移仍由调用帧负责，lookup 不把中间结果误当独立低槽。
                // 调用结果的字段读取也由此逐层重放 CALL→GETTABLE 的原同槽覆盖。
                self.register_lookup(access, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && matches!(
                        access.key,
                        HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                    )
                    && matches!(
                        access.base,
                        HirExpr::LocalRef(_)
                            | HirExpr::ParamRef(_)
                            | HirExpr::UpvalueRef(_)
                            | HirExpr::GlobalRef(_)
                    ) =>
            {
                if self.constructor_depth > 0 && !callee_chain {
                    let layout = self.facts.native_table_read_layout(access)?;
                    if self.facts.table_read_result_home(access) != Some(HomeSlotKey::new(slot, 0))
                        || layout.key.is_some()
                        || self.facts.table_read_base_home(access) != Some(layout.base)
                        || layout.base.slot() >= self.base
                    {
                        return None;
                    }
                }
                let mut access = access.as_ref().clone();
                access.base = self.expr(
                    &access.base,
                    before,
                    slot,
                    None,
                    callee_chain,
                    argument_home,
                    None,
                )?;
                Some(HirExpr::TableAccess(Box::new(access)))
            }
            HirExpr::UpvalueRef(_) if self.native.is_some() && !self.register_operand => {
                Some(expr.clone())
            }
            HirExpr::GlobalRef(global) => {
                if self.register_operand
                    && self.facts.global_read_frame(global, self.dialect).is_none_or(|home| home.slot() != slot)
                { return None; }
                if let Some(temp) = self.facts.global_key_preparation(global)
                    && let Some((index, key_expr)) = self.temp_definitions.get(&temp)
                        .map(|&index| (index, HirExpr::TempRef(temp)))
                        .or_else(|| {
                            let local = self.facts.promoted_local_for_temp(temp)?;
                            Some((self.definition(local, before)?, HirExpr::LocalRef(local)))
                        })
                {
                    // GlobalRef 发射仍包含宽常量键 LOADK；按原 key Def 消费这次
                    // 隐式准备事件，不能留下一个独立 Temp 阻断外层构造帧。
                    let key_home = self.facts.trusted_temp_home_slot(temp)?;
                    let adjacent_key = key_home.slot() == slot + 1
                        && self.facts.global_read_frame(global, self.dialect).is_some_and(|home| home.slot() == slot)
                        && self.literal_uses_rk(&HirExpr::String(global.key.clone()), None) == Some(false);
                    if index >= before || (key_home.slot() != slot && !adjacent_key) {
                        return None;
                    }
                    let previous = std::mem::replace(&mut self.register_operand, false);
                    let key = self.expr(&key_expr, before, key_home.slot(), None, false, true, Some(temp));
                    self.register_operand = previous;
                    if key != Some(HirExpr::String(global.key.clone())) { return None; }
                }
                Some(expr.clone())
            }
            HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Complex { .. }
                if self.dialect == DecompileDialect::Luajit
                    && self.native.is_some()
                    && !self.register_operand
                    && original_producer.is_some_and(|producer| {
                        self.facts.trusted_temp_home_slot(producer).is_some_and(|home| {
                            home.slot() == slot
                                && !self.native.unwrap().closed.contains(&home)
                                && self.facts.complete_temp_definition_write_homes(producer)
                                    .iter().copied().eq([home])
                        })
                    }) =>
            {
                // cdata 常量是原 LOADK 的寄存器准备，不能当作无准备的数字 RK。
                // 只有携带输入 use→Def 身份的完整帧才可在同一槽重发它。
                Some(expr.clone())
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => Some(expr.clone()),
            // 其它操作有各自的目标槽和分配协议，不能借当前调用帧证明一并移动。
            _ => None,
        }
    }

    /// 原 CONCAT 的整个操作数区一起重发：求值从左到右，合并与旧槽覆盖仍从右到左。
    /// 只展开同一原指令的 synthetic 右链，不能把两个原 CONCAT 合并为一条。
    fn concat(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        // Luau 的单上值赋值先预留 RHS 结果，再分配 CONCAT 操作数区；
        // PUC/JIT 的结果则覆盖首操作数。调用方仍须证明该表达式语境的原入口。
        let operand_start = slot + usize::from(self.dialect == DecompileDialect::Luau);
        let result = self.facts.operation_result_home(binary.source_site?)?;
        // 槽距决定编译布局，原 source site 决定值版本；循环后的新 epoch
        // 仍可使用同一准备位置，不能把它重置为入口的 epoch 0。
        if result.slot() != slot {
            return None;
        }
        self.concat_in_frame(binary, before, operand_start, result)
    }

    /// 既有低槽赋值不预留新结果 local；输入区与原结果槽分别由赋值 owner 核对。
    fn concat_in_frame(
        &mut self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        operand_start: usize,
        result: HomeSlotKey,
    ) -> Option<HirExpr> {
        let buffer = self.facts.native_concat_buffer(binary)?;
        if buffer.start.index() != operand_start
            || self.facts.operation_result_home(binary.source_site?) != Some(result)
        {
            return None;
        }
        let mut operands = vec![&binary.lhs];
        let mut cursor = &binary.rhs;
        while let HirExpr::Binary(next) = cursor
            && next.op == crate::hir::common::HirBinaryOpKind::Concat
            && next.source_site.is_none()
        {
            operands.push(&next.lhs);
            cursor = &next.rhs;
        }
        operands.push(cursor);
        if operands.len() != buffer.len {
            return None;
        }
        let mut values = Vec::with_capacity(operands.len());
        for (offset, operand) in operands.into_iter().enumerate() {
            let value = self.expr(
                operand,
                before,
                operand_start + offset,
                None,
                false,
                true,
                self.facts.concat_operand_value(binary, offset),
            )?;
            if matches!(&value, HirExpr::Binary(nested)
                if nested.op == crate::hir::common::HirBinaryOpKind::Concat)
            {
                return None;
            }
            values.push(value);
        }
        crate::hir::common::HirBinaryExpr::concat(binary.source_site?, values)
    }

    /// 全局读取可触发环境元方法；原读取和比较必须使用同一准备槽，事件仍由 expr 核对。
    fn global_comparison_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        if self.dialect != DecompileDialect::Luau {
            let value = if let HirExpr::LocalRef(local) = binary.lhs {
                let Some(index) = self.definition(local, before) else {
                    return false;
                };
                let Some((_, value)) = scalar_local(self.run[index]) else {
                    return false;
                };
                value
            } else {
                &binary.lhs
            };
            let home = HomeSlotKey::new(slot, 0);
            return matches!(value, HirExpr::GlobalRef(global)
                if self.facts.global_read_frame(global, self.dialect) == Some(home))
                && self
                    .facts
                    .native_binary_layout(binary)
                    .is_some_and(|layout| layout.lhs == Some(home));
        }
        if self.dialect != DecompileDialect::Luau
            || binary.op != crate::hir::common::HirBinaryOpKind::Eq
            || !self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.lhs == Some(HomeSlotKey::new(slot + 1, 0)) && layout.rhs.is_none()
                })
        {
            return false;
        }
        let HirExpr::LocalRef(local) = binary.lhs else {
            return false;
        };
        self.definition(local, before).is_some_and(|index| {
            matches!(scalar_local(self.run[index]), Some((_, HirExpr::GlobalRef(global)))
                if global.key.as_utf8().is_some_and(|name| self.dialect.is_identifier_name(name)))
        })
    }

    /// 原左侧索引先在 Boolean 目标槽求值；物化 local 只转交这次读取，不借同槽其它版本。
    fn comparison_lookup_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        let home = HomeSlotKey::new(
            slot + usize::from(self.dialect == DecompileDialect::Luau),
            0,
        );
        let (access, access_before) = match &binary.lhs {
            HirExpr::TableAccess(access) => (access, before),
            HirExpr::LocalRef(local) => {
                let Some(index) = self.definition(*local, before) else {
                    return false;
                };
                let Some((_, HirExpr::TableAccess(access))) = scalar_local(self.run[index]) else {
                    return false;
                };
                if self.facts.trusted_local_home_slot(*local) != Some(home) {
                    return false;
                }
                (access, index)
            }
            _ => return false,
        };
        let prepared_base = match &access.base {
            HirExpr::LocalRef(local) => self
                .definition(*local, access_before)
                .and_then(|index| scalar_local(self.run[index]))
                .map_or(&access.base, |(_, value)| value),
            value => value,
        };
        matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                if self.facts.operation_result_reference_unaliased(source))
            && self.facts.table_read_result_home(access) == Some(home)
            && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(home))
            && (self.facts.upvalue_table_read_frame(access) == Some(home)
                || self
                .facts
                .native_table_read_layout(access)
                .is_some_and(|layout| {
                    (layout.base.slot() < self.base
                        && self.facts.table_read_base_home(access) == Some(layout.base)
                        && layout.key.is_none_or(|key| {
                            key.slot() < self.base && self.direct_home(&access.key) == Some(key)
                        }))
                        // 全局读取或同槽连续 GETTABLE 可先物化为比较 subject。这里只识别原结果；
                        // expr 的 register_lookup 仍逐层验证 base/key 的 Def、写槽和事件。
                        || (self.dialect != DecompileDialect::Luau && layout.base == home
                            && matches!(access.base, HirExpr::TableAccess(_) | HirExpr::GlobalRef(_)))
                        // 上值 base 的原准备同样可先物化为比较 subject；与直接树化
                        // 路径消费同一证书，键和两次读取顺序仍由 register_lookup 验证。
                        || (layout.base == home
                            && self.prepared_upvalue_lookup_base(access, access_before) == Some(layout.base))
                        // 单结果 CALL 也可在原槽继续查表；准备证书绑定这次
                        // GETTABLE 的唯一输入 Def，不能借同槽的另一版结果。
                        || (layout.base == home
                            && matches!(prepared_base, HirExpr::Call(_))
                            && matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                                if self.facts.operation_input_preparation(source, prepared_base)
                                    .is_some_and(|(_, prepared)| prepared == layout.base)))
                }))
    }

    /// 内层比较的 Boolean 写回占外层左操作数槽；外层检查仍须原样重发。
    fn puc_comparison_value_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        if matches!(
            self.dialect,
            DecompileDialect::Luajit | DecompileDialect::Luau
        ) {
            return false;
        }
        let value = match &binary.lhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value)),
            value => Some(value),
        };
        let Some(HirExpr::Binary(inner)) = value else {
            return false;
        };
        let home = HomeSlotKey::new(slot, 0);
        self.facts
            .comparison_result_temp(inner)
            .is_some_and(|result| self.facts.trusted_temp_home_slot(result) == Some(home))
            && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(home))
    }

    fn in_place_arithmetic_comparison_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        if self.dialect == DecompileDialect::Luau {
            return false;
        }
        let value = match &binary.lhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value)),
            value => Some(value),
        };
        let Some(HirExpr::Binary(arithmetic)) = value else {
            return false;
        };
        let Some(home) = arithmetic
            .source_site
            .and_then(|source| self.facts.operation_result_home(source))
            .filter(|home| home.slot() == slot)
        else {
            return false;
        };
        // 算术先在 Boolean 目标槽求值，比较随后读取同一槽；内部操作数及
        // 求值事件仍由 register_arithmetic 证明。沿原 Def 保留 CLOSE 后的 epoch，
        // 不能用 epoch=0 的占位身份拒绝循环下一轮的同槽准备。
        self.puc_comparison_prepared_rhs(&binary.lhs, before)
            && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(home))
    }

    fn puc_comparison_prepared_rhs(&self, rhs: &HirExpr, before: usize) -> bool {
        let value = match rhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value)),
            value => Some(value),
        };
        // 单值 CALL 也在比较结果槽准备；其参数、派发与结果写回由 register_operand
        // 转交完整 call builder，不能套用双侧都占 scratch 的相邻槽规则。
        matches!(value, Some(HirExpr::TableAccess(_) | HirExpr::Call(_)))
            || matches!(value, Some(HirExpr::Unary(unary))
                if unary.op == crate::hir::common::HirUnaryOpKind::Not)
            || matches!(value, Some(HirExpr::Binary(binary)) if is_scalar_binary_operation(binary.op))
    }

    fn comparison_value_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        let Some(result) = self.facts.binary_phi_operand(binary, 0) else {
            return false;
        };
        let value = match &binary.lhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]))
                .map(|(_, value)| value),
            value => Some(value),
        };
        let inner = match value {
            Some(HirExpr::Binary(inner)) => Some(inner.as_ref()),
            Some(HirExpr::Unary(unary))
                if unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not =>
            {
                match &unary.expr {
                    HirExpr::Binary(inner) => Some(inner.as_ref()),
                    _ => None,
                }
            }
            _ => None,
        };
        // 内层比较在外层 subject 的原槽完成物化；它仍是一个值，不能并成外层条件链。
        // PUC/JIT 的短路值树也可作为这次比较的 phi 输入；原 use 固定结果身份，
        // 后续 comparison_tree 逐叶核对同槽准备，不重复扫描或吞掉外层显式比较。
        (inner.is_some_and(|inner| self.facts.comparison_result_temp(inner) == Some(result))
            || self.dialect != DecompileDialect::Luau
                && matches!(value, Some(HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))))
            && self
                .facts
                .trusted_temp_home_slot(result)
                .is_some_and(|home| {
                    home.slot() == slot + usize::from(self.dialect == DecompileDialect::Luau)
                })
    }

    fn comparison_literal_layout(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        value: &HirExpr,
        slot: usize,
    ) -> bool {
        if matches!(
            self.dialect,
            DecompileDialect::Luajit | DecompileDialect::Luau
        ) {
            return true;
        }
        let Some(layout) = self.facts.native_binary_layout(binary) else {
            return false;
        };
        let sources = binary
            .source_site
            .map(crate::hir::common::HirOperationSources::Single);
        // 5.4/5.5 的小整数（含整数值浮点）直接编码在比较指令中，独立于常量池容量。
        let immediate = matches!(
            self.dialect,
            DecompileDialect::Lua54 | DecompileDialect::Lua55
        ) && match value {
            HirExpr::Integer(value) => (-127..=128).contains(value),
            HirExpr::Number(value) => value.fract() == 0.0 && (-127.0..=128.0).contains(value),
            _ => false,
        };
        if immediate {
            return layout.rhs.is_none();
        }
        if matches!(
            self.dialect,
            DecompileDialect::Lua54 | DecompileDialect::Lua55
        ) && matches!(
            binary.op,
            crate::hir::common::HirBinaryOpKind::Lt
                | crate::hir::common::HirBinaryOpKind::Le
                | crate::hir::common::HirBinaryOpKind::Gt
                | crate::hir::common::HirBinaryOpKind::Ge
        ) {
            // 5.4/5.5 的有序比较没有 RK 常量形式；非立即数字面量必须先写寄存器。
            // 常量池容量只影响 EQK 等指令，不能据此拒绝原 LOAD 的相邻准备槽。
            return layout.rhs.is_some_and(|home| home.slot() == slot);
        }
        match layout.rhs {
            None => {
                self.literal_uses_rk(value, sources.as_ref().map(|sources| (sources, true)))
                    == Some(true)
            }
            Some(home) => {
                home.slot() == slot
                    && self.literal_uses_rk(value, sources.as_ref().map(|sources| (sources, true)))
                        == Some(false)
            }
        }
    }

    fn comparison_rhs_is_supported(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        let expr = &binary.rhs;
        if self.direct_home(expr).is_some_and(|home| {
            home.slot() < self.base
                && self
                    .facts
                    .native_binary_layout(binary)
                    .is_some_and(|layout| {
                        layout.rhs == Some(home)
                            && (self.dialect != DecompileDialect::Luau
                                || layout.lhs == Some(HomeSlotKey::new(slot - 1, 0)))
                    })
        }) {
            // 原比较直接在 CALL 后读取低槽 local/param，不另写 operand scratch。
            // 即使 CALL 改写 captured cell，这次读取仍保留在其后；提前 COPY 的高槽快照
            // 不借用此许可。原调用帧与整个声明前后缀继续由共享 builder/事务核对。
            return true;
        }
        if matches!(
            expr,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        ) {
            return self.comparison_literal_layout(binary, expr, slot);
        }
        let value = if let HirExpr::LocalRef(local) = expr {
            let Some(index) = self.definition(*local, before) else {
                return false;
            };
            if self.facts.trusted_local_home_slot(*local) != Some(HomeSlotKey::new(slot, 0)) {
                return false;
            }
            let Some((_, value)) = scalar_local(self.run[index]) else {
                return false;
            };
            value
        } else {
            expr
        };
        if tables::literal_rk(value) {
            return self.comparison_literal_layout(binary, value, slot);
        }
        if let HirExpr::Call(call) = value {
            let home = HomeSlotKey::new(slot, 0);
            // RHS 调用在左值之后占相邻 scratch；比较必须直接消费该单结果。
            // 这里只确认入口，callee/参数和事件顺序仍由 expr 的 CALL 证明核对。
            return self.facts.native_call_frame(call).is_some_and(|frame| {
                frame.home == home
                    && matches!(frame.results, Some(ResultPack::Fixed(range))
                        if range.start.index() == slot && range.len == 1)
            }) && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.lhs == Some(HomeSlotKey::new(slot - 1, 0)) && layout.rhs == Some(home)
                });
        }
        if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            && self.pure_conditional_value(value)
        {
            // CALL 先占据 lhs 槽，条件 RHS 随后在相邻槽选择原值。
            // 只接受无额外事件的条件树；实际 producer 与整条准备区仍由 expr 消费。
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                        && layout.rhs == Some(HomeSlotKey::new(slot, 0))
                });
        }
        if self.dialect != DecompileDialect::Luau {
            let comparison = match value {
                HirExpr::Binary(inner) => Some(inner.as_ref()),
                HirExpr::Unary(unary)
                    if unary.source_site.is_none()
                        && unary.op == crate::hir::common::HirUnaryOpKind::Not =>
                {
                    match &unary.expr {
                        HirExpr::Binary(inner) => Some(inner.as_ref()),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(inner) = comparison
                && let Some(result) = self.facts.comparison_result_temp(inner)
            {
                let home = HomeSlotKey::new(slot, 0);
                // 内层双分支 Boolean 写回仍占原 RHS 槽；外层比较必须保留，
                // 不根据 Boolean 值域消去检查。内层输入与事件再由 expr 递归证明。
                return self.facts.trusted_temp_home_slot(result) == Some(home)
                    && self
                        .facts
                        .native_binary_layout(binary)
                        .is_some_and(|layout| {
                            layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                                && layout.rhs == Some(home)
                        });
            }
        }
        if let HirExpr::Binary(operation) = value
            && (operation.op == crate::hir::common::HirBinaryOpKind::Concat
                || is_scalar_binary_operation(operation.op))
            && self.dialect != DecompileDialect::Luau
        {
            let home = HomeSlotKey::new(slot, 0);
            // 算术与 CONCAT 都可在已保留的左操作数之后完成 RHS；原结果 home
            // 必须是比较读取的相邻槽。内部读取、常量准备及运算顺序仍由各自 owner 重放。
            return operation
                .source_site
                .and_then(|source| self.facts.operation_result_home(source))
                == Some(home)
                && self
                    .facts
                    .native_binary_layout(binary)
                    .is_some_and(|layout| {
                        layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                            && layout.rhs == Some(home)
                    });
        }
        if let HirExpr::TableAccess(access) = value {
            let home = HomeSlotKey::new(slot, 0);
            // 比较先保留 lhs 结果，再为 rhs lookup 分配一槽。
            // 原比较、GETTABLE 输出和低槽 base 必须一致；不把 CALL 前的 COPY
            // 当作 CALL 后读取。PUC/JIT 动态 key 使用 lookup 结果槽的准备区；
            // Luau 则在 lookup 结果高一槽准备 key；实际表达式继续由方言 lookup owner 验证。
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.rhs == Some(home) && layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                })
                && self.facts.table_read_result_home(access) == Some(home)
                && (self.completed_global_lookup(value, slot)
                    || self
                        .facts
                        .native_table_read_layout(access)
                        .is_some_and(|layout| {
                            (layout.key.is_none()
                                || self.dialect != DecompileDialect::Luau
                                    && layout.key == Some(home)
                                || self.dialect == DecompileDialect::Luau
                                    && layout.key == Some(HomeSlotKey::new(slot + 1, 0)))
                                && layout.base.slot() < self.base
                                && self.facts.table_read_base_home(access) == Some(layout.base)
                        }));
        }
        if let HirExpr::Unary(unary) = value
            && unary.op == crate::hir::common::HirUnaryOpKind::Neg
        {
            let home = HomeSlotKey::new(slot, 0);
            // 右侧一元运算先在相邻槽完成，再由比较读取；具体输入及元方法
            // 仍由 expr 的原一元操作证明消费，不能只凭 Neg 外形提前重读其输入。
            return self.facts.unary_result_home(unary) == Some(home)
                && self
                    .facts
                    .native_binary_layout(binary)
                    .is_some_and(|layout| {
                        layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                            && layout.rhs == Some(home)
                    });
        }
        matches!(value, HirExpr::Unary(unary)
            if unary.op == crate::hir::common::HirUnaryOpKind::Not
                && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                && self.direct_home(&unary.expr).is_some_and(|home| home.slot() < self.base))
    }

    /// PUC/JIT 的已计算输入与比较 Boolean 共用结果槽；完整输入树的
    /// 准备、事件次序和结果绑定继续由 expr 与批次预览核对。
    fn in_place_comparison_input(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        if self.dialect == DecompileDialect::Luau {
            return false;
        }
        let value = match &binary.lhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value)),
            value => Some(value),
        };
        let home = HomeSlotKey::new(slot, 0);
        let input_matches = match value {
            Some(HirExpr::Call(call)) => self.facts.native_call_frame(call).is_some_and(|frame| {
                frame.home == home
                    && matches!(frame.results, Some(ResultPack::Fixed(range))
                    if range.len == 1 && range.start.index() == slot)
            }),
            Some(HirExpr::Binary(arithmetic)) if numeric_rk_arithmetic(arithmetic) => {
                arithmetic
                    .source_site
                    .and_then(|site| self.facts.operation_result_home(site))
                    == Some(home)
            }
            _ => false,
        };
        input_matches
            && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(home))
    }

    fn low_left_comparison_rhs(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
        replay_logical: bool,
    ) -> bool {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        if !matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
            return false;
        }
        let Some(lhs) = self
            .facts
            .direct_binary_operand_home(binary, 0)
            .filter(|home| home.slot() < self.base)
        else {
            return false;
        };
        let value = match &binary.rhs {
            HirExpr::LocalRef(local) => self
                .definition(*local, before)
                .and_then(|index| scalar_local(self.run[index]).map(|(_, value)| value)),
            value => Some(value),
        };
        // replay_logical 仅用于随后进入 expr 的完整帧候选；复杂条件必须逐叶核对
        // 原准备槽和事件。直接保留原表达式的查询仍只接受无需准备的纯值树。
        value.is_some_and(|value| {
            (matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
                && (replay_logical || self.pure_conditional_value(value)))
                // 低槽左值与物化的比较结果也遵守同一 operand 布局；内层 Boolean
                // 必须有自己的原写回身份，不能把外层比较的结果槽借给任意表达式。
                || (replay_logical
                    && matches!(value, HirExpr::Binary(inner)
                        if self.facts.comparison_result_temp(inner).is_some_and(|result|
                            self.facts.trusted_temp_home_slot(result) == Some(HomeSlotKey::new(
                                if self.dialect == DecompileDialect::Luau {
                                    self.boolean_operand_start(slot)
                                } else { slot }, 0)))))
                // PUC/JIT 的算术或 CONCAT 可直接占比较结果槽；低槽左值仍在原比较点读取。
                // 此处只确认 RHS 的原写入，操作数区及元方法顺序由共享帧 builder 逐层核对。
                || (replay_logical
                    && self.dialect != DecompileDialect::Luau
                    && matches!(value, HirExpr::Binary(inner)
                        if (is_scalar_binary_operation(inner.op) || inner.op == crate::hir::common::HirBinaryOpKind::Concat)
                            && inner.source_site.and_then(|source|
                                self.facts.operation_result_home(source))
                                == Some(HomeSlotKey::new(slot, 0))))
                // 单值 CALL/索引同样可直接占比较结果槽；原 use→Def 固定 RHS 版本。
                // 左侧低槽仍在 RHS 后读取，各操作 owner 核对其准备、事件和写回。
                || (replay_logical
                    && self.dialect != DecompileDialect::Luau
                    && matches!(value, HirExpr::Call(_) | HirExpr::TableAccess(_))
                    && self.facts.binary_operand_preparation(binary, 1, value)
                        .is_some_and(|(_, home)| home == HomeSlotKey::new(slot, 0)))
                // PUC/JIT 的原 NOT 也可写入随后比较的 Boolean 槽；值语境仍重发
                // 原操作，不能把它当成分支极性或按当前 Local 名称猜测输入版本。
                // 连续 NOT 可复用同一结果槽；内层输入身份及逐次写回由 expr
                // 消费 operation_input_preparation 证书，不要求最外层直接读取低槽。
                || (replay_logical
                    && self.dialect != DecompileDialect::Luau
                    && matches!(value, HirExpr::Unary(unary)
                        if unary.op == crate::hir::common::HirUnaryOpKind::Not
                            && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                            && (self.direct_home(&unary.expr).is_some_and(|home|
                                home.slot() < self.base
                                    && self.facts.unary_operand_home(unary) == Some(home))
                                || matches!(&unary.expr, HirExpr::Unary(inner)
                                    if inner.op == crate::hir::common::HirUnaryOpKind::Not
                                        && self.facts.unary_result_home(inner) == Some(HomeSlotKey::new(slot, 0))
                                        && self.facts.unary_operand_home(unary) == Some(HomeSlotKey::new(slot, 0))))))
                // Luau 有序比较仍在 Boolean 上方准备数值常量；恢复其 initializer
                // 时消费原 LOADK，避免把 scratch 声明留在后续 CALL 的低槽前缀中。
                || (self.dialect == DecompileDialect::Luau
                    && matches!(binary.op, Lt | Le | Gt | Ge)
                    && matches!(value, HirExpr::Integer(_) | HirExpr::Number(_)))
                // 低槽左值与右侧 LEN 不需要交换操作数；LEN 仍在 Boolean 上方的
                // 原 scratch 求值，保留可能的 __len 和随后比较的执行顺序。
                || (self.dialect == DecompileDialect::Luau
                    && matches!(value, HirExpr::Unary(unary)
                        if unary.op == crate::hir::common::HirUnaryOpKind::Length
                            && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot + 1, 0))
                            && self.direct_home(&unary.expr).is_some_and(|home|
                                home.slot() < self.base
                                    && self.facts.unary_operand_home(unary) == Some(home))))
        }) && self
            .facts
            .native_binary_layout(binary)
            .is_some_and(|layout| {
                layout.lhs == Some(lhs)
                    && layout.rhs
                        == Some(HomeSlotKey::new(
                            if self.dialect == DecompileDialect::Luau {
                                self.boolean_operand_start(slot)
                            } else { slot },
                            0,
                        ))
            })
    }

    /// 运算暂存结果按当前比较的原操作数顺序准备；低槽引用与内嵌常量不占槽。
    fn luau_comparison_preparations(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<[Option<(HomeSlotKey, crate::hir::common::TempId)>; 2]> {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        if self.dialect != DecompileDialect::Luau || !matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
            return None;
        }
        let layout = self.facts.native_binary_layout(binary)?;
        let mut result = [None, None];
        let mut next = slot + 1;
        for (index, (input, original)) in [&binary.lhs, &binary.rhs]
            .into_iter()
            .zip([layout.lhs, layout.rhs])
            .enumerate()
        {
            if self
                .facts
                .direct_binary_operand_home(binary, index)
                .is_some_and(|home| home.slot() < self.base && Some(home) == original)
                || (original.is_none()
                    && matches!(
                        input,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                            | HirExpr::String(_)
                    ))
            {
                continue;
            }
            let value = match input {
                HirExpr::LocalRef(local) => {
                    scalar_local(self.run[self.definition(*local, before)?])?.1
                }
                value => value,
            };
            let scalar_copy = if let HirExpr::LocalRef(local) = input {
                self.scalar_copy_source(*local, before)
            } else {
                None
            };
            let value = scalar_copy.map_or(value, |(_, index, _)| {
                scalar_local(self.run[index])
                    .expect("validated scalar CALL")
                    .1
            });
            let producer = if let HirExpr::TableAccess(access) = value {
                // 原比较 operand 的结果身份选择候选；base、key 和准备事件由
                // 随后的 luau_lookup 统一验证，不在这里重复一套较窄的读取形状。
                if self.facts.table_read_result_home(access) != Some(HomeSlotKey::new(next, 0)) {
                    return None;
                }
                let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
                    return None;
                };
                self.facts.operation_result_temp(source)?
            } else if let HirExpr::Binary(binary) = value {
                if matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
                    self.facts.comparison_result_temp(binary)?
                } else {
                    // 算术结果由原运算 Def 产生，不是 Boolean 分支合流；后续 expr
                    // 仍逐层核对输入准备及写回槽，不因结果 home 相同就跳过操作。
                    self.facts.operation_result_temp(binary.source_site?)?
                }
            } else if matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
                // 内嵌取值由 Structure 冻结为该比较的单次 phi 输入；下方仍按原
                // 连续 scratch 逐叶重放，不能从表达式外形猜一个结果槽。
                self.facts.binary_phi_operand(binary, index)?
            } else if let HirExpr::Call(call) = value {
                // 比较的 CALL 操作数也由完整帧重放；原单结果必须写入下一个
                // 比较 scratch，不把低槽调用快照搬到谓词中。
                if let Some(result) = self.expanded_call_result(call) {
                    if self.facts.binary_value_operand(binary, index) != Some(result) {
                        return None;
                    }
                    result
                } else {
                    self.facts.operation_result_temp(call.source_site?)?
                }
            } else if let HirExpr::Unary(unary) = value {
                if unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not
                {
                    let (HirExpr::Binary(comparison), _) = synthetic_not_subject(value) else {
                        return None;
                    };
                    let producer = self.facts.comparison_result_temp(comparison)?;
                    // 结构极性不另占结果槽；外层 use 必须消费这个确切的比较 phi。
                    if self.facts.binary_phi_operand(binary, index) != Some(producer) {
                        return None;
                    }
                    producer
                } else {
                    // LEN 等一元结果同样占一个比较 scratch；后续 expr 仍核对其
                    // 原输入和写回槽，不能因右侧有短路取值而丢弃左侧准备身份。
                    self.facts.operation_result_temp(unary.source_site?)?
                }
            } else if let HirExpr::GlobalRef(global) = value {
                if self.facts.global_read_frame(global, self.dialect)
                    != Some(HomeSlotKey::new(next, 0))
                {
                    return None;
                }
                self.facts
                    .binary_operand_preparation(binary, index, value)?
                    .0
            } else if matches!(value, HirExpr::UpvalueRef(_)) || tables::literal_rk(value) {
                // GETUPVAL 与 O0 的显式常量都占下一个 operand scratch。
                // 使用这次比较的 use→Def，既不重新读取旧快照，也不遗漏 LOADK/LOADNIL。
                self.facts
                    .binary_operand_preparation(binary, index, value)?
                    .0
            } else {
                return None;
            };
            let home = match value {
                HirExpr::Call(call) => self
                    .expanded_scalar_home(call)
                    .filter(|home| Some(*home) == original),
                _ => None,
            }
            .or_else(|| self.facts.trusted_temp_home_slot(producer))?;
            // 编译准备区按槽连续；循环内合流仍保留其原 value epoch，不能要求 epoch=0。
            if home.slot() != next || original != Some(home) {
                return None;
            }
            result[index] = Some((home, producer));
            next += 1;
        }
        result.iter().any(Option::is_some).then_some(result)
    }

    /// Luau 将比较结果写入预留参数槽，operand 暂存区在其上一槽；不套用 PUC 的槽距。
    fn luau_boolean_comparison(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        slot: usize,
    ) -> bool {
        use crate::hir::common::HirBinaryOpKind::{Eq, Ge, Gt, Le, Lt};
        if self.dialect != DecompileDialect::Luau || !matches!(binary.op, Eq | Lt | Le | Gt | Ge) {
            return false;
        }
        if self.low_left_comparison_rhs(binary, 0, slot, false) {
            return true;
        }
        if let (Some(lhs), Some(rhs)) = (
            self.facts.direct_binary_operand_home(binary, 0),
            self.facts.direct_binary_operand_home(binary, 1),
        ) && lhs.slot() < self.base
            && rhs.slot() < self.base
        {
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(lhs) && layout.rhs == Some(rhs));
        }
        if let Some(layout) = self.facts.native_binary_layout(binary) {
            // 一个操作数直接读取低槽，另一个字段读取占原 Boolean 结果上一槽。
            // 保持左右顺序和 GETTABLE 时点，不交换比较操作数来迁就已有形状。
            let low = |value: &HirExpr, home| {
                self.direct_home(value)
                    .is_some_and(|direct| direct.slot() < self.base && Some(direct) == home)
            };
            let field = |value: &HirExpr, home| {
                matches!(value,
                HirExpr::TableAccess(access)
                    if home == Some(HomeSlotKey::new(slot + 1, 0))
                        && self.luau_comparison_table_read(access, slot + 1))
            };
            if (field(&binary.lhs, layout.lhs) && low(&binary.rhs, layout.rhs))
                || (low(&binary.lhs, layout.lhs) && field(&binary.rhs, layout.rhs))
            {
                return true;
            }
        }
        if matches!(binary.op, Lt | Le | Gt | Ge) {
            let Some(layout) = self.facts.native_binary_layout(binary) else {
                return false;
            };
            // 有序比较的常量仍占 operand scratch；不把 Eq 的内嵌常量规则
            // 套到有序关系。Gt/Ge 的 layout 已按当前方向投影，仍核对同一低槽引用和
            // slot+1 常量准备；没有 CALL operand 或 COPY，也不改变元方法与短路位置。
            let constant = |value: &HirExpr| {
                matches!(
                    value,
                    HirExpr::Integer(_) | HirExpr::Number(_) | HirExpr::String(_)
                )
            };
            let low = |value: &HirExpr, original| {
                self.direct_home(value)
                    .is_some_and(|home| home.slot() < self.base && Some(home) == original)
            };
            let scratch = Some(HomeSlotKey::new(slot + 1, 0));
            return (constant(&binary.lhs)
                && layout.lhs == scratch
                && low(&binary.rhs, layout.rhs))
                || (low(&binary.lhs, layout.lhs)
                    && constant(&binary.rhs)
                    && layout.rhs == scratch);
        }
        if let (HirExpr::TableAccess(lhs), HirExpr::TableAccess(rhs)) = (&binary.lhs, &binary.rhs) {
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.lhs == Some(HomeSlotKey::new(slot + 1, 0))
                        && layout.rhs == Some(HomeSlotKey::new(slot + 2, 0))
                })
                && self.luau_comparison_table_read(lhs, slot + 1)
                && self.luau_comparison_table_read(rhs, slot + 2);
        }
        if !matches!(
            binary.rhs,
            HirExpr::Nil
                | HirExpr::Boolean(_)
                | HirExpr::Integer(_)
                | HirExpr::Number(_)
                | HirExpr::String(_)
        ) {
            return false;
        }
        match &binary.lhs {
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_) | HirExpr::TempRef(_) => self
                .facts
                .direct_binary_operand_home(binary, 0)
                .is_some_and(|home| home.slot() < self.base),
            HirExpr::UpvalueRef(_) => self
                .facts
                .comparison_read_preparation(binary, &binary.lhs)
                .is_some_and(|(_, home)| home == HomeSlotKey::new(slot + 1, 0)),
            HirExpr::GlobalRef(global) => {
                let home = HomeSlotKey::new(slot + 1, 0);
                self.facts.global_read_frame(global, self.dialect) == Some(home)
                    && self
                        .facts
                        .native_binary_layout(binary)
                        .is_some_and(|layout| layout.lhs == Some(home) && layout.rhs.is_none())
            }
            HirExpr::TableAccess(access) => self.luau_comparison_table_read(access, slot + 1),
            HirExpr::Unary(unary) => {
                unary.op == crate::hir::common::HirUnaryOpKind::Length
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot + 1, 0))
                    && self
                        .direct_home(&unary.expr)
                        .is_some_and(|home| home.slot() < self.base)
            }
            _ => false,
        }
    }

    /// 比较的表操作数仍在原 scratch 读取；base 的准备证书绑定原 use→Def，
    /// 嵌套查表逐层核对读取布局，不按表达式形状猜测准备槽。
    fn luau_comparison_table_read(
        &self,
        access: &crate::hir::common::HirTableAccess,
        slot: usize,
    ) -> bool {
        let Some(layout) = self.facts.native_table_read_layout(access) else {
            return false;
        };
        if self.facts.table_read_result_home(access) != Some(HomeSlotKey::new(slot, 0))
            || access
                .sources
                .try_for_each_known(|source| {
                    self.facts
                        .operation_result_reference_unaliased(source)
                        .then_some(())
                })
                .is_none()
        {
            return false;
        }
        if let Some(key) = layout.key {
            if self.direct_home(&access.key) == Some(key)
                && key.slot() < self.base
                && layout.base == HomeSlotKey::new(slot + 1, 0)
                && matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                    if self.facts.operation_input_preparation(source, &access.base)
                        .is_some_and(|(_, home)| home == layout.base))
                && match &access.base {
                    HirExpr::UpvalueRef(_) => true,
                    HirExpr::TableAccess(base) => {
                        self.luau_comparison_table_read(base, layout.base.slot())
                    }
                    _ => false,
                }
            {
                // 动态低槽键不占准备区；base 在查表结果上方准备。
                // 原 GETTABLE 输入 Def 绑定同一次上值或内层读取，不能重读旧快照。
                return true;
            }
            // 低槽键直接读取；上值和 O0 的字面键在结果上方准备。
            // 原 use→Def 同时约束值、身份和槽位，不能把先前 COPY 当成本次准备。
            return self.facts.table_read_base_home(access) == Some(layout.base)
                && layout.base.slot() < self.base
                && ((self.direct_home(&access.key) == Some(key) && key.slot() < self.base)
                    || (matches!(access.key, HirExpr::UpvalueRef(_))
                        || tables::literal_rk(&access.key))
                        && key == HomeSlotKey::new(slot + 1, 0)
                        && self.facts.table_key_preparation(access) == Some(key));
        }
        if !matches!(access.key, HirExpr::String(_) | HirExpr::Integer(1..=256)) {
            return false;
        }
        if self.facts.table_read_base_home(access) == Some(layout.base)
            && layout.base.slot() < self.base
        {
            return true;
        }
        if let HirExpr::GlobalRef(global) = &access.base {
            // GETIMPORT 展开的环境和字段读取共用原结果槽；保留读取顺序，
            // 不把其它槽上的全局快照当成可重新求值的 base。
            return layout.base == HomeSlotKey::new(slot, 0)
                && self.facts.global_read_frame(global, self.dialect) == Some(layout.base)
                && matches!(&access.key, HirExpr::String(key)
                    if key.as_utf8().is_some_and(|key| self.dialect.is_identifier_name(key)));
        }
        if !matches!(access.base, HirExpr::UpvalueRef(_)) {
            return false;
        }
        let base_slot = match &access.key {
            HirExpr::String(key)
                if key
                    .as_utf8()
                    .is_some_and(|key| self.dialect.is_identifier_name(key)) =>
            {
                slot
            }
            HirExpr::Integer(1..=256) => slot + 1,
            _ => return false,
        };
        let crate::hir::common::HirOperationSources::Single(source) = access.sources else {
            return false;
        };
        layout.base == HomeSlotKey::new(base_slot, 0)
            && self
                .facts
                .operation_input_preparation(source, &access.base)
                .is_some_and(|(_, home)| home == layout.base)
    }

    fn pure_conditional_value(&self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.pure_conditional_value(&logical.lhs)
                    && self.pure_conditional_value(&logical.rhs)
            }
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => self
                .direct_home(expr)
                .is_some_and(|home| home.slot() < self.base),
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::UpvalueRef(_) => true,
            _ => false,
        }
    }

    /// 保留比较/CALL 值树的原分组，每个短路右臂都禁止消费无条件 producer。
    /// 子逻辑节点直接递归，不再逐层重扫 pure_conditional_value，长比较链仍只访问各节点一次。
    fn comparison_tree(
        &mut self,
        expr: &HirExpr,
        before: usize,
        slot: usize,
        argument_home: bool,
    ) -> Option<HirExpr> {
        match expr {
            HirExpr::UpvalueRef(upvalue) => {
                let condition = self.boolean_condition.as_mut()?;
                let home = self
                    .facts
                    .boolean_condition_upvalue(condition.result, *upvalue)?;
                if home.slot() != slot || !condition.reads.insert(*upvalue) {
                    return None;
                }
                Some(expr.clone())
            }
            HirExpr::GlobalRef(global)
                if self.facts.global_read_frame(global, self.dialect)
                    == Some(HomeSlotKey::new(slot, 0)) =>
            {
                // 全局值本身参与短路时也写入共同结果槽；保留原读取位置，
                // 不将它当作仅提供分支极性的比较，亦不吸收右臂之外的 producer。
                Some(expr.clone())
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => Some(expr.clone()),
            HirExpr::Unary(unary)
                if unary.op == crate::hir::common::HirUnaryOpKind::Neg
                    || unary.op == crate::hir::common::HirUnaryOpKind::Not
                        && unary.source_site.is_some() =>
            {
                // 原生 NOT 是短路值叶的实际写回；expr 核对结果 home 与输入准备，
                // 不能走下方仅处理结构极性的 synthetic NOT 分支。
                self.expr(expr, before, slot, None, false, false, None)
            }
            HirExpr::TableAccess(access) if self.dialect == DecompileDialect::Luau => {
                // 字段值本身参与短路，仍在原结果槽读取；右臂沿共同事件游标检查。
                self.luau_lookup(access, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.dialect == DecompileDialect::Luajit
                    && let Some(home) = self.boolean_frame.filter(|home| home.slot() == slot)
                    && self.jit_direct_lookup(access, home) =>
            {
                // 末项保留任意字段值，原 TGET 与前面的谓词共用结果槽。
                Some(expr.clone())
            }
            HirExpr::TableAccess(access)
                if !matches!(
                    self.dialect,
                    DecompileDialect::Luajit | DecompileDialect::Luau
                ) =>
            {
                // 短路末项可以是任意字段值；原 GETTABLE 必须在同一结果槽，
                // 右臂的事件游标检查仍禁止吸收无条件执行的准备语句。
                self.register_lookup(access, before, slot)
            }
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_)
                if self
                    .direct_home(expr)
                    .is_some_and(|home| home.slot() < self.base) =>
            {
                // 原低槽作为短路测试不准备新值；右臂比较仍按原 Boolean 槽重发。
                Some(expr.clone())
            }
            HirExpr::LocalRef(_) => {
                // 逻辑结果 local 可能先 COPY 左值，再原槽短路写回；按 before 读取
                // 前一个值版本，仍由 expr 核对 home 和事件。完整参数语境继续持有
                // 该槽，不能在递归时遗失已证明的根交接；右臂仍不能消费准备区。
                self.expr(expr, before, slot, None, false, argument_home, None)
            }
            HirExpr::TempRef(temp) if self.native.is_some() => {
                // 尚未提升的短路左值直接携带原 Def，复用相同的 home 与准备事件证明；
                // 右臂仍由下方游标检查禁止吸收无条件执行的定义。
                self.expr(expr, before, slot, None, false, argument_home, Some(*temp))
            }
            HirExpr::Binary(_) | HirExpr::Call(_) => {
                // 比较叶同样在参数结果槽写 Boolean；保持正向与反向谓词的值语境一致。
                self.expr(expr, before, slot, None, false, argument_home, None)
            }
            HirExpr::Unary(unary)
                if unary.source_site.is_none()
                    && unary.op == crate::hir::common::HirUnaryOpKind::Not =>
            {
                // 结构恢复的极性包装不对应独立写槽；内部 CALL/比较仍须通过
                // 同一短路帧和事件边界证明，原生 NOT 不走这条路径。
                let value = self.comparison_tree(&unary.expr, before, slot, argument_home)?;
                Some(HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                    expr: value,
                    ..unary.as_ref().clone()
                })))
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let lhs = self.comparison_tree(&logical.lhs, before, slot, argument_home)?;
                let checkpoint = (self.first_event, self.next_event);
                let rhs = self.comparison_tree(&logical.rhs, before, slot, argument_home)?;
                // 候选拒绝[SemanticBarrier:EvalOrder]：右臂不能吸收原本无条件执行的 CALL 等事件。
                if checkpoint != (self.first_event, self.next_event) {
                    return None;
                }
                let rebuilt = Box::new(crate::hir::common::HirLogicalExpr {
                    preserves_boolean_prewrite: logical.preserves_boolean_prewrite,
                    lhs,
                    rhs,
                });
                Some(if matches!(expr, HirExpr::LogicalAnd(_)) {
                    HirExpr::LogicalAnd(rebuilt)
                } else {
                    HirExpr::LogicalOr(rebuilt)
                })
            }
            _ => None,
        }
    }

    fn constructor_field_is_preserved(&self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_) => true,
            HirExpr::Closure(closure) => {
                // 这里只证明捕获身份位于整个准备区以下，不合并或退休 cell。
                // 循环绑定可跨同槽的多个 CLOSE epoch；完整来源都在低槽即可，
                // 不要求唯一 home。未知或 home-free 来源仍不能签发帧布局证明。
                closure
                    .captures
                    .iter()
                    .all(|capture| match capture.binding {
                        crate::hir::common::HirBinding::Local(local) => self
                            .facts
                            .possible_local_home_slots(local)
                            .is_some_and(|homes| {
                                !homes.is_empty()
                                    && homes.iter().all(|home| home.slot() < self.base)
                            }),
                        crate::hir::common::HirBinding::Param(param) => self
                            .facts
                            .possible_param_home_slots(param)
                            .is_some_and(|homes| {
                                !homes.is_empty()
                                    && homes.iter().all(|home| home.slot() < self.base)
                            }),
                        crate::hir::common::HirBinding::Upvalue(_) => true,
                        crate::hir::common::HirBinding::Temp(_) => false,
                    })
            }
            _ => false,
        }
    }

    /// Luau 可在参数之后执行 receiver COPY 和方法查找；只分阶段核对该原协议，
    /// receiver 表达式仍先消费，参数完成后再按连续事件提交准备写。
    fn late_method_setup(&self, call: &HirCallExpr, before: usize) -> Option<[Option<usize>; 2]> {
        if self.dialect != DecompileDialect::Luau || call.method != HirMethodCall::Explicit {
            return None;
        }
        let (access, lookup) = match &call.callee {
            HirExpr::LocalRef(callee) => {
                let index = self.definition(*callee, before)?;
                let (_, HirExpr::TableAccess(access)) = scalar_local(self.run[index])? else {
                    return None;
                };
                (access.as_ref(), Some(index))
            }
            HirExpr::TableAccess(access) => (access.as_ref(), None),
            _ => return None,
        };
        let HirExpr::LocalRef(receiver) = access.base else {
            return None;
        };
        let copy = self.definition(receiver, lookup.unwrap_or(before))?;
        let (_, value) = scalar_local(self.run[copy])?;
        let original = self.facts.call_argument_value(call, 0)?;
        if self.facts.promoted_local_for_temp(original) != Some(receiver)
            || !match value {
                HirExpr::LocalRef(source) => {
                    self.facts.call_argument_copy(call, 0).is_some_and(|copy| {
                        self.facts.promoted_local_for_temp(copy.source) == Some(*source)
                    })
                }
                HirExpr::ParamRef(source) => {
                    self.facts.readonly_parameter_copy(original) == Some(*source)
                }
                _ => false,
            }
            || !(call.args.tail.is_some()
                || call.args.fixed.iter().skip(1).any(|arg| {
                    matches!(arg,
                    HirExpr::LocalRef(local) if self.definition(*local, before)
                        .is_some_and(|index| index < copy && index >= self.next_event))
                }))
        {
            return None;
        }
        Some([Some(copy), lookup])
    }

    fn method_callee(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        args_start: usize,
    ) -> Option<HirExpr> {
        let HirCallRootHandoff::MethodCallee(protocol_id) = call.callee_root_handoff?;
        let protocol = self.facts.method_setup_protocol(protocol_id)?;
        let callee_home = self.facts.trusted_temp_home_slot(protocol.callee_temp)?;
        let receiver_home = self
            .facts
            .trusted_temp_home_slot(self.facts.call_argument_value(call, 0)?)?;
        if receiver_home.slot() != args_start {
            return None;
        }
        if call.method != HirMethodCall::Explicit
            || call.fastcall.is_some()
            || callee_home.slot() != slot
            || !protocol
                .method_key
                .as_utf8()
                .is_some_and(|key| self.dialect.is_identifier_name(key))
            || !(call.argument_roots.iter().any(|root| {
                root.argument == 0
                    && self.facts.trusted_temp_home_slot(root.producer) == Some(receiver_home)
            }) || (self.facts.native_call_frame(call).is_some_and(|frame| frame.arguments_unaliased)
                // 参数中的分支与 TAILCALL 可能没有独立的根交接许可，但唯一 SELF
                // 协议及原 receiver Def/槽仍存在。这里只在完整帧中重发该 COPY，
                // 不向局部内联消费者签发可删除参数根的许可。
                && self.facts.call_argument_value(call, 0).is_some_and(|producer| {
                    self.facts.trusted_temp_home_slot(producer)
                        == Some(receiver_home)
                        && matches!(call.args.first(), Some(HirExpr::LocalRef(local))
                            if self.facts.promoted_local_for_temp(producer) == Some(*local))
                })))
        {
            return None;
        }
        let (access, lookup_index) = match &call.callee {
            HirExpr::TableAccess(access) => (access.as_ref(), None),
            HirExpr::LocalRef(local) => {
                let index = self.definition(*local, before)?;
                if index < self.next_event
                    || !(self.facts.trusted_local_home_slot(*local) == Some(callee_home)
                        || self.facts.promoted_local_for_temp(protocol.callee_temp) == Some(*local))
                {
                    return None;
                }
                let HirExpr::TableAccess(access) = scalar_local(self.run[index])?.1 else {
                    return None;
                };
                (access.as_ref(), Some(index))
            }
            _ => return None,
        };
        if super::method_protocol::match_method_setup_pair(access, &call.callee, call)?
            != protocol_id
        {
            return None;
        }
        let lookup_before = lookup_index.unwrap_or(before);
        if let HirExpr::LocalRef(receiver) = access.base
            && self.definition(receiver, lookup_before) != self.definition(receiver, before)
        {
            return None;
        }
        let mut access = access.clone();
        // SELF 的 receiver 副本槽由原 CALL 参数布局给出；LuaJIT frame gap
        // 不同于 PUC 的相邻槽，不能从最终冒号语法反推（common_09）。
        // 方法链的 receiver 可以由前一个 CALL 加 SELF 副本组成；此时核对
        // producer CALL 的完整写域。独立 receiver COPY 则核对当前参数 Def，
        // 不把同一 Local 后续值版本的写入混入当前准备。
        let receiver_producer = match &access.base {
            HirExpr::LocalRef(local) => self
                .definition(*local, lookup_before)
                .and_then(|index| scalar_local(self.run[index]))
                .and_then(|(_, value)| match value {
                    HirExpr::Call(producer) => producer
                        .source_site
                        .and_then(|site| self.facts.operation_result_temp(site)),
                    _ => None,
                }),
            _ => None,
        }
        .or_else(|| {
            protocol.receiver_temp.filter(|temp| match access.base {
                HirExpr::LocalRef(local) => {
                    self.facts.promoted_local_for_temp(*temp) == Some(local)
                }
                HirExpr::TempRef(receiver) => receiver == *temp,
                _ => false,
            })
        })
        .or_else(|| self.facts.call_argument_value(call, 0));
        access.base = self.expr(
            &access.base,
            lookup_before,
            slot,
            Some(receiver_home),
            true,
            false,
            receiver_producer,
        )?;
        let callee = HirExpr::TableAccess(Box::new(access));
        if let Some(index) = lookup_index {
            self.finish_event(index)?;
        }
        self.methods += 1;
        Some(callee)
    }
    /// 开放 VARARG 必须重发到原消费帧的尾槽；不能用省略号代替 CALL 或合流包。
    fn open_tail(
        &mut self,
        tail: &HirPackTail,
        vararg_home: Option<HomeSlotKey>,
        before: usize,
        slot: usize,
    ) -> Option<HirPackTail> {
        if tail.exact_width().is_some() {
            return None;
        }
        match tail.as_expr() {
            HirExpr::VarArg if vararg_home.map(HomeSlotKey::slot) == Some(slot) => {
                Some(tail.clone())
            }
            HirExpr::Call(call) => Some(HirPackTail::open(HirExpr::Call(Box::new(self.call(
                call,
                before,
                slot,
                false,
                CallWidth::Open,
            )?)))),
            _ => None,
        }
    }

    fn call(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        outer: bool,
        width: CallWidth,
    ) -> Option<HirCallExpr> {
        if call.fastcall.is_some() {
            if call.args.tail.as_ref().is_some_and(|tail| {
                matches!(tail.as_expr(), HirExpr::Call(_))
                    || matches!(tail.as_expr(), HirExpr::VarArg)
                        && matches!(
                            call.fastcall,
                            Some(crate::transformer::FastCallProtocol::All { .. })
                        )
            }) {
                return self.fastcall_open(call, before, slot, width);
            }
            return self.fastcall_fixed(call, before, slot, width);
        }
        let mut method = call.method;
        let mut transaction = call.method_rewrite_transaction;
        let native_frame = if self.native.is_some() {
            Some(self.facts.native_call_frame(call)?)
        } else {
            None
        };
        let args_start = if let Some(frame) = native_frame {
            if frame.home.slot() != slot
                || !match (width, frame.results) {
                    (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
                    (CallWidth::Single, Some(ResultPack::Fixed(range))) => {
                        range.start.index() == slot && range.len == 1
                    }
                    (CallWidth::Fixed(width), Some(ResultPack::Fixed(range))) => {
                        range.start.index() == slot && range.len == width
                    }
                    (CallWidth::Open, Some(ResultPack::Open(start))) => start.index() == slot,
                    (CallWidth::Tail, None) => true,
                    _ => false,
                }
            {
                return None;
            }
            let args_start = match frame.args {
                ValuePack::Fixed(range)
                    if call.args.tail.is_none() && range.len == call.args.fixed.len() =>
                {
                    range.start.index()
                }
                ValuePack::Open(start)
                    if call
                        .args
                        .tail
                        .as_ref()
                        .is_some_and(|tail| tail.exact_width().is_none()) =>
                {
                    start.index()
                }
                _ => return None,
            };
            if args_start <= slot {
                return None;
            }
            if let HirExpr::LocalRef(local) = call.callee
                && self.definition(local, before).is_some()
                && self
                    .facts
                    .trusted_local_home_slot(local)
                    .is_none_or(|home| home.slot() >= self.base)
                && self.facts.promoted_local_for_temp(frame.callee) != Some(local)
            {
                return None;
            }
            args_start
        } else {
            slot + 1
        };
        let expanded_method_argument =
            if call.is_method() && call.args.fixed.len() == 2 && call.args.tail.is_none() {
                self.expanded_captured_argument(call, 1, before, args_start + 1)
            } else {
                None
            };
        let delayed_method = expanded_method_argument.is_some();
        let late_setup = (!delayed_method)
            .then(|| self.late_method_setup(call, before))
            .flatten();
        if let Some(events) = late_setup {
            self.deferred_method_events
                .extend(events.into_iter().flatten());
        }
        let first_arg = usize::from(call.is_method());
        let callee = if call.is_method() {
            method = HirMethodCall::Implicit;
            transaction = None;
            if delayed_method {
                None
            } else {
                Some(self.method_callee(call, before, slot, args_start)?)
            }
        } else if native_frame.is_some() || outer {
            Some(self.expr(
                &call.callee,
                before,
                slot,
                None,
                true,
                false,
                native_frame.map(|frame| frame.callee),
            )?)
        } else {
            return None;
        };
        let argument_roots = if self.native.is_some() {
            call.argument_roots
                .iter()
                .map(|root| (root.argument, root.producer))
                .collect::<BTreeMap<_, _>>()
        } else {
            BTreeMap::new()
        };
        let mut boolean_prewrite_arguments = call.boolean_prewrite_arguments.clone();
        let fixed = call
            .args
            .fixed
            .iter()
            .enumerate()
            .skip(first_arg)
            .map(|(index, arg)| {
                if !call.is_method()
                    && let Some(restored) = self.expanded_published_table_argument(call, index, before, args_start + index)
                {
                    return Some(restored);
                }
                if let Some(restored) = expanded_method_argument.as_ref().filter(|_| index == 1) {
                    return Some(restored.clone());
                }
                if !call.is_method()
                    && let Some(restored) = self.expanded_captured_sum_argument(call, index, before, args_start + index)
                {
                    return Some(restored);
                }
                if !call.is_method()
                    && let Some(restored) = self.expanded_captured_argument(call, index, before, args_start + index)
                {
                    return Some(restored);
                }
                let prewrite = (self.native.is_some() && self.dialect == DecompileDialect::Luau)
                    .then(|| self.facts.boolean_argument_prewrite(call, index))
                    .flatten();
                if let Some(prewrite) = prewrite {
                    self.consume_boolean_argument_prewrite(
                        call,
                        index,
                        arg,
                        before,
                        args_start + index,
                    )?;
                    let value = match arg {
                        HirExpr::LocalRef(local) => self
                            .definition(*local, before)
                            .and_then(|index| scalar_local(self.run[index]))
                            .map_or(arg, |(_, value)| value),
                        value => value,
                    };
                    // 普通 CALL 与 FASTCALL 共用原 Boolean 预写；合取/析取自身
                    // 已重发该写，裸比较才需要在 AST 投影时补回对应的 Boolean 外壳。
                    if !matches!(value, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)) {
                        boolean_prewrite_arguments.push((index, prewrite.initial_value));
                    }
                }
                // 原参数 Def 的交接证明同样在本次 CALL 时点排除了打开的 capture；
                // 后续其它 binding 复用该槽不能反向阻止这一原子帧事务。
                // 槽距约束不要求 epoch 为零；身份仍绑定原参数 Def 与当前 Local。
                let argument_home = prewrite.is_some()
                    || argument_roots.get(&index).is_some_and(|&producer| {
                        self.facts
                            .trusted_temp_home_slot(producer)
                            .is_some_and(|home| home.slot() == args_start + index)
                            && matches!(arg, HirExpr::LocalRef(local)
                            if self.facts.promoted_local_for_temp(producer) == Some(*local))
                    })
                    || native_frame.is_some_and(|frame| frame.arguments_unaliased)
                        && match arg {
                            HirExpr::TempRef(temp) => {
                                self.facts.call_argument_value(call, index) == Some(*temp)
                                    && self
                                        .facts
                                        .trusted_temp_home_slot(*temp)
                                        .is_some_and(|home| home.slot() == args_start + index)
                            }
                            HirExpr::LocalRef(local) => self
                                .facts
                                .call_argument_value(call, index)
                                .is_some_and(|producer| {
                                    self.facts.promoted_local_for_temp(producer) == Some(*local)
                                        && self
                                            .facts
                                            .trusted_temp_home_slot(producer)
                                            .is_some_and(|home| home.slot() == args_start + index)
                                }),
                            // 已处于参数表达式中的表没有待删除的 binding；完整 CALL 恢复
                            // 原参数槽时仍在此语境求值，不能要求不存在的 Local 身份。
                            HirExpr::TableConstructor(_) | HirExpr::Closure(_) => true,
                            HirExpr::Decision(_) => self
                                .facts
                                .call_argument_value(call, index)
                                .and_then(|producer| self.facts.trusted_temp_home_slot(producer))
                                .is_some_and(|home| home.slot() == args_start + index),
                            HirExpr::Call(nested) if nested.required_luau_inlining.is_some() => {
                                self.expanded_call_result(nested).is_some_and(|result| {
                                    self.facts.call_argument_value(call, index) == Some(result)
                                        && self.facts.trusted_temp_home_slot(result)
                                            .is_some_and(|home| home.slot() == args_start + index)
                                })
                            }
                            HirExpr::TableAccess(access) => {
                                matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                                    if self.facts.call_argument_value(call, index).is_some_and(|producer|
                                        self.facts.operation_result_temp(source) == Some(producer)))
                                    && self.facts.table_read_result_home(access)
                                        == Some(HomeSlotKey::new(args_start + index, 0))
                            }
                            HirExpr::LogicalOr(logical)
                                if self.dialect == DecompileDialect::Luau
                                    && matches!(logical.rhs, HirExpr::TableConstructor(_)) =>
                            {
                                true
                            }
                            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
                                if self.dialect == DecompileDialect::Luau =>
                            {
                                // 已嵌入参数的短路树仍消费原 CALL 的 phi 结果槽；Local
                                // 外壳消失不改变参数角色。值树 builder 继续逐叶核对原操作。
                                self.facts.call_argument_value(call, index).is_some_and(|result| {
                                    self.facts.is_phi_carrier_temp(result)
                                        && self.facts.trusted_temp_home_slot(result)
                                            == Some(HomeSlotKey::new(args_start + index, 0))
                                })
                            }
                            HirExpr::Binary(binary) => {
                                self.facts
                                    .comparison_result_temp(binary)
                                    // 已内联的算术也保留原结果 Def；参数角色不能因
                                    // LocalRef 已消失而丢失，否则下一轮只能展开 callee。
                                    .or_else(|| binary.source_site.and_then(|site| self.facts.operation_result_temp(site)))
                                    .is_some_and(|temp| {
                                        self.facts.call_argument_value(call, index) == Some(temp)
                                            && self.facts.trusted_temp_home_slot(temp)
                                                == Some(HomeSlotKey::new(args_start + index, 0))
                                    })
                            }
                            _ => false,
                        };
                self.consume_argument_root_release(call, index, arg, before, args_start + index)?;
                let previous_top = self.declaration_reserved_top;
                if self.dialect == DecompileDialect::Luau
                    && call.args.tail.is_none()
                    && index + 1 == call.args.fixed.len()
                    && let CallWidth::Fixed(results) = width
                {
                    // 普通参数用 TempTop 临时收缩准备区，末参数则保留完整 CALL 区；
                    // 多结果宽度超过参数区时，末参数内部的临时槽仍从预留结果之后开始。
                    self.declaration_reserved_top = Some(slot + results.max(1 + call.args.fixed.len()));
                }
                let previous_parameter_copy = std::mem::replace(
                    &mut self.parameter_copy, self.facts.call_parameter_copy(call, index));
                let result = self.expr(
                    arg,
                    before,
                    args_start + index,
                    None,
                    false,
                    argument_home,
                    self.facts
                        .call_argument_value(call, index)
                        .or_else(|| argument_roots.get(&index).copied())
                        .filter(|producer| match arg {
                            // 尚未提升的参数保留原 Def；传递同一身份给已有 Temp 帧证明，
                            // 不能在这里丢掉来源后再让前缀 owner 猜测临时值的槽。
                            HirExpr::TempRef(temp) => temp == producer,
                            HirExpr::LocalRef(local) => {
                                self.facts.promoted_local_for_temp(*producer) == Some(*local)
                            }
                            HirExpr::Closure(closure) => {
                                closure
                                    .source_site
                                    .and_then(|source| self.facts.operation_result_temp(source))
                                    == Some(*producer)
                            }
                            // 已树化的展开调用沿用外层 CALL 的原参数 Def；完整帧
                            // 仍验证 COPY、求值顺序与返回槽，不从 nil 字面量重猜身份。
                            HirExpr::Call(nested) if nested.required_luau_inlining.is_some() => {
                                self.expanded_call_result(nested) == Some(*producer)
                            }
                            // cdata 已树化仍是本次 CALL 的原单次准备；按 use→Def
                            // 核对字面量及 home，不能当作可复制的普通数字常量。
                            HirExpr::Int64(_) | HirExpr::UInt64(_) | HirExpr::Complex { .. } => {
                                self.facts.call_argument_preparation(call, index, arg)
                                    .is_some_and(|home| self.facts.trusted_temp_home_slot(*producer) == Some(home))
                            }
                            HirExpr::Binary(_) | HirExpr::Integer(_) | HirExpr::Number(_) => {
                                self.has_constant_control(*producer)
                            }
                            _ => false,
                        }),
                );
                self.declaration_reserved_top = previous_top;
                self.parameter_copy = previous_parameter_copy;
                result
            })
            .collect::<Option<Vec<_>>>()?;
        let tail = match &call.args.tail {
            Some(tail) if matches!(tail.as_expr(), HirExpr::VarArg) => {
                if tail.exact_width().is_some()
                    || self.native.is_none()
                    || !matches!(
                        self.dialect,
                        DecompileDialect::Lua51
                            | DecompileDialect::Lua52
                            | DecompileDialect::Lua53
                            | DecompileDialect::Lua54
                            | DecompileDialect::Lua55
                            | DecompileDialect::Luajit
                            | DecompileDialect::Luau
                    )
                    || self
                        .facts
                        .call_vararg_tail_home(call)
                        .map(HomeSlotKey::slot)
                        != Some(args_start + call.args.fixed.len())
                    || !native_frame.is_some_and(|frame| frame.arguments_unaliased)
                {
                    return None;
                }
                // 普通 Luau CALL 也先完成 callee 与固定前缀，再把 VARARG 写到原尾槽。
                // FASTCALL 的延后 lookup 仍由 fastcall_open 独立处理，不交换两个协议的事件。
                Some(tail.clone())
            }
            Some(tail) => {
                let HirExpr::Call(nested) = tail.as_expr() else {
                    return None;
                };
                let call = self.call(
                    nested,
                    before,
                    args_start + call.args.fixed.len(),
                    false,
                    CallWidth::Open,
                )?;
                Some(match tail.exact_width() {
                    Some(width) => HirPackTail::exact(HirExpr::Call(Box::new(call)), width),
                    None => HirPackTail::open(HirExpr::Call(Box::new(call))),
                })
            }
            None => None,
        };
        // receiver 表达式先于参数执行；Luau 的延后 COPY/NAMECALL 单独提交，
        // 开放尾调用也不能让整个 receiver 求值一起移到参数之后。
        let callee = match callee {
            Some(callee) => callee,
            None => self.method_callee(call, before, slot, args_start)?,
        };
        if let Some(events) = late_setup {
            for index in events.into_iter().flatten() {
                self.deferred_method_events.remove(&index);
                self.finish_event(index)?;
            }
        }
        self.finish_dispatch(call, before)?;
        Some(HirCallExpr {
            required_luau_inlining: call.required_luau_inlining,
            source_site: call.source_site,
            argument_roots: Vec::new(),
            frame_root_ends: Vec::new(),
            callee,
            args: HirValuePack { fixed, tail },
            method,
            fastcall: call.fastcall,
            method_key: call.method_key.clone(),
            callee_root_handoff: call.callee_root_handoff,
            method_rewrite_transaction: transaction,
            interpolation: call.interpolation.clone(),
            plain_method_syntax: false,
            boolean_prewrite_arguments,
        })
    }
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
