//! 在 HIR 收尾把完整原调用帧恢复为表达式，统一普通调用和终端方法链的槽/事件核对。
//!
//! Promotion 以原 HirSourceSite 发布 callee Def、参数起点和固定/开放结果包；方法另消费
//! 原 SELF 双端协议。共享 FrameBuilder 逐定义版本、逐 home、逐事件树化，不从 AST
//! 反推寄存器，也不把零返回假定为旧 callee 必然覆写。普通非终端调用还必须核对
//! 整个源码低槽声明前缀，并通过 PhysicalFramePrefix 保留已有身份及其声明起点。普通帧由
//! Deferred 调度处理，声明 epoch 改变后交还构造器 owner；缺少完整前缀证明的方法帧
//! 仍由最终终端事务独立处理。
//! 例如 `p=print; c=table.concat; p("x",c(t))` 原子恢复成原生嵌套调用，可避免
//! 多出的低槽 local 抬高后续 GC 的 caller top；`print(obj:make():next())` 则由
//! 同一 builder 消费原方法 receiver/参数槽，终端边界维持其既有独立合同。
//! CONCAT 输入按各自原值版本核对写域；同一 Local 承接拼接结果后附带的低槽 MOVE，
//! 仍属于输出责任，不应使原输入 COPY 被永久物化并在每轮重编译中增长。

mod fastcalls;
mod logical;
mod lookups;
mod native;
mod parameter_returns;
mod tables;

pub(super) use native::prepare_source_frames;
pub(super) use native::preserve_existing_call_prefixes;
pub(super) use native::restore_expanded_frames;
pub(super) use native::restore_tbc_initializer_frames;
pub(super) use parameter_returns::restore as restore_parameter_return_frames;
pub(super) use tables::constants_fit_rk;

use crate::transformer::{ResultPack, ValuePack};
use std::collections::{BTreeMap, BTreeSet};

use super::mention::{CaptureCollector, ProtectedLocalCollector, ToBeClosedHomeCollector};
use super::source_frames as prefix;
use crate::decompile::DecompileDialect;
use crate::hir::common::{
    HirBlock, HirCallExpr, HirCallRootHandoff, HirCaptureMode, HirExpr, HirLValue, HirMethodCall,
    HirPackTail, HirProto, HirStmt, HirTableAllocation, HirTableField, HirValuePack, LocalId,
};
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};

struct FrameRestrictions {
    barred: BTreeSet<HomeSlotKey>,
    closed: BTreeSet<HomeSlotKey>,
    protected: BTreeSet<LocalId>,
}

fn numeric_rk_arithmetic(binary: &crate::hir::common::HirBinaryExpr) -> bool {
    use crate::hir::common::HirBinaryOpKind;
    matches!(
        binary.op,
        HirBinaryOpKind::Add
            | HirBinaryOpKind::Sub
            | HirBinaryOpKind::Mul
            | HirBinaryOpKind::Div
            | HirBinaryOpKind::Mod
            | HirBinaryOpKind::Pow
    ) && matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
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
        barred,
        closed: closed.homes,
        protected: protected.locals,
    }
}

pub(super) fn restore_native_call_frames(
    module: &mut crate::hir::HirModule,
    promotion: &[ProtoPromotionFacts],
    values: &super::object_flow::ReturnValueFacts,
    dialect: DecompileDialect,
) -> bool {
    // 所有候选先消费同一模块快照，再统一提交；子函数 body 改写后，后一个 proto
    // 不能继续把旧返回值摘要当成新快照。只保存有 local 的 proto，候选不借用旧 HIR。
    let mut prepared = Vec::new();
    let terminal = native::terminal_closure_facts(module, promotion, values, dialect);
    for proto in &module.protos {
        if proto.local_count == 0 {
            continue;
        }
        let Some(facts) = promotion.get(proto.id.index()) else {
            continue;
        };
        let constraints = frame_restrictions(proto, facts);
        prepared.push((
            proto.id,
            native::prepare(
                proto,
                facts,
                dialect,
                &constraints.barred,
                &constraints.closed,
                &terminal,
            ),
        ));
    }
    let mut changed = false;
    for (id, plans) in prepared {
        changed |= plans.commit(
            &mut module.protos[id.index()],
            &promotion[id.index()],
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
        constructor_depth: 0,
        constructor_reserved_top: None,
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
        boolean_frame: None,
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
    constructor_depth: usize,
    // Luau 多目标声明先预留全部结果槽，record scratch 从整组目标末端开始。
    constructor_reserved_top: Option<usize>,
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
    boolean_frame: Option<usize>,
}

#[derive(Clone, Copy)]
struct NativeFrameContext<'a> {
    proto: &'a HirProto,
    barred: &'a BTreeSet<HomeSlotKey>,
    closed: &'a BTreeSet<HomeSlotKey>,
    constants_fit_rk: bool,
}

#[derive(Clone, Copy)]
enum CallWidth {
    Ignore,
    Single,
    Fixed(usize),
    Open,
    Tail,
}

impl FrameBuilder<'_> {
    fn finish_event(&mut self, index: usize) -> Option<()> {
        if self.first_event.is_none() {
            self.first_event = Some(index);
            self.next_event = index;
        }
        if index != self.next_event {
            return None;
        }
        self.next_event += 1;
        Some(())
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

    fn homes_match(
        &self,
        local: LocalId,
        definition: usize,
        slot: usize,
        receiver: Option<usize>,
        original_producer: Option<crate::hir::common::TempId>,
    ) -> bool {
        let producer = original_producer.or_else(|| {
            let (_, HirExpr::Call(call)) = scalar_local(self.run[definition])? else {
                return None;
            };
            self.facts.operation_result_temp(call.source_site?)
        });
        // 编译位置只比较 slot；写入集合仍匹配该原值版本的完整 home，包括 epoch。
        // CALL+COPY 可能由低槽 local 承接，不能拿该 local 的展示 home 冒充 CALL 结果。
        let target_home = producer.map_or_else(
            || self.facts.trusted_local_home_slot(local),
            |producer| self.facts.trusted_temp_home_slot(producer),
        );
        let Some(target_home) = target_home else {
            return false;
        };
        if target_home.slot() != slot && receiver != Some(target_home.slot()) {
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
                        *home != target_home
                            && !receiver.is_some_and(|slot| *home == HomeSlotKey::new(slot, 0))
                    })
            {
                return false;
            }
            // 一个匿名 LocalId 可承接多个值版本。原 CALL 的 callee、参数与结果都有
            // 精确 Def；不能把别的 value epoch 的隐藏写归到当前操作。
            self.facts.complete_temp_definition_write_homes(producer)
        } else {
            self.facts.complete_local_definition_write_homes(local)
        };
        !homes.is_empty()
            && homes.iter().all(|home| {
                *home == target_home
                    || receiver.is_some_and(|slot| *home == HomeSlotKey::new(slot, 0))
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
        receiver: Option<usize>,
        callee_chain: bool,
        argument_home: bool,
        original_producer: Option<crate::hir::common::TempId>,
    ) -> Option<HirExpr> {
        match expr {
            HirExpr::TempRef(temp) if self.native.is_some() && original_producer == Some(*temp) => {
                let index = *self.temp_definitions.get(temp)?;
                let target_home = self.facts.trusted_temp_home_slot(*temp)?;
                if index >= before
                    || index < self.next_event
                    || target_home.slot() != slot
                    || self.native.is_some_and(|context| {
                        context.closed.contains(&target_home)
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
                let HirStmt::Assign(assign) = self.run[index] else {
                    return None;
                };
                let [value] = assign.values.fixed.as_slice() else {
                    return None;
                };
                let value = self.expr(value, index, slot, None, true, false, None)?;
                self.finish_event(index)?;
                Some(value)
            }
            HirExpr::LocalRef(local) => {
                if self.native.is_some()
                    && self.facts.trusted_local_home_slot(*local)?.slot() < self.base
                {
                    return Some(expr.clone());
                }
                if let Some(index) = self.definition(*local, before) {
                    if index < self.next_event
                        || !self.homes_match(*local, index, slot, receiver, original_producer)
                    {
                        return None;
                    }
                    let value = scalar_local(self.run[index])?.1;
                    if let Some(native) = self.native {
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
                                    if reasons.iter().any(|reason| *reason !=
                                        crate::hir::common::HirInlineRetentionReason::BooleanValueContext))
                            || (!callee_chain
                                && !argument_home
                                && !self
                                    .facts
                                    .complete_local_definition_write_homes(*local)
                                    .is_disjoint(native.barred))
                            || !self
                                .facts
                                .complete_local_definition_write_homes(*local)
                                .is_disjoint(native.closed)
                            || (native.proto.physical_root_locals.contains(local)
                                && self.constructor_depth == 0
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
                    if self.constructors.contains_key(&index)
                        && let HirExpr::TableConstructor(table) = value
                    {
                        return self.constructor(index, table, slot);
                    }
                    // 同一 Boolean 参数 Local 已通过 homes_match 的完整写域及前述
                    // 保留约束；把整棵值树的结果槽传给叶比较，而非为每个谓词猜一个 phi。
                    let previous_boolean_frame = self.boolean_frame;
                    if self.dialect == DecompileDialect::Luajit
                        && argument_home
                        && crate::hir::value_facts::value_facts(value).is_boolean()
                        && self.facts.complete_local_definition_write_homes(*local)
                            .iter().copied().eq(std::iter::once(HomeSlotKey::new(slot, 0)))
                    {
                        self.boolean_frame = Some(slot);
                    }
                    let result = self.expr(
                        value,
                        index,
                        slot,
                        receiver,
                        callee_chain,
                        argument_home,
                        matches!(value, HirExpr::Closure(_))
                            .then_some(original_producer)
                            .flatten(),
                    );
                    self.boolean_frame = previous_boolean_frame;
                    let result = result?;
                    self.finish_event(index)?;
                    Some(result)
                } else {
                    let home = self.facts.trusted_local_home_slot(*local)?;
                    (home.slot() < self.base).then(|| expr.clone())
                }
            }
            HirExpr::ParamRef(param) => (self.facts.trusted_param_home_slot(*param)?.slot()
                < self.base)
                .then(|| expr.clone()),
            HirExpr::Call(call) => self
                .call(call, before, slot, false, CallWidth::Single)
                .map(|call| HirExpr::Call(Box::new(call))),
            HirExpr::Closure(_)
                if self.constructor_depth > 0 && self.constructor_field_is_preserved(expr) =>
            {
                Some(expr.clone())
            }
            HirExpr::Closure(closure)
                if self.native.is_some()
                    && argument_home
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
                // 原参数 CLOSURE 仍在同一槽创建；只消费当前 CALL 的精确 Def 和低槽
                // capture，不按匿名函数外形或子 proto 猜测原分配。合成 factory 无此来源。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.boolean_frame == Some(slot)
                    && self.luau_boolean_comparison(binary, slot) =>
            {
                // 已在低槽完成的比较可原样保留；CALL subject 仍由后面的完整帧分支逐事件证明。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame == Some(slot))
                    && (self.jit_lookup_comparison(binary, slot)
                        || self.jit_scalar_comparison(binary, slot)) =>
            {
                // 已嵌入的比较按原 operand 和 Boolean scratch 求值，不另提升声明。
                Some(expr.clone())
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && (argument_home || self.boolean_frame == Some(slot))
                    && let Some(left) = self.luau_arithmetic_comparison_operand(binary, before, slot) =>
            {
                let operand = if left { &binary.lhs } else { &binary.rhs };
                let previous_boolean_frame = self.boolean_frame.replace(slot);
                let value = self.expr(operand, before, slot + 1, None, false, true, None);
                self.boolean_frame = previous_boolean_frame;
                let value = value?;
                let mut rebuilt = binary.as_ref().clone();
                if left {
                    rebuilt.lhs = value;
                } else {
                    // HIR 的 Le/Lt 可以来自反向源码；重发时必须先计算原 scratch 的
                    // 算术，再准备常量，否则 compileExprAuto 会交换两个暂存槽。
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
                    && self.direct_home(&binary.lhs).is_some_and(|lhs| {
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
                    && !matches!(
                        self.dialect,
                        DecompileDialect::Luajit | DecompileDialect::Luau
                    )
                    && binary.op == crate::hir::common::HirBinaryOpKind::Concat =>
            {
                self.concat(binary, before, slot)
            }
            HirExpr::Binary(binary)
                if self.dialect == DecompileDialect::Luau
                    && self.native.is_some()
                    && argument_home
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
                if (self.dialect == DecompileDialect::Luajit
                    || self.dialect == DecompileDialect::Luau
                        && self.boolean_frame.is_some()
                        && self.boolean_frame == slot.checked_sub(1))
                    && self.native.is_some()
                    && argument_home
                    && self.constructor_depth == 0
                    && self.indexed_key_base.is_none()
                    && numeric_rk_arithmetic(binary) =>
            {
                // Luau 仅消费已经签证的 Boolean operand；普通返回帧仍需独立证明
                // 首项 COPY 和整个返回区，不能借 RK 算术外形退休该副本。
                self.direct_rk_arithmetic(binary, slot)
            }
            HirExpr::Binary(binary)
                if self.native.is_some()
                    && argument_home
                    && self.constructor_depth == 0
                    && self.indexed_key_base.is_none()
                    && !matches!(
                        self.dialect,
                        DecompileDialect::Luajit | DecompileDialect::Luau
                    )
                    && matches!(
                        binary.op,
                        crate::hir::common::HirBinaryOpKind::Add
                            | crate::hir::common::HirBinaryOpKind::Sub
                            | crate::hir::common::HirBinaryOpKind::Mul
                            | crate::hir::common::HirBinaryOpKind::Div
                            | crate::hir::common::HirBinaryOpKind::Mod
                            | crate::hir::common::HirBinaryOpKind::Pow
                    ) =>
            {
                self.puc_arithmetic(binary, before, slot)
            }
            HirExpr::Binary(binary)
                if self.constructor_depth > 0 || self.indexed_key_base.is_some() =>
            {
                let layout = self.facts.native_binary_layout(binary)?;
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
                    || layout.rhs.is_some()
                    || !matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
                    || !matches!(
                        binary.op,
                        crate::hir::common::HirBinaryOpKind::Add
                            | crate::hir::common::HirBinaryOpKind::Sub
                            | crate::hir::common::HirBinaryOpKind::Mul
                            | crate::hir::common::HirBinaryOpKind::Div
                            | crate::hir::common::HirBinaryOpKind::Mod
                            | crate::hir::common::HirBinaryOpKind::Pow
                    )
                {
                    return None;
                }
                let lhs_home = layout.lhs?;
                if lhs_home != HomeSlotKey::new(slot, 0)
                    && self.direct_home(&binary.lhs) != Some(lhs_home)
                    && !(self.indexed_key_base == Some(lhs_home.slot())
                        && lhs_home == HomeSlotKey::new(lhs_home.slot(), 0)
                        && slot == lhs_home.slot() + 1)
                {
                    return None;
                }
                let lhs = self.expr(
                    &binary.lhs,
                    before,
                    lhs_home.slot(),
                    None,
                    false,
                    false,
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
                    && argument_home
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
                    && (matches!(binary.rhs, HirExpr::TableAccess(_))
                        || matches!(binary.rhs, HirExpr::LocalRef(local)
                            if self.definition(local, before).is_some_and(|index|
                                matches!(scalar_local(self.run[index]), Some((_, HirExpr::TableAccess(_))))))) =>
            {
                // 左侧直接读取既有低槽，只有右侧索引需要 scratch，复用 Boolean 结果槽。
                // 不能套用左侧 CALL 已占一槽时的 RHS +1 规则，也不提前读取右侧字段。
                let rhs = self.register_operand(&binary.rhs, before, slot)?;
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
                    )
                    && (matches!(binary.lhs, HirExpr::Call(_) | HirExpr::Unary(_))
                        || matches!(&binary.lhs, HirExpr::LocalRef(local)
                        if self.definition(*local, before).is_some_and(|index| {
                            matches!(scalar_local(self.run[index]),
                                Some((_, HirExpr::Call(_) | HirExpr::Unary(_))))
                        }))
                        || self.luau_global_comparison_subject(binary, before, slot)
                        || self.puc_comparison_lookup_subject(binary, before, slot)
                        || !matches!(
                            self.dialect,
                            DecompileDialect::Luajit | DecompileDialect::Luau
                        ) && self.native.is_some_and(|context| context.constants_fit_rk)
                            && match &binary.lhs {
                                HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => {
                                    self.direct_home(&binary.lhs).is_some_and(|home| {
                                        home.slot() < self.base
                                            && (self.dialect == DecompileDialect::Lua51
                                                || self
                                                    .facts
                                                    .native_binary_layout(binary)
                                                    .is_some_and(|layout| {
                                                        layout.lhs == Some(home)
                                                            && layout.rhs.is_none()
                                                    }))
                                    })
                                }
                                HirExpr::TableAccess(access) => self
                                    .facts
                                    .table_read_result_home(access)
                                    .is_some_and(|home| {
                                        home == HomeSlotKey::new(slot, 0)
                                            && (self
                                                .facts
                                                .native_table_read_layout(access)
                                                .is_some_and(|layout| {
                                                    layout.key.is_none()
                                                        && self.direct_home(&access.base)
                                                            == Some(layout.base)
                                                        && layout.base.slot() < self.base
                                                })
                                                // 连续 GETTABLE 也可原位准备 Boolean subject；
                                                // 这里只接原比较同槽/内嵌 RHS，逐层读取的 base、
                                                // key 和事件顺序仍交下方 expr 的完整 register_lookup。
                                                || matches!(access.base, HirExpr::TableAccess(_))
                                                    && self.facts.native_binary_layout(binary)
                                                        .is_some_and(|layout| layout.lhs == Some(home)
                                                            && layout.rhs.is_none()))
                                    }),
                                _ => false,
                            })
                    && self.comparison_rhs_is_supported(
                        binary, before,
                        slot + 1 + usize::from(self.dialect == DecompileDialect::Luau),
                    ) =>
            {
                // 参数已有比较值语境；CALL/Unary/GETTABLE subject 保持原参数暂存槽，
                // 低槽 local/param 直接参与比较。比较本身可执行元方法，不据值类型判纯。
                // Luau 先保留 Boolean 目标，再在其上方求值 subject；PUC 复用目标槽。
                // 每个原 CALL/Unary 仍核对自己的精确结果 home，不按语法猜测已经移动成功。
                let subject_slot = slot + usize::from(self.dialect == DecompileDialect::Luau);
                let lhs = self.expr(&binary.lhs, before, subject_slot, None, false, true, None)?;
                let rhs = if self.dialect != DecompileDialect::Luau
                    && matches!(binary.rhs, HirExpr::LocalRef(_) | HirExpr::TableAccess(_))
                {
                    // 已由比较布局签证的 RHS 是原寄存器操作数；读取须在 lhs 后原位重发。
                    self.register_operand(&binary.rhs, before, subject_slot + 1)?
                } else {
                    self.expr(&binary.rhs, before, subject_slot + 1, None, false, false, None)?
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
                if self.native.is_some_and(|context| {
                    let home = HomeSlotKey::new(slot, 0);
                    !context.barred.contains(&home) && !context.closed.contains(&home)
                }) && !matches!(
                    self.dialect,
                    DecompileDialect::Luajit | DecompileDialect::Luau
                ) && matches!(unary.expr, HirExpr::TableAccess(_) | HirExpr::LocalRef(_))
                    && self.facts.unary_operand_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0)) =>
            {
                // 原位一元操作复用 lookup 准备槽；每次 GETTABLE 与最终 LEN/NOT 均在原 home 写回。
                let value = self.register_operand(&unary.expr, before, slot)?;
                Some(HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                    source_site: unary.source_site,
                    op: unary.op,
                    expr: value,
                })))
            }
            HirExpr::Unary(unary)
                if self.indexed_key_base.is_some()
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                    && self
                        .facts
                        .operation_operand_preparation(unary.source_site?, &unary.expr)
                        == Some(HomeSlotKey::new(slot, 0)) =>
            {
                Some(expr.clone())
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
                    && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
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
                    && matches!(logical.lhs, HirExpr::Call(_))
                    && self
                        .direct_home(&logical.rhs)
                        .is_some_and(|home| home.slot() < self.base) =>
            {
                // 普通值短路不同于 Boolean 比较树：CALL 先在原结果槽取一个值，
                // 仅选中右臂时读取既有低槽并写回该槽。rhs 不消费任何无条件 producer。
                // 外层原参数/CONCAT 帧及 Local 的完整写域仍核对最终结果和声明身份。
                let lhs = self.expr(&logical.lhs, before, slot, None, false, true, None)?;
                let rebuilt = Box::new(crate::hir::common::HirLogicalExpr {
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
                if self.native.is_some() && self.pure_conditional_value(expr) =>
            {
                // 原 callee/参数的 phi home 已由调用布局与目标声明核对。这里只保留
                // 既有条件值表达式的低槽读取；不把无条件 producer 塞进短路分支。
                Some(expr.clone())
            }
            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) if self.native.is_some() => {
                self.comparison_tree(expr, before, slot)
            }
            HirExpr::TableConstructor(table)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && self.constructor_depth > 0 =>
            {
                self.completed_luau_array(table, slot)
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
                    && matches!(table.allocation, HirTableAllocation::PucBatched(_)) =>
            {
                self.complete_constructor(table, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && self.dialect == DecompileDialect::Luau
                    && matches!(access.key, HirExpr::Binary(_))
                    && self.facts.native_table_read_layout(access).is_some_and(|layout| layout.key.is_some()) =>
            {
                // O0 的字面键也可能占寄存器，仍由既有字面 lookup 入口重发；
                // 此处分派的是含算术准备的键，不能用 key home 的有无抢占旧能力。
                self.luau_lookup(access, before, slot)
            }
            HirExpr::TableAccess(access)
                if self.native.is_some()
                    && !matches!(
                        self.dialect,
                        DecompileDialect::Luajit | DecompileDialect::Luau
                    )
                    && (self.register_operand
                        || matches!(access.base, HirExpr::TableAccess(_))
                        || !matches!(
                            access.key,
                            HirExpr::String(_) | HirExpr::Integer(_) | HirExpr::Number(_)
                        )) =>
            {
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
                        || self.direct_home(&access.base) != Some(layout.base)
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
            HirExpr::GlobalRef(global) if self.register_operand => {
                (self.facts.global_read_frame(global, self.dialect)
                    == Some(HomeSlotKey::new(slot, 0)))
                .then(|| expr.clone())
            }
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::GlobalRef(_) => Some(expr.clone()),
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
        let buffer = self.facts.native_concat_buffer(binary)?;
        // Luau 的单上值赋值先预留 RHS 结果，再分配 CONCAT 操作数区；
        // PUC 的结果则覆盖首操作数。调用方仍须证明该表达式语境的原入口。
        let operand_start = slot + usize::from(self.dialect == DecompileDialect::Luau);
        if buffer.start.index() != operand_start
            || self.facts.operation_result_home(binary.source_site?)
                != Some(HomeSlotKey::new(slot, 0))
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

    /// GlobalRef 本身没有 source site；只消费仍有原定义的高槽读取，并由比较的
    /// operand 布局证明该 home。全局读取可触发环境元方法，仍走 expr 的事件游标。
    fn luau_global_comparison_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
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

    /// 原左侧字段先在 Boolean 目标槽求值；物化 local 只转交这次读取，不借同槽其它版本。
    fn puc_comparison_lookup_subject(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        if matches!(
            self.dialect,
            DecompileDialect::Luajit | DecompileDialect::Luau
        ) || !self.native.is_some_and(|context| context.constants_fit_rk)
        {
            return false;
        }
        let HirExpr::LocalRef(local) = binary.lhs else {
            return false;
        };
        let Some(index) = self.definition(local, before) else {
            return false;
        };
        let Some((_, HirExpr::TableAccess(access))) = scalar_local(self.run[index]) else {
            return false;
        };
        let home = HomeSlotKey::new(slot, 0);
        self.facts.trusted_local_home_slot(local) == Some(home)
            && matches!(access.sources, crate::hir::common::HirOperationSources::Single(source)
                if self.facts.operation_result_reference_unaliased(source))
            && self.facts.table_read_result_home(access) == Some(home)
            && self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(home))
            && self
                .facts
                .native_table_read_layout(access)
                .is_some_and(|layout| {
                    layout.key.is_none()
                        && layout.base.slot() < self.base
                        && self.direct_home(&access.base) == Some(layout.base)
                })
    }

    fn comparison_rhs_is_supported(
        &self,
        binary: &crate::hir::common::HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> bool {
        let expr = &binary.rhs;
        if self.dialect != DecompileDialect::Luajit
            && self.direct_home(expr).is_some_and(|home| {
                home.slot() < self.base
                    && self
                        .facts
                        .native_binary_layout(binary)
                        .is_some_and(|layout| {
                            layout.rhs == Some(home)
                                && (self.dialect != DecompileDialect::Luau
                                    || layout.lhs == Some(HomeSlotKey::new(slot - 1, 0)))
                        })
            })
        {
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
            return true;
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
        if let HirExpr::TableAccess(access) = value {
            let home = HomeSlotKey::new(slot, 0);
            // 比较先保留 lhs 结果，再为 rhs lookup 分配一槽。
            // 原比较、GETTABLE 输出和低槽 base 必须一致；不把 CALL 前的 COPY
            // 当作 CALL 后读取。JIT 动态 key 仅接与 lookup 结果同槽的准备区；
            // Luau 则在 lookup 结果高一槽准备 key；实际表达式继续由方言 lookup owner 验证。
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| {
                    layout.rhs == Some(home) && layout.lhs == Some(HomeSlotKey::new(slot - 1, 0))
                })
                && self.facts.table_read_result_home(access) == Some(home)
                && self
                    .facts
                    .native_table_read_layout(access)
                    .is_some_and(|layout| {
                        (layout.key.is_none()
                            || self.dialect == DecompileDialect::Luajit && layout.key == Some(home)
                            || self.dialect == DecompileDialect::Luau
                                && layout.key == Some(HomeSlotKey::new(slot + 1, 0)))
                            && layout.base.slot() < self.base
                            && self.direct_home(&access.base) == Some(layout.base)
                    });
        }
        matches!(value, HirExpr::Unary(unary)
            if unary.op == crate::hir::common::HirUnaryOpKind::Not
                && self.facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
                && self.direct_home(&unary.expr).is_some_and(|home| home.slot() < self.base))
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
        if let (Some(lhs), Some(rhs)) =
            (self.direct_home(&binary.lhs), self.direct_home(&binary.rhs))
            && lhs.slot() < self.base
            && rhs.slot() < self.base
        {
            return self
                .facts
                .native_binary_layout(binary)
                .is_some_and(|layout| layout.lhs == Some(lhs) && layout.rhs == Some(rhs));
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
            HirExpr::LocalRef(_) | HirExpr::ParamRef(_) => self
                .direct_home(&binary.lhs)
                .is_some_and(|home| home.slot() < self.base),
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

    /// 比较的表操作数仍在原 scratch 读取：具名上值字段复用结果槽，数字索引
    /// 另在高一槽准备 base。准备证书绑定唯一 GETUPVAL use→Def，不按上值编号猜槽。
    fn luau_comparison_table_read(
        &self,
        access: &crate::hir::common::HirTableAccess,
        slot: usize,
    ) -> bool {
        let Some(layout) = self.facts.native_table_read_layout(access) else {
            return false;
        };
        if layout.key.is_some()
            || self.facts.table_read_result_home(access) != Some(HomeSlotKey::new(slot, 0))
            || !matches!(access.key, HirExpr::String(_) | HirExpr::Integer(1..=256))
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
        if self.direct_home(&access.base) == Some(layout.base) && layout.base.slot() < self.base {
            return true;
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
    fn comparison_tree(&mut self, expr: &HirExpr, before: usize, slot: usize) -> Option<HirExpr> {
        match expr {
            HirExpr::Binary(_) | HirExpr::Call(_) => {
                self.expr(expr, before, slot, None, false, false, None)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                let lhs = self.comparison_tree(&logical.lhs, before, slot)?;
                let checkpoint = (self.first_event, self.next_event);
                let rhs = self.comparison_tree(&logical.rhs, before, slot)?;
                // 候选拒绝[SemanticBarrier:EvalOrder]：右臂不能吸收原本无条件执行的 CALL 等事件。
                if checkpoint != (self.first_event, self.next_event) {
                    return None;
                }
                let rebuilt = Box::new(crate::hir::common::HirLogicalExpr { lhs, rhs });
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
                closure
                    .captures
                    .iter()
                    .all(|capture| match capture.binding {
                        crate::hir::common::HirBinding::Local(local) => self
                            .facts
                            .trusted_local_home_slot(local)
                            .is_some_and(|home| home.slot() < self.base),
                        crate::hir::common::HirBinding::Param(param) => self
                            .facts
                            .trusted_param_home_slot(param)
                            .is_some_and(|home| home.slot() < self.base),
                        crate::hir::common::HirBinding::Upvalue(_) => true,
                        crate::hir::common::HirBinding::Temp(_) => false,
                    })
            }
            _ => false,
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
                && self.facts.trusted_local_home_slot(local)?.slot() >= self.base
                && self.facts.promoted_local_for_temp(frame.callee) != Some(local)
            {
                return None;
            }
            args_start
        } else {
            slot + 1
        };
        let (callee, first_arg) = if call.is_method() {
            let HirCallRootHandoff::MethodCallee(protocol_id) = call.callee_root_handoff?;
            let protocol = self.facts.method_setup_protocol(protocol_id)?;
            if call.method != HirMethodCall::Explicit
                || call.fastcall.is_some()
                || self.facts.trusted_temp_home_slot(protocol.callee_temp)?
                    != HomeSlotKey::new(slot, 0)
                || !protocol
                    .method_key
                    .as_utf8()
                    .is_some_and(|key| self.dialect.is_identifier_name(key))
                || !(call.argument_roots.iter().any(|root| {
                    root.argument == 0
                        && self.facts.trusted_temp_home_slot(root.producer)
                            == Some(HomeSlotKey::new(args_start, 0))
                }) || (matches!(width, CallWidth::Tail)
                    && native_frame.is_some_and(|frame| {
                        frame.results.is_none() && frame.arguments_unaliased
                    })
                    // TAILCALL 没有普通 CALL 的根交接许可，但原参数 Def/槽仍存在。
                    // 只用于完整 SELF 帧重发；不向其它消费者制造 argument root。
                    && self.facts.call_argument_value(call, 0).is_some_and(|producer| {
                        self.facts.trusted_temp_home_slot(producer)
                            == Some(HomeSlotKey::new(args_start, 0))
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
                        || self.facts.trusted_local_home_slot(*local)? != HomeSlotKey::new(slot, 0)
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
            access.base = self.expr(
                &access.base,
                lookup_before,
                slot,
                Some(args_start),
                true,
                false,
                None,
            )?;
            let callee = HirExpr::TableAccess(Box::new(access));
            if let Some(index) = lookup_index {
                self.finish_event(index)?;
            }
            method = HirMethodCall::Implicit;
            transaction = None;
            self.methods += 1;
            (callee, 1)
        } else if native_frame.is_some() || outer {
            (
                self.expr(
                    &call.callee,
                    before,
                    slot,
                    None,
                    true,
                    false,
                    native_frame.map(|frame| frame.callee),
                )?,
                0,
            )
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
        let fixed = call
            .args
            .fixed
            .iter()
            .enumerate()
            .skip(first_arg)
            .map(|(index, arg)| {
                // 原参数 Def 的交接证明同样在本次 CALL 时点排除了打开的 capture；
                // 后续其它 binding 复用该槽不能反向阻止这一原子帧事务。
                let argument_home = argument_roots.get(&index).is_some_and(|&producer| {
                    self.facts.trusted_temp_home_slot(producer)
                        == Some(HomeSlotKey::new(args_start + index, 0))
                        && matches!(arg, HirExpr::LocalRef(local)
                            if self.facts.promoted_local_for_temp(producer) == Some(*local))
                }) || native_frame
                    .is_some_and(|frame| frame.arguments_unaliased)
                    && match arg {
                        HirExpr::LocalRef(local) => {
                            self.facts.trusted_local_home_slot(*local)
                                == Some(HomeSlotKey::new(args_start + index, 0))
                        }
                        // 已处于参数表达式中的表没有待删除的 binding；完整 CALL 恢复
                        // 原参数槽时仍在此语境求值，不能要求不存在的 Local 身份。
                        HirExpr::TableConstructor(_) | HirExpr::Closure(_) => true,
                        HirExpr::LogicalOr(logical)
                            if self.dialect == DecompileDialect::Luau
                                && matches!(logical.rhs, HirExpr::TableConstructor(_)) =>
                        {
                            true
                        }
                        HirExpr::Binary(binary) if self.dialect == DecompileDialect::Luajit => self
                            .facts
                            .comparison_result_temp(binary)
                            .is_some_and(|temp| {
                                self.facts.call_argument_value(call, index) == Some(temp)
                                    && self.facts.trusted_temp_home_slot(temp)
                                        == Some(HomeSlotKey::new(args_start + index, 0))
                            }),
                        _ => false,
                    };
                self.expr(
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
                            _ => false,
                        }),
                )
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
        self.finish_dispatch(call, before)?;
        Some(HirCallExpr {
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
            plain_method_syntax: false,
        })
    }
}
