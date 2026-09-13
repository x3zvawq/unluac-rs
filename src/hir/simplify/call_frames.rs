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

mod native;
mod tables;

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
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
    is_chunk_entry: bool,
) -> bool {
    // 普通 local 同样可能多保留原参数表；没有显式 PhysicalRoot 标签不代表帧无需恢复。
    // builder 只消费已物化 Local，完全没有 local 时才不存在可收回的前缀。
    if proto.local_count == 0 {
        return false;
    }
    let constraints = frame_restrictions(proto, facts);
    native::restore(
        proto,
        facts,
        dialect,
        &constraints.barred,
        &constraints.closed,
        is_chunk_entry,
    )
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
                        *home != HomeSlotKey::new(slot, 0)
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
                *home == HomeSlotKey::new(slot, 0)
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
                if index >= before
                    || index < self.next_event
                    || self.native.is_some_and(|context| {
                        context.closed.contains(&HomeSlotKey::new(slot, 0))
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
                        .any(|home| *home != HomeSlotKey::new(slot, 0))
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
                    let result = self.expr(
                        value,
                        index,
                        slot,
                        receiver,
                        callee_chain,
                        argument_home,
                        None,
                    )?;
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
            HirExpr::Binary(binary)
                if self.boolean_frame == Some(slot)
                    && self.luau_boolean_comparison(binary, slot) =>
            {
                // 已在低槽完成的比较可原样保留；CALL subject 仍由后面的完整帧分支逐事件证明。
                Some(expr.clone())
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
            HirExpr::Binary(binary) if self.constructor_depth > 0 => {
                let layout = self.facts.native_binary_layout(binary)?;
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
                {
                    return None;
                }
                let lhs = self.expr(&binary.lhs, before, slot, None, false, false, None)?;
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
                        || !matches!(
                            self.dialect,
                            DecompileDialect::Luajit | DecompileDialect::Luau
                        ) && self.native.is_some_and(|context| context.constants_fit_rk)
                            && match &binary.lhs {
                                HirExpr::LocalRef(_) | HirExpr::ParamRef(_)
                                    if self.dialect == DecompileDialect::Lua51 =>
                                {
                                    self.direct_home(&binary.lhs)
                                        .is_some_and(|home| home.slot() < self.base)
                                }
                                HirExpr::TableAccess(access) => self
                                    .facts
                                    .table_read_result_home(access)
                                    .is_some_and(|home| {
                                        home == HomeSlotKey::new(slot, 0)
                                            && self
                                                .facts
                                                .native_table_read_layout(access)
                                                .is_some_and(|layout| {
                                                    layout.key.is_none()
                                                        && self.direct_home(&access.base)
                                                            == Some(layout.base)
                                                        && layout.base.slot() < self.base
                                                })
                                    }),
                                _ => false,
                            })
                    && self.comparison_rhs_is_supported(&binary.rhs, before, slot + 1) =>
            {
                // 参数已有比较值语境；CALL/Unary/GETTABLE subject 保持原参数暂存槽，
                // 低槽 local/param 直接参与比较。比较本身可执行元方法，不据值类型判纯。
                // Luau 先保留 Boolean 目标，再在其上方求值 subject；PUC 复用目标槽。
                // 每个原 CALL/Unary 仍核对自己的精确结果 home，不按语法猜测已经移动成功。
                let subject_slot = slot + usize::from(self.dialect == DecompileDialect::Luau);
                let lhs = self.expr(&binary.lhs, before, subject_slot, None, false, true, None)?;
                let rhs = self.expr(
                    &binary.rhs,
                    before,
                    subject_slot + 1,
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
                        rhs,
                    },
                )))
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
            HirExpr::UpvalueRef(_) if self.native.is_some() => Some(expr.clone()),
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
        if buffer.start.index() != slot
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
            let value = self.expr(operand, before, slot + offset, None, false, true, None)?;
            if matches!(&value, HirExpr::Binary(nested)
                if nested.op == crate::hir::common::HirBinaryOpKind::Concat)
            {
                return None;
            }
            values.push(value);
        }
        crate::hir::common::HirBinaryExpr::concat(binary.source_site?, values)
    }

    fn comparison_rhs_is_supported(&self, expr: &HirExpr, before: usize, slot: usize) -> bool {
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
        use crate::hir::common::HirBinaryOpKind::{Eq, Le, Lt};
        if self.dialect != DecompileDialect::Luau || !matches!(binary.op, Eq | Lt | Le) {
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
        if matches!(binary.op, Lt | Le) {
            let Some(layout) = self.facts.native_binary_layout(binary) else {
                return false;
            };
            // 有序比较的常量仍占 operand scratch；不把 Eq 的内嵌常量规则
            // 套到 LT/LE。保持原左右顺序，因此元方法方向和短路位置不变。
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
            HirExpr::TableAccess(access) => {
                self.facts
                    .table_read_result_home(access)
                    .is_some_and(|home| {
                        home == HomeSlotKey::new(slot + 1, 0)
                            && self
                                .facts
                                .native_table_read_layout(access)
                                .is_some_and(|layout| {
                                    layout.key.is_none()
                                        && self.direct_home(&access.base) == Some(layout.base)
                                        && layout.base.slot() < self.base
                                })
                    })
            }
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

    /// 保留整棵比较树的原分组，每个短路右臂都禁止消费无条件 producer。
    /// 子逻辑节点直接递归，不再逐层重扫 pure_conditional_value，长比较链仍只访问各节点一次。
    fn comparison_tree(&mut self, expr: &HirExpr, before: usize, slot: usize) -> Option<HirExpr> {
        match expr {
            HirExpr::Binary(_) => self.expr(expr, before, slot, None, false, false, None),
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
        let mut method = call.method;
        let mut transaction = call.method_rewrite_transaction;
        let native_frame = if self.native.is_some() {
            Some(self.facts.native_call_frame(call)?)
        } else {
            None
        };
        let args_start = if let Some(frame) = native_frame {
            if frame.home != HomeSlotKey::new(slot, 0)
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
                || !call.argument_roots.iter().any(|root| {
                    root.argument == 0
                        && self.facts.trusted_temp_home_slot(root.producer)
                            == Some(HomeSlotKey::new(args_start, 0))
                })
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
                        HirExpr::TableConstructor(_) => true,
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
                        .filter(|producer| {
                            matches!(arg, HirExpr::LocalRef(local)
                            if self.facts.promoted_local_for_temp(*producer) == Some(*local))
                        }),
                )
            })
            .collect::<Option<Vec<_>>>()?;
        let tail = match &call.args.tail {
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
        })
    }
}
