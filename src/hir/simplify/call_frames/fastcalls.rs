//! 恢复完整帧树中的 FASTCALL 参数与开放尾准备协议。
//!
//! 消费 Promotion 的 builtin 和原槽事实，由共享 FrameBuilder 提供统一帧证明。

use super::*;
use crate::hir::common::TempId;

/// 当前 proto 中唯一初始化、无引用捕获的 builtin 别名；值表示根读取是否为 assert。
/// 仅供同一 HIR 快照的完整帧消费，声明或写入变化后重建，不随 Promotion 长期保存。
#[derive(Default)]
pub(super) struct CalleeAliases(BTreeMap<LocalId, bool>);

impl CalleeAliases {
    pub(super) fn collect(proto: &HirProto, captured: &BTreeSet<LocalId>) -> Self {
        use crate::hir::common::HirBinding;
        use crate::hir::simplify::mention::BindingWriteCollector;
        use crate::hir::visit::{HirVisitor, visit_stmts};

        enum Source {
            Named(bool),
            Alias(LocalId),
        }
        #[derive(Default)]
        struct Initializers(BTreeMap<LocalId, Source>);
        impl HirVisitor<'_> for Initializers {
            fn visit_stmt(&mut self, stmt: &HirStmt) {
                let HirStmt::LocalDecl(decl) = stmt else {
                    return;
                };
                let ([local], [value], None) = (
                    decl.bindings.as_slice(),
                    decl.values.fixed.as_slice(),
                    &decl.values.tail,
                ) else {
                    return;
                };
                let source = match value {
                    HirExpr::LocalRef(source) => Source::Alias(*source),
                    value if callee_is_named(value) => Source::Named(
                        matches!(value, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("assert")),
                    ),
                    _ => return,
                };
                self.0.insert(*local, source);
            }
        }
        let mut writes = BTreeMap::<LocalId, usize>::new();
        let mut collectors = (
            Initializers::default(),
            BindingWriteCollector(|binding| {
                if let HirBinding::Local(local) = binding {
                    *writes.entry(local).or_default() += 1;
                }
            }),
        );
        visit_stmts(&proto.body.stmts, &mut collectors);
        let (initializers, _) = collectors;
        let mut result = Self::default();
        let mut dependents = BTreeMap::<LocalId, Vec<LocalId>>::new();
        let mut pending = Vec::new();
        for (local, source) in initializers.0 {
            if writes.get(&local) != Some(&1) || captured.contains(&local) {
                continue;
            }
            match source {
                Source::Named(assert) => pending.push((local, assert)),
                Source::Alias(source) => dependents.entry(source).or_default().push(local),
            }
        }
        // 每条别名边最多传播一次；未到达具名根的环或可变绑定不获得许可。
        while let Some((local, assert)) = pending.pop() {
            result.0.insert(local, assert);
            if let Some(users) = dependents.remove(&local) {
                pending.extend(users.into_iter().map(|user| (user, assert)));
            }
        }
        result
    }

    pub(super) fn accepts(&self, callee: &HirExpr) -> bool {
        callee_is_named(callee)
            || matches!(callee, HirExpr::LocalRef(local) if self.0.contains_key(local))
            || matches!(callee, HirExpr::TableAccess(access)
                if matches!((&access.base, &access.key),
                    (HirExpr::LocalRef(local), HirExpr::String(key))
                        if self.0.contains_key(local)
                            && key.as_utf8().is_some_and(|key| DecompileDialect::Luau.is_identifier_name(key))))
    }

    pub(super) fn accepts_assert(&self, callee: &HirExpr) -> bool {
        matches!(callee, HirExpr::GlobalRef(global) if global.key.as_utf8() == Some("assert"))
            || matches!(callee, HirExpr::LocalRef(local) if self.0.get(local) == Some(&true))
    }
}

/// 原 FASTCALL 已签发 builtin 身份，具名读取仍保持原全局或库字段拼写。
fn callee_is_named(callee: &HirExpr) -> bool {
    let identifier = |name: &crate::lua_string::LuaString| {
        name.as_utf8()
            .is_some_and(|name| DecompileDialect::Luau.is_identifier_name(name))
    };
    match callee {
        HirExpr::GlobalRef(global) => identifier(&global.key),
        HirExpr::TableAccess(access) => matches!((&access.base, &access.key),
            (HirExpr::GlobalRef(global), HirExpr::String(key)) if identifier(&global.key) && identifier(key)),
        _ => false,
    }
}

impl FrameBuilder<'_> {
    /// 开放尾参数先求值，fallback 再读取原 callee；固定结果宽度独立核对。
    pub(super) fn fastcall_open(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        width: CallWidth,
    ) -> Option<HirCallExpr> {
        let context = self.native?;
        let facts = self.facts;
        let dialect = self.dialect;
        if !call.fastcall.is_some_and(|protocol| {
            protocol.tail_is_direct()
                && (0..call.args.fixed.len()).all(|index| protocol.fixed_is_direct(index))
        }) {
            return None;
        }
        if dialect != DecompileDialect::Luau || call.method != HirMethodCall::None {
            return None;
        }
        let tail = call.args.tail.as_ref()?;
        if tail.exact_width().is_some() {
            return None;
        }
        let frame = facts.native_fastcall_frame(call)?;
        let ValuePack::Open(argument_home) = frame.args else {
            return None;
        };
        if frame.home.slot() != slot
            || !match (width, frame.results) {
                (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
                (CallWidth::Single, Some(ResultPack::Fixed(pack))) => {
                    pack.start.index() == frame.home.slot() && pack.len == 1
                }
                (CallWidth::Fixed(width), Some(ResultPack::Fixed(pack))) => {
                    pack.start.index() == frame.home.slot() && pack.len == width
                }
                (CallWidth::Open, Some(ResultPack::Open(start))) => start.index() == slot,
                _ => false,
            }
            || !frame.arguments_unaliased
            || argument_home.index() != frame.home.slot() + 1
        {
            return None;
        }
        let roots = call
            .argument_roots
            .iter()
            .map(|root| (root.argument, root.producer))
            .collect::<BTreeMap<_, _>>();
        let mut fixed = Vec::with_capacity(call.args.fixed.len());
        for (index, value) in call.args.fixed.iter().enumerate() {
            let value = self.expr(
                value,
                before,
                argument_home.index() + index,
                None,
                false,
                true,
                facts
                    .call_argument_value(call, index)
                    .or_else(|| roots.get(&index).copied()),
            )?;
            // expr 已逐事件重放比较的输入；结果 phi 必须仍是当前参数的原写入槽。
            // 带独立 Boolean 预写的值树仍需专门事务，不能仅因结果相同就漏掉预写。
            let comparison = facts.boolean_argument_prewrite(call, index).is_none()
                && matches!(&value, HirExpr::Binary(binary)
                    if facts.comparison_result_temp(binary).is_some_and(|temp|
                        facts.call_argument_value(call, index) == Some(temp)
                            && facts.trusted_temp_home_slot(temp)
                                == Some(HomeSlotKey::new(argument_home.index() + index, 0))));
            if !matches!(
                value,
                HirExpr::Nil
                    | HirExpr::Boolean(_)
                    | HirExpr::Integer(_)
                    | HirExpr::Number(_)
                    | HirExpr::String(_)
                    | HirExpr::LocalRef(_)
                    | HirExpr::ParamRef(_)
                    | HirExpr::Call(_)
            ) && !comparison
            {
                return None;
            }
            fixed.push(value);
        }
        let tail = self.open_tail(
            tail,
            facts.call_vararg_tail_home(call),
            before,
            argument_home.index() + fixed.len(),
        )?;
        let callee = self.expr(
            &call.callee,
            before,
            frame.home.slot(),
            None,
            true,
            false,
            Some(frame.callee),
        )?;
        if !context.callee_aliases.accepts(&callee) {
            return None;
        }
        self.finish_dispatch(call, before)?;
        let rebuilt = HirCallExpr {
            callee,
            args: HirValuePack {
                fixed,
                tail: Some(tail),
            },
            required_luau_inlining: call.required_luau_inlining,
            source_site: call.source_site,
            argument_roots: call.argument_roots.clone(),
            frame_root_ends: call.frame_root_ends.clone(),
            method: call.method,
            fastcall: call.fastcall,
            method_key: call.method_key.clone(),
            callee_root_handoff: call.callee_root_handoff,
            method_rewrite_transaction: call.method_rewrite_transaction,
            plain_method_syntax: call.plain_method_syntax,
            boolean_prewrite_arguments: call.boolean_prewrite_arguments.clone(),
        };
        Some(rebuilt)
    }

    /// 预写属于原 Boolean 值决策；direct 参数无论是否与 COPY 参数混合，都须
    /// 在同一结果槽重发它。值树的比较布局和后继声明仍由完整帧核对。
    pub(super) fn consume_boolean_argument_prewrite(
        &mut self,
        call: &HirCallExpr,
        argument_index: usize,
        argument: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<()> {
        let Some(prewrite) = self.facts.boolean_argument_prewrite(call, argument_index) else {
            // 字段值等左臂直接写入结果槽，没有 Boolean 预写。此处不消费
            // 任何语句；完整帧事件游标仍核对连续准备区，不能借此删除未获证的预写。
            return Some(());
        };
        self.consume_boolean_prewrite(
            (
                prewrite.initial,
                prewrite.result,
                prewrite.home,
                prewrite.initial_value,
            ),
            prewrite.reference_uncaptured,
            argument,
            before,
            slot,
        )
    }

    pub(super) fn consume_boolean_prewrite(
        &mut self,
        (initial, result, home, initial_value): (TempId, TempId, HomeSlotKey, bool),
        reference_uncaptured: bool,
        argument: &HirExpr,
        before: usize,
        slot: usize,
    ) -> Option<()> {
        let context = self.native?;
        let facts = self.facts;
        if home.slot() != slot
            || matches!(argument, HirExpr::LocalRef(local)
                if facts.promoted_local_for_temp(result) != Some(*local))
        {
            return None;
        }
        if matches!(argument, HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_))
            && reference_uncaptured
            && !self.temp_definitions.contains_key(&initial)
            && facts
                .promoted_local_for_temp(initial)
                .is_none_or(|local| self.definition(local, before).is_none())
        {
            // 前轮已将预写并入原 CALL 的值树。树本身重发 Boolean 写，不再要求
            // 已退休的声明；各叶来源、原结果槽与整个调用的声明前缀仍须重新核对。
            return Some(());
        }
        let index = if let Some(&index) = self.temp_definitions.get(&initial) {
            if index >= before
                || !matches!(self.run[index], HirStmt::Assign(assign)
                    if assign.targets.as_slice() == [HirLValue::Temp(initial)]
                        && assign.values.fixed.as_slice() == [HirExpr::Boolean(initial_value)]
                        && assign.values.tail.is_none())
            {
                return None;
            }
            index
        } else {
            // locals 可以复用旧 callee 的身份；只消费当前 Boolean 写，不退休旧声明。
            let local = facts.promoted_local_for_temp(initial)?;
            // 入口预写和结果 phi 可以提升为同一 Local；预写在结果定义之前，
            // 不能把调用前最后一次结果赋值误认为原 Boolean 初始化。
            // 配对身份来自原值决策，结果表达式仍由后续完整帧逐事件消费。
            let before = if argument == &HirExpr::LocalRef(local)
                && facts.promoted_local_for_temp(result) == Some(local)
            {
                self.definition(local, before)?
            } else {
                before
            };
            let index = self.definition(local, before)?;
            // ProofIncomplete/BindingIdentity：预写的值、完整写域和公开身份须保持原合同。
            if !matches!(scalar_local(self.run[index]), Some((target, HirExpr::Boolean(value))) if target == local && *value == initial_value)
                || facts.trusted_local_home_slot(local) != Some(home)
                || !self.homes_match(local, index, slot, None, Some(initial))
                || context.proto.local_debug_hints[local.index()].is_some()
                || context.proto.local_debug_scopes[local.index()].is_some()
                // 本事务仍在原槽先写 Boolean，再求值完整参数；保留值语境并不要求独立声明。
                || matches!(context.proto.inline_dispositions.local(local),
                    crate::hir::common::HirInlineDisposition::Preserve(reasons)
                        if reasons.iter().any(|reason| *reason != crate::hir::common::HirInlineRetentionReason::BooleanValueContext))
                || (context.barred.contains(&home) && !reference_uncaptured)
                || context.closed.contains(&home)
            {
                return None;
            }
            index
        };
        self.finish_event(index)
    }

    pub(super) fn fastcall_fixed(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        width: CallWidth,
    ) -> Option<HirCallExpr> {
        self.native?;
        let facts = self.facts;
        let dialect = self.dialect;
        let protocol = call.fastcall?;
        if dialect != DecompileDialect::Luau
            || call.method != HirMethodCall::None
            || matches!(protocol, crate::transformer::FastCallProtocol::Mask { .. })
                && !(1..=3).contains(&call.args.fixed.len())
        {
            return None;
        }
        let frame = facts.native_fastcall_frame(call)?;
        // 通用 FASTCALL 的 All 表示全部参数直接准备，不表示 CALL 必须有开放尾。
        // 固定空参数区也保留原起点；callee 读取和结果帧仍由同一事务逐事件核对。
        let args = match (frame.args, &call.args.tail) {
            (ValuePack::Fixed(args), None)
                if matches!(protocol, crate::transformer::FastCallProtocol::All { .. })
                    || !protocol.tail_is_direct() =>
            {
                args
            }
            (ValuePack::Open(start), Some(tail))
                if protocol.tail_is_direct()
                    && tail.exact_width().is_none()
                    && matches!(tail.as_expr(), HirExpr::VarArg)
                    && facts.call_vararg_tail_home(call).map(HomeSlotKey::slot)
                        == Some(start.index() + call.args.fixed.len()) =>
            {
                // 原 VARARG 在 fallback CALL 前物化；没有额外求值事件，宽度保持开放。
                crate::transformer::RegRange {
                    start,
                    len: call.args.fixed.len(),
                }
            }
            _ => return None,
        };
        if frame.home.slot() != slot
            || args.len != call.args.fixed.len()
            || args.start.index() != frame.home.slot() + 1
            || !match (width, frame.results) {
                (CallWidth::Ignore, Some(ResultPack::Ignore)) => true,
                (CallWidth::Single, Some(ResultPack::Fixed(pack))) => {
                    pack.start.index() == frame.home.slot() && pack.len == 1
                }
                (CallWidth::Open, Some(ResultPack::Open(start))) => start.index() == slot,
                _ => false,
            }
            || !frame.arguments_unaliased
        {
            return None;
        }
        let copies = facts.fastcall_argument_copies(call)?;
        if copies.len()
            != (0..args.len)
                .filter(|index| !protocol.fixed_is_direct(*index))
                .count()
        {
            return None;
        }

        let mut arguments = vec![None; args.len];
        let mut boolean_prewrite_arguments = Vec::new();
        let mut copies = copies.iter();
        let mut callee = None;
        for prepare_direct in [true, false] {
            if !prepare_direct && facts.fastcall_callee_precedes_copies(call) {
                callee = Some(self.expr(
                    &call.callee,
                    before,
                    frame.home.slot(),
                    None,
                    true,
                    false,
                    Some(frame.callee),
                )?);
            }
            for (index, argument) in call.args.fixed.iter().enumerate() {
                let direct = protocol.fixed_is_direct(index);
                let embedded = protocol.fixed_is_embedded_constant(index);
                if (direct && !embedded) != prepare_direct {
                    continue;
                }
                let slot = args.start.index() + index;
                if direct {
                    let original_value = match argument {
                        HirExpr::LocalRef(local) => self
                            .definition(*local, before)
                            .and_then(|index| scalar_local(self.run[index]))
                            .map_or(argument, |(_, value)| value),
                        value => value,
                    };
                    let boolean_tree = !embedded
                        && (matches!(
                            original_value,
                            HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_)
                        ) || matches!(original_value, HirExpr::Unary(unary)
                                if unary.source_site.is_none()
                                    && unary.op == crate::hir::common::HirUnaryOpKind::Not
                                    && matches!(unary.expr, HirExpr::LogicalOr(_))));
                    let boolean_prewrite = !embedded
                        && !boolean_tree
                        && facts.boolean_argument_prewrite(call, index).is_some()
                        && matches!(original_value, HirExpr::Binary(_) | HirExpr::Unary(_));
                    if boolean_tree || boolean_prewrite {
                        self.consume_boolean_argument_prewrite(
                            call, index, argument, before, slot,
                        )?;
                    }
                    let previous_boolean_frame = self.boolean_frame;
                    if boolean_tree || boolean_prewrite {
                        self.boolean_frame = facts
                            .call_argument_value(call, index)
                            .and_then(|temp| facts.trusted_temp_home_slot(temp));
                    }
                    let value = self.expr(
                        argument,
                        before,
                        slot,
                        None,
                        false,
                        true,
                        facts.call_argument_value(call, index),
                    );
                    self.boolean_frame = previous_boolean_frame;
                    let value = value?;
                    let literal = matches!(
                        value,
                        HirExpr::Nil
                            | HirExpr::Boolean(_)
                            | HirExpr::Integer(_)
                            | HirExpr::Number(_)
                            | HirExpr::String(_)
                    );
                    let lookup = !embedded
                        && matches!(&value, HirExpr::TableAccess(access)
                if facts.table_read_result_home(access) == Some(HomeSlotKey::new(slot, 0))
                    && facts.native_table_read_layout(access).is_some_and(|layout|
                        layout.base.slot() < frame.home.slot()
                            && self.direct_home(&access.base) == Some(layout.base)
                            // 动态键已有低槽身份时，GETTABLE 不增加 key scratch；
                            // expr 已核对该读取，仍在后续参数及 fallback callee 之前执行。
                            && layout.key.is_none_or(|key|
                                key.slot() < frame.home.slot()
                                    && self.direct_home(&access.key) == Some(key))));
                    // CALL 的单结果与完整原槽准备由 self.call 签证；direct 阶段仍先于
                    // fallback COPY/lookup，不能借此移动未纳入同一事务的根释放。
                    let is_call = !embedded && matches!(value, HirExpr::Call(_));
                    // direct GETUPVAL 先写原参数槽，fallback 随后查找 callee；
                    // 读取身份须绑定本次 CALL，不能用同名上值替换较早的快照。
                    let upvalue = !embedded
                        && matches!(value, HirExpr::UpvalueRef(_))
                        && facts.call_argument_preparation(call, index, &value)
                            == Some(HomeSlotKey::new(slot, 0));
                    // compileExprFastcallN 对非 local 参数调用 compileExprTempTop；已有
                    // builder 证明表字段/事件，原 allocation 还须落在当前 direct 参数槽。
                    let table = !embedded
                        && matches!(&value, HirExpr::TableConstructor(table)
                        if facts.allocation_result_home(table).is_some_and(|home| home.slot() == slot));
                    // expr 已逐叶重发操作数；mixed 参数的 fallback COPY 不改变求值时点。
                    // 预写参数由完整值帧提供身份并重发 and/or 包装，裸比较核对独立 LOADBOOL 结果；
                    // 不再用只接受纯低槽值的形状查询拒绝已证明的条件操作数。
                    let comparison = !embedded
                        && matches!(&value, HirExpr::Binary(binary)
                            if boolean_prewrite && matches!(binary.op,
                                crate::hir::HirBinaryOpKind::Eq | crate::hir::HirBinaryOpKind::Lt
                                | crate::hir::HirBinaryOpKind::Le | crate::hir::HirBinaryOpKind::Gt
                                | crate::hir::HirBinaryOpKind::Ge)
                            || facts.comparison_result_temp(binary).is_some_and(|result|
                                facts.call_argument_value(call, index) == Some(result)
                                    && facts.trusted_temp_home_slot(result)
                                        .is_some_and(|home| home.slot() == slot)));
                    // direct 算术参数先在原参数槽求值，fallback 随后读取 callee；
                    // expr 已核对原操作数与准备顺序，这里再绑定原结果槽。
                    let arithmetic = !embedded
                        && matches!(&value, HirExpr::Binary(binary)
                            if binary.source_site.and_then(|site| facts.operation_result_home(site))
                                .is_some_and(|home| home.slot() == slot)
                                && is_scalar_binary_operation(binary.op));
                    // CONCAT 的原连续 buffer 已由 expr 整体重发；结果留在参数槽，
                    // 不把消息求值移到前一个参数之前，也不拆成额外源码声明。
                    let concat = !embedded
                        && matches!(&value, HirExpr::Binary(binary)
                            if binary.op == crate::hir::common::HirBinaryOpKind::Concat
                                && binary.source_site.and_then(|site| facts.operation_result_home(site))
                                    == Some(HomeSlotKey::new(slot, 0))
                                && facts.native_concat_buffer(binary)
                                    .is_some_and(|buffer| buffer.start.index() == slot + 1));
                    // 原生 NOT 也直接写参数槽；内部 CALL 的准备区由 expr 逐层核对，
                    // 不能把它当作仅改变谓词极性的 synthetic Not。
                    let negation = !embedded
                        && matches!(&value, HirExpr::Unary(unary)
                            if unary.op == crate::hir::common::HirUnaryOpKind::Not
                                && facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0)));
                    let conditional_table = !embedded
                        && matches!(&value, HirExpr::LogicalOr(logical)
                        if self.luau_table_or_empty_layout(logical, before, slot).is_some());
                    // 嵌入常量不能变成有事件的 RHS；其余表达式尚无此准备协议的证明。
                    if !literal
                        && !lookup
                        && !is_call
                        && !upvalue
                        && !table
                        && !comparison
                        && !arithmetic
                        && !concat
                        && !negation
                        && !conditional_table
                        && !boolean_tree
                    {
                        return None;
                    }
                    if boolean_prewrite {
                        boolean_prewrite_arguments.push((
                            index,
                            facts.boolean_argument_prewrite(call, index)?.initial_value,
                        ));
                    }
                    arguments[index] = Some(value);
                    continue;
                }
                let copy = copies.next()?;
                if copy.argument != index
                    // 编译参数位置只限定槽号；原 COPY producer 的完整 epoch 由
                    // Promotion 与 expr/homes_match 校验，循环后的新 epoch 仍可重发。
                    || copy.home.slot() != slot
                    || copy.source_home.slot() >= frame.home.slot()
                {
                    return None;
                }
                let value = self.expr(
                    argument,
                    before,
                    slot,
                    None,
                    false,
                    true,
                    Some(copy.producer),
                )?;
                let home = match &value {
                    HirExpr::LocalRef(local) => facts.trusted_local_home_slot(*local),
                    HirExpr::ParamRef(param) => facts.trusted_param_home_slot(*param),
                    HirExpr::TempRef(temp) if copy.source == Some(*temp) => {
                        // 仍未提升的低槽 phi 必须是原 COPY 的准确输入，不能只按同槽猜值。
                        facts.trusted_temp_home_slot(*temp)
                    }
                    _ => None,
                };
                if home != Some(copy.source_home) {
                    return None;
                }
                arguments[index] = Some(value);
            }
        }
        let arguments = arguments.into_iter().collect::<Option<Vec<_>>>()?;
        let callee = callee.or_else(|| {
            self.expr(
                &call.callee,
                before,
                frame.home.slot(),
                None,
                true,
                false,
                Some(frame.callee),
            )
        })?;
        // 保留具名读取或其不可变快照，不能用当前全局值替换保存过的 callee。
        if !self.native?.callee_aliases.accepts(&callee) {
            return None;
        }
        self.finish_dispatch(call, before)?;
        let rebuilt = HirCallExpr {
            callee,
            args: HirValuePack {
                fixed: arguments,
                tail: call.args.tail.clone(),
            },
            method: call.method,
            method_key: call.method_key.clone(),
            callee_root_handoff: call.callee_root_handoff,
            method_rewrite_transaction: call.method_rewrite_transaction,
            plain_method_syntax: false,
            boolean_prewrite_arguments,
            frame_root_ends: call.frame_root_ends.clone(),
            required_luau_inlining: call.required_luau_inlining,
            source_site: call.source_site,
            fastcall: call.fastcall,
            argument_roots: call.argument_roots.clone(),
        };
        Some(rebuilt)
    }
}
