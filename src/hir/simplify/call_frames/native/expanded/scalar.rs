//! 证明标量更新后 CALL 的高结果、低 COPY 展开帧。
//!
//! 现存闭包提供更新或恒等函数体；caller 只恢复字节码仍能证明的标量实参信息。
//! NOT 的赋值边界属于编译合同，不能再树化成会被编译器整体折叠的常量表达式。

use super::*;
use crate::hir::common::{HirAssign, HirUnaryExpr, HirUnaryOpKind};

/// O2 的内联发生在常量折叠之后。原比较仍存在时，用现存 identity 模板
/// 重发其字面量 LOAD；否则直接打印常量比较会在重编译时删除这次检查。
pub(super) fn constant_comparisons(
    context: NativeFrameContext<'_>,
    facts: &ProtoPromotionFacts,
) -> Vec<Plan> {
    let Some(callee) = context
        .expanded_callees
        .and_then(|callees| callees.get(&(HirLuauInliningBody::Identity, "".into())))
    else {
        return Vec::new();
    };
    context.proto.body.stmts.iter().enumerate().filter_map(|(index, stmt)| {
        if index <= callee.declaration { return None; }
        let HirStmt::CallStmt(stmt) = stmt else { return None; };
        let ([HirExpr::Binary(binary)], None) = (stmt.call.args.fixed.as_slice(), &stmt.call.args.tail) else { return None; };
        let literal = match binary.lhs {
            HirExpr::Boolean(_) | HirExpr::Integer(-32768..=32767) => binary.lhs.clone(),
            HirExpr::Number(value) if value.fract() == 0.0 && (-32768.0..=32767.0).contains(&value)
                && value.to_bits() != (-0.0f64).to_bits() => HirExpr::Integer(value as i64),
            _ => return None,
        };
        if !matches!(binary.rhs, HirExpr::Boolean(_) | HirExpr::Integer(_) | HirExpr::Number(_) | HirExpr::String(_)) {
            return None;
        }
        let call = &stmt.call;
        let frame = facts.native_fastcall_frame(call)?;
        if binary.op != crate::hir::common::HirBinaryOpKind::Eq
            || !matches!(frame.args, ValuePack::Fixed(pack) if pack.len == 1 && pack.start.index() == frame.home.slot() + 1)
            || frame.results != Some(ResultPack::Ignore) || !frame.arguments_unaliased
            || !call.fastcall.is_some_and(|protocol| protocol.fixed_is_direct(0) && !protocol.fixed_is_embedded_constant(0))
            || facts.comparison_result_temp(binary) != facts.call_argument_value(call, 0)
            || facts.comparison_result_temp(binary).is_none()
            || facts.boolean_argument_prewrite(call, 0).is_some()
        { return None; }
        let layout = facts.native_binary_layout(binary)?;
        if layout.lhs != Some(HomeSlotKey::new(frame.home.slot() + 2, 0)) || layout.rhs.is_some()
            || facts.comparison_operand_preparation(binary, 0, &binary.lhs).map(|(_, home)| home) != layout.lhs {
            return None;
        }
        let mut builder = frame_builder(context, &[], facts, DecompileDialect::Luau, frame.home.slot())?;
        if builder.expr(&call.callee, 0, frame.home.slot(), None, true, false, Some(frame.callee))? != call.callee
            || !context.callee_aliases.accepts(&call.callee) { return None; }
        let mut plan = Plan {
            start: index, sink: index, base: frame.home, values: vec![HirExpr::Call(Box::new(call.clone()))].into(),
            result_locals: Vec::new(), discarded_result: None, assignment_targets: Vec::new(),
            luau_compound_global: false, indexed_target: None, continuing_root: None,
            retained_copies: Vec::new(), replayed_effects: Vec::new(), removed: Vec::new(),
        };
        let HirExpr::Call(call) = &mut plan.values.fixed[0] else { return None; };
        let HirExpr::Binary(binary) = &mut call.args.fixed[0] else { return None; };
        binary.lhs = factories::factory_call(callee.local, Some(binary.source_site?), vec![literal].into());
        Some(plan)
    }).collect()
}

fn not_chain(expr: &HirExpr) -> (Vec<&HirUnaryExpr>, &HirExpr) {
    let mut chain = Vec::new();
    let mut value = expr;
    while let HirExpr::Unary(unary) = value {
        if unary.op != HirUnaryOpKind::Not {
            break;
        }
        chain.push(unary.as_ref());
        value = &unary.expr;
    }
    (chain, value)
}

struct BodyParts<'a> {
    local: Option<LocalId>,
    prefix: Vec<&'a HirUnaryExpr>,
    suffix: Vec<&'a HirUnaryExpr>,
    leaf: &'a HirExpr,
    call: &'a HirCallExpr,
}

fn body_parts<'a>(proto: &'a HirProto, facts: &ProtoPromotionFacts) -> Option<BodyParts<'a>> {
    let (last, updates) = proto.body.stmts.split_last()?;
    let HirStmt::Return(ret) = last else {
        return None;
    };
    let ([HirExpr::Call(call)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    let [argument] = call.args.fixed.as_slice() else {
        return None;
    };
    let (mut suffix, tail) = not_chain(argument);
    if updates.is_empty() {
        let split = suffix
            .iter()
            .take_while(|unary| facts.unary_result_home(unary) != Some(HomeSlotKey::new(1, 0)))
            .count();
        let prefix = suffix.split_off(split);
        Some(BodyParts {
            local: None,
            prefix,
            suffix,
            leaf: tail,
            call,
        })
    } else {
        let (local, prefix, leaf) = update_chain(updates)?;
        if *tail != HirExpr::LocalRef(local)
            || facts.trusted_local_home_slot(local) != Some(HomeSlotKey::new(1, 0))
        {
            return None;
        }
        Some(BodyParts {
            local: Some(local),
            prefix,
            suffix,
            leaf,
            call,
        })
    }
}

fn scalar_frame(
    call: &HirCallExpr,
    global: &crate::hir::common::HirGlobalRef,
    facts: &ProtoPromotionFacts,
) -> Option<crate::hir::promotion::NativeCallFrame> {
    if let Some(protocol) = call.fastcall {
        // pinned Luau 的 builtin 编号来自 Bytecode.h；同时核对原协议和 fallback 拼写，
        // 不能仅凭全局名把普通 CALL 升格为 FASTCALL。
        let builtin = match global.key.as_utf8()? {
            "type" => 40,
            "tostring" => 63,
            _ => return None,
        };
        if protocol.builtin() != builtin
            || !protocol.fixed_is_direct(0)
            || protocol.fixed_is_embedded_constant(0)
            || !facts.fastcall_argument_copies(call)?.is_empty()
        {
            return None;
        }
        facts.native_fastcall_frame(call)
    } else {
        facts.native_call_frame(call)
    }
}

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let BodyParts {
        prefix,
        suffix,
        leaf,
        call,
        ..
    } = body_parts(proto, facts)?;
    let HirExpr::GlobalRef(global) = &call.callee else {
        return None;
    };
    let frame = scalar_frame(call, global, facts)?;
    if prefix.len() < 2
        || suffix.is_empty()
        || prefix.len() + suffix.len() > 21
        || *leaf != HirExpr::ParamRef(proto.params[0])
        || frame.home != HomeSlotKey::new(2, 0)
        || !frame.arguments_unaliased
        || !matches!(frame.args, ValuePack::Fixed(range) if range.start.index() == 3 && range.len == 1)
        || !matches!(frame.results, Some(ResultPack::Fixed(range)) if range.start.index() == 2 && range.len == 1)
        || call.args.tail.is_some()
        || call.is_method()
        || global
            .key
            .as_utf8()
            .is_none_or(|name| name == "getfenv" || name == "setfenv")
    {
        return None;
    }
    let mut previous = None;
    for (index, unary) in prefix.iter().rev().enumerate() {
        let source = unary.source_site?;
        if !single_not_write(unary, facts, 1)
            || facts.unary_operand_home(unary) != Some(HomeSlotKey::new(usize::from(index != 0), 0))
            || previous.is_some_and(|previous| source.instr.index() != previous + 1)
        {
            return None;
        }
        previous = Some(source.instr.index());
    }
    let crate::hir::common::HirOperationSources::Single(lookup) = global.sources else {
        return None;
    };
    let argument_start = previous? + 1 + usize::from(call.fastcall.is_none());
    let expected_lookup = previous?
        + 1
        + if call.fastcall.is_some() {
            suffix.len()
        } else {
            0
        };
    if lookup.instr.index() != expected_lookup
        || facts.global_read_frame(global, DecompileDialect::Luau) != Some(frame.home)
        || !suffix_layout(&suffix, facts, 3, 1, argument_start)
        || call.source_site?.instr.index() != previous? + 2 + suffix.len()
    {
        return None;
    }
    Some((
        HirLuauInliningBody::ScalarNotCall {
            prefix: prefix.len(),
            suffix: suffix.len(),
            fastcall: call.fastcall.is_some(),
        },
        global.key.clone(),
    ))
}

/// 只展开同一 binding 的相邻 NOT 更新；保留每条原指令，事务写入不参与投影。
fn update_chain(stmts: &[HirStmt]) -> Option<(LocalId, Vec<&HirUnaryExpr>, &HirExpr)> {
    let (first, updates) = stmts.split_first()?;
    let HirStmt::LocalDecl(decl) = first else {
        return None;
    };
    if decl.initializer_merge_transaction.is_some() {
        return None;
    }
    let (local, initial) = scalar_local(first)?;
    let (mut chain, leaf) = not_chain(initial);
    chain.reverse();
    for stmt in updates {
        let HirStmt::Assign(assign) = stmt else {
            return None;
        };
        if assign.is_phi_transfer
            || assign.initializer_merge_transaction.is_some()
            || assign.generic_for_initializer_producer.is_some()
            || assign.generic_for_dispatch_release.is_some()
            || assign.method_rewrite_transaction.is_some()
        {
            return None;
        }
        let (written, value) = scalar_local(stmt)?;
        let (next, input) = not_chain(value);
        if written != local || next.is_empty() || *input != HirExpr::LocalRef(local) {
            return None;
        }
        chain.extend(next.into_iter().rev());
        if chain.len() > 21 {
            return None;
        }
    }
    chain.reverse();
    Some((local, chain, leaf))
}

fn suffix_layout(
    suffix: &[&HirUnaryExpr],
    facts: &ProtoPromotionFacts,
    result: usize,
    input: usize,
    start: usize,
) -> bool {
    suffix.iter().enumerate().all(|(index, unary)| {
        single_not_write(unary, facts, result + index)
            && facts.unary_operand_home(unary)
                == Some(HomeSlotKey::new(
                    if index + 1 == suffix.len() {
                        input
                    } else {
                        result + index + 1
                    },
                    0,
                ))
            && unary
                .source_site
                .is_some_and(|source| source.instr.index() == start + suffix.len() - index - 1)
    })
}

fn single_not_write(unary: &HirUnaryExpr, facts: &ProtoPromotionFacts, slot: usize) -> bool {
    let Some(source) = unary.source_site else {
        return false;
    };
    let Some(temp) = facts.operation_result_temp(source) else {
        return false;
    };
    facts.unary_result_home(unary) == Some(HomeSlotKey::new(slot, 0))
        && facts.operation_result_reference_unaliased(source)
        && facts
            .complete_temp_definition_write_homes(temp)
            .iter()
            .copied()
            .eq([HomeSlotKey::new(slot, 0)])
}

pub(super) fn result_home(facts: &ProtoPromotionFacts, call: &HirCallExpr) -> Option<HomeSlotKey> {
    let site = call.source_site?;
    let producer = facts.operation_result_temp(site)?;
    let result = facts.operation_result_home(site)?;
    let [copy] = facts.trusted_immediate_moves(producer)? else {
        return None;
    };
    (copy.source == Some(producer)
        && copy.source_home == result
        && copy.target_home.slot() + 2 == result.slot()
        && copy.target_home == HomeSlotKey::new(copy.target_home.slot(), 0)
        && result == HomeSlotKey::new(result.slot(), 0)
        && facts.operation_result_reference_unaliased(site)
        && facts
            .complete_temp_definition_write_homes(producer)
            .iter()
            .all(|home| *home == result || *home == copy.target_home))
    .then_some(copy.target_home)
}

/// 将复制到 caller 的 child 局部区间投影为未提交表达式；原 CALL 仍交给
/// FrameBuilder 证明，所有区间必须由同一批内联证书承接后才能发布。
pub(super) fn debug_updates(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
    callees: &Callees,
) -> Option<(HirProto, Vec<(crate::hir::HirSourceSite, LocalId)>)> {
    use crate::hir::simplify::walk::{HirRewritePass, rewrite_proto};
    if !callees.values().any(|callee| {
        matches!(callee.body, HirLuauInliningBody::ScalarNotCall { .. })
            && callee.result_name.is_some()
    }) {
        return None;
    }
    let mut reads = BTreeMap::<LocalId, usize>::new();
    let mut writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &proto.body.stmts,
        &mut (
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
    struct Draft<'a> {
        proto: &'a HirProto,
        facts: &'a ProtoPromotionFacts,
        callees: &'a Callees,
        reads: BTreeMap<LocalId, usize>,
        writes: BTreeMap<LocalId, usize>,
        obligations: Vec<(crate::hir::HirSourceSite, LocalId)>,
    }
    struct Candidate {
        updates: usize,
        sink: usize,
        argument_definition: Option<usize>,
        input: HirExpr,
        callee: LocalId,
    }
    impl Draft<'_> {
        fn candidate(&self, stmts: &[HirStmt]) -> Option<Candidate> {
            let (local, HirExpr::Boolean(_)) = scalar_local(stmts.first()?)? else {
                return None;
            };
            let name = self.proto.local_debug_hints[local.index()].as_ref()?;
            let scope_id = self.proto.local_debug_scopes[local.index()]?;
            let scope = self.proto.debug_scopes.get(scope_id)?.as_ref()?;
            let count = stmts
                .iter()
                .skip(1)
                .take(21)
                .take_while(|stmt| {
                    matches!(stmt, HirStmt::Assign(_))
                        && scalar_local(stmt).is_some_and(|(written, _)| written == local)
                })
                .count()
                + 1;
            let (_, prefix, leaf) = update_chain(&stmts[..count])?;
            // phi 空声明不求值，单用参数与 fallback callee 保留原位置；
            // 只跨过这些已识别准备，未消费语句仍由完整 FrameBuilder 验证。
            let mut sink = count;
            if matches!(stmts.get(sink), Some(HirStmt::LocalDecl(decl))
                if decl.bindings.len() == 1 && decl.values.is_empty()
                    && decl.initializer_merge_transaction.is_none())
            {
                sink += 1;
            }
            let argument_definition = if let Some((argument, value)) =
                scalar_local(stmts.get(sink)?)
                && matches!(value, HirExpr::Unary(_))
                && matches!(&stmts[sink], HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none())
                && self.proto.local_debug_hints[argument.index()].is_none()
                && self.proto.local_debug_scopes[argument.index()].is_none()
                && self.reads.get(&argument) == Some(&1)
                && self.writes.get(&argument) == Some(&1)
            {
                let index = sink;
                sink += 1;
                Some((index, argument, value))
            } else {
                None
            };
            let lookup = scalar_local(stmts.get(sink)?)
                .filter(|(_, value)| matches!(value, HirExpr::GlobalRef(_)));
            if lookup.is_some() {
                sink += 1;
            }
            let call = scalar_call(stmts.get(sink)?)?;
            let [argument] = call.args.fixed.as_slice() else {
                return None;
            };
            let argument = match argument_definition {
                Some((_, local, value)) if *argument == HirExpr::LocalRef(local) => value,
                None => argument,
                _ => return None,
            };
            let (suffix, tail) = not_chain(argument);
            let callee_value = match lookup {
                Some((local, value)) if call.callee == HirExpr::LocalRef(local) => value,
                None => &call.callee,
                _ => return None,
            };
            let HirExpr::GlobalRef(global) = callee_value else {
                return None;
            };
            let key = (
                HirLuauInliningBody::ScalarNotCall {
                    prefix: prefix.len() + 1,
                    suffix: suffix.len(),
                    fastcall: call.fastcall.is_some(),
                },
                global.key.clone(),
            );
            let callee = self.callees.get(&key)?;
            let initial = prefix.last()?.source_site?;
            let (initializer, home) = self.facts.operation_input_preparation(initial, leaf)?;
            let site = call.source_site?;
            if callee.result_name.as_ref() != Some(name)
                || *tail != HirExpr::LocalRef(local)
                || self.reads.get(&local) != Some(&count)
                || self.writes.get(&local) != Some(&count)
                || scope.initializer_temp != Some(initializer)
                || scope.initializer_end_instr?.index() + 1 != initial.instr.index()
                || scope.end_instr?.index() != site.instr.index() + 2
                || self.facts.trusted_local_home_slot(local) != Some(home)
                || !self
                    .facts
                    .complete_local_definition_write_homes(local)
                    .iter()
                    .copied()
                    .eq([home])
                || matches!(self.proto.inline_dispositions.local(local),
                    crate::hir::common::HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
            {
                return None;
            }
            let mut input = leaf.clone();
            // 先构造 prefix，再包 suffix，保持原 NOT 的求值次序。
            for unary in prefix.iter().rev().chain(suffix.iter().rev()) {
                let mut unary = (*unary).clone();
                unary.expr = input;
                input = HirExpr::Unary(Box::new(unary));
            }
            Some(Candidate {
                updates: count,
                sink,
                argument_definition: argument_definition.map(|(index, _, _)| index),
                input,
                callee: callee.local,
            })
        }
    }
    impl HirRewritePass for Draft<'_> {
        fn rewrite_block(&mut self, block: &mut HirBlock) -> bool {
            let mut removed = BTreeSet::new();
            let mut index = 0;
            while index < block.stmts.len() {
                if let Some(candidate) = self.candidate(&block.stmts[index..]) {
                    let sink = index + candidate.sink;
                    let call =
                        scalar_call_mut(&mut block.stmts[sink]).expect("validated scalar CALL");
                    self.obligations
                        .push((call.source_site.expect("validated CALL"), candidate.callee));
                    if let Some(argument) = candidate.argument_definition {
                        let HirStmt::LocalDecl(decl) = &mut block.stmts[index + argument] else {
                            unreachable!()
                        };
                        decl.values.fixed[0] = candidate.input;
                    } else {
                        call.args.fixed[0] = candidate.input;
                    }
                    removed.extend(index..index + candidate.updates);
                    index = sink + 1;
                } else {
                    index += 1;
                }
            }
            if removed.is_empty() {
                return false;
            }
            let mut index = 0;
            block.stmts.retain(|_| {
                let keep = !removed.contains(&index);
                index += 1;
                keep
            });
            true
        }
    }
    let mut pass = Draft {
        proto,
        facts,
        callees,
        reads,
        writes,
        obligations: Vec::new(),
    };
    let mut draft = proto.clone();
    rewrite_proto(&mut draft, &mut pass);
    (!pass.obligations.is_empty()).then_some((draft, pass.obligations))
}

fn scalar_call(stmt: &HirStmt) -> Option<&HirCallExpr> {
    let value = match stmt {
        HirStmt::If(branch) => &branch.cond,
        HirStmt::LocalDecl(_) | HirStmt::Assign(_) => scalar_local(stmt)?.1,
        HirStmt::CallStmt(stmt)
            if stmt.call.args.fixed.len() == 1 && stmt.call.args.tail.is_none() =>
        {
            &stmt.call.args.fixed[0]
        }
        _ => return None,
    };
    match value {
        HirExpr::Call(call) => Some(call),
        HirExpr::Binary(binary) => match &binary.lhs {
            HirExpr::Call(call) => Some(call),
            _ => None,
        },
        _ => None,
    }
}

fn scalar_call_mut(stmt: &mut HirStmt) -> Option<&mut HirCallExpr> {
    let value = match stmt {
        HirStmt::If(branch) => &mut branch.cond,
        HirStmt::LocalDecl(decl) => decl.values.fixed.first_mut()?,
        HirStmt::Assign(assign) => assign.values.fixed.first_mut()?,
        HirStmt::CallStmt(stmt) => stmt.call.args.fixed.first_mut()?,
        _ => return None,
    };
    match value {
        HirExpr::Call(call) => Some(call),
        HirExpr::Binary(binary) => match &mut binary.lhs {
            HirExpr::Call(call) => Some(call),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn preserve_updates(proto: &mut HirProto, facts: &mut ProtoPromotionFacts) {
    let BodyParts {
        local,
        prefix,
        suffix,
        leaf,
        call,
    } = body_parts(proto, facts).expect("certified scalar body");
    let prefix = prefix.into_iter().rev().cloned().collect::<Vec<_>>();
    let suffix = suffix.into_iter().rev().cloned().collect::<Vec<_>>();
    let mut input = leaf.clone();
    let mut call = call.clone();
    let local = local.unwrap_or_else(|| {
        let local = LocalId(proto.local_count);
        proto.local_count += 1;
        proto.local_debug_hints.push(None);
        proto.local_debug_scopes.push(None);
        facts.record_local_home_slot(local, HomeSlotKey::new(1, 0));
        // 原 home 1 的逐次更新归属于同一 binding；不是无来源的新 scratch。
        for unary in &prefix {
            let temp = facts
                .operation_result_temp(unary.source_site.expect("certified NOT"))
                .expect("certified NOT result");
            facts.record_temp_to_local_merge(temp, local);
            proto.inline_dispositions.promote_temp_to_local(temp, local);
        }
        local
    });
    let mut statements = Vec::with_capacity(prefix.len() + 1);
    for (index, mut unary) in prefix.into_iter().enumerate() {
        unary.expr = input;
        let values = vec![HirExpr::Unary(Box::new(unary))].into();
        if index == 0 {
            statements.push(HirStmt::LocalDecl(Box::new(HirLocalDecl {
                bindings: vec![local],
                values,
                initializer_merge_transaction: None,
            })));
        } else {
            statements.push(HirStmt::Assign(Box::new(HirAssign {
                luau_compound_global: false,
                upvalue_write_source: None,
                is_phi_transfer: false,
                parallel_nil_frame: None,
                targets: vec![HirLValue::Local(local)],
                values,
                initializer_merge_transaction: None,
                generic_for_initializer_producer: None,
                generic_for_dispatch_release: None,
                method_rewrite_transaction: None,
            })));
        }
        input = HirExpr::LocalRef(local);
    }
    for mut unary in suffix {
        unary.expr = input;
        input = HirExpr::Unary(Box::new(unary));
    }
    call.args.fixed[0] = input;
    let mut ret = proto.body.stmts.last().expect("certified return").clone();
    let HirStmt::Return(ret_value) = &mut ret else {
        unreachable!()
    };
    ret_value.values.fixed[0] = HirExpr::Call(Box::new(call));
    statements.push(ret);
    proto.body.stmts = statements;
    proto
        .inline_dispositions
        .preserve_local(local, HirInlineRetentionReason::PhysicalFramePrefix);
}

impl FrameBuilder<'_> {
    /// 只穿过原 CALL 后唯一的立即 COPY，不追任意别名链；两条写入与内联调用
    /// 在同一事件事务中退休，后缀验证仍负责保留高结果根。
    pub(in crate::hir::simplify::call_frames) fn scalar_copy_source(
        &self,
        local: LocalId,
        before: usize,
    ) -> Option<(&HirCallExpr, usize, usize)> {
        self.native?.expanded_callees?;
        let (copy_index, value) = self.scalar_definition(local, before)?;
        let (call_index, call) = match value {
            HirExpr::Call(call) => (copy_index, call.as_ref()),
            HirExpr::LocalRef(source) => {
                let (index, HirExpr::Call(call)) = self.scalar_definition(*source, copy_index)?
                else {
                    return None;
                };
                if self
                    .facts
                    .operation_result_temp(call.source_site?)
                    .and_then(|temp| self.facts.promoted_local_for_temp(temp))
                    != Some(*source)
                {
                    return None;
                }
                (index, call.as_ref())
            }
            _ => return None,
        };
        let producer = self.facts.operation_result_temp(call.source_site?)?;
        let [copy] = self.facts.trusted_immediate_moves(producer)? else {
            return None;
        };
        if self.facts.promoted_local_for_temp(copy.target) != Some(local)
            || self.expanded_scalar_home(call) != Some(copy.target_home)
        {
            return None;
        }
        Some((call, call_index, copy_index))
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_scalar_local(
        &mut self,
        local: LocalId,
        before: usize,
        slot: usize,
        original: Option<crate::hir::common::TempId>,
    ) -> Option<HirExpr> {
        let (call, call_index, copy_index) = self.scalar_copy_source(local, before)?;
        let producer = self.facts.operation_result_temp(call.source_site?)?;
        if self.expanded_scalar_home(call) != Some(HomeSlotKey::new(slot, 0))
            || original.is_some_and(|original| original != producer)
        {
            return None;
        }
        let call = call.clone();
        let restored = self.expanded_scalar_call(&call, call_index, slot)?;
        self.finish_event(call_index)?;
        if copy_index != call_index {
            self.finish_event(copy_index)?;
        }
        Some(HirExpr::Call(Box::new(restored)))
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_scalar_home(
        &self,
        call: &HirCallExpr,
    ) -> Option<HomeSlotKey> {
        self.native?.expanded_callees?;
        result_home(self.facts, call)
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_scalar_call(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirCallExpr> {
        // 独立 callee 和参数准备可能仍有未消费事件；失败后普通 CALL 路径
        // 必须看到原游标，不能继承本候选已经消费一半的准备区。
        let events = (self.first_event, self.next_event);
        let result = self.expanded_scalar_call_inner(call, before, slot);
        if result.is_none() {
            (self.first_event, self.next_event) = events;
        }
        result
    }

    fn expanded_scalar_call_inner(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirCallExpr> {
        let context = self.native?;
        let callees = context.expanded_callees?;
        let home = HomeSlotKey::new(slot, 0);
        if self.expanded_scalar_home(call) != Some(home) || context.closed.contains(&home) {
            return None;
        }
        let callee_definition = if let HirExpr::LocalRef(local) = &call.callee {
            Some(self.scalar_definition(*local, before)?)
        } else {
            None
        };
        let callee_value = callee_definition.map_or(&call.callee, |(_, value)| value);
        let HirExpr::GlobalRef(global) = callee_value else {
            return None;
        };
        let frame = scalar_frame(call, global, self.facts)?;
        if frame.home != HomeSlotKey::new(slot + 2, 0)
            || !frame.arguments_unaliased
            || call.is_method()
            || call.args.tail.is_some()
            || !matches!(frame.results, Some(ResultPack::Fixed(range)) if range.start.index() == slot + 2 && range.len == 1)
            || !matches!(frame.args, ValuePack::Fixed(range) if range.start.index() == slot + 3 && range.len == 1)
        {
            return None;
        }
        let [argument] = call.args.fixed.as_slice() else {
            return None;
        };
        let crate::hir::common::HirOperationSources::Single(lookup) = global.sources else {
            return None;
        };
        if self.facts.global_read_frame(global, DecompileDialect::Luau) != Some(frame.home) {
            return None;
        }
        let (mut chain, mut leaf) = not_chain(argument);
        let prefix_definition = if let HirExpr::LocalRef(local) = leaf {
            let (index, value) = self.scalar_definition(*local, before)?;
            let (prefix, value) = not_chain(value);
            let expected_home = prefix
                .first()
                .and_then(|unary| self.facts.unary_result_home(unary))
                .unwrap_or(HomeSlotKey::new(slot + 1, 0));
            if self.facts.trusted_local_home_slot(*local) != Some(expected_home) {
                return None;
            }
            chain.extend(prefix);
            leaf = value;
            Some(index)
        } else {
            None
        };
        let HirExpr::Boolean(value) = leaf else {
            return None;
        };
        let suffix_len = chain
            .iter()
            .take_while(|unary| {
                self.facts.unary_result_home(unary) != Some(HomeSlotKey::new(slot + 1, 0))
            })
            .count();
        let (suffix, prefix) = chain.split_at(suffix_len);
        let after_prefix = if call.fastcall.is_some() {
            lookup.instr.index().checked_sub(suffix.len())?
        } else {
            lookup.instr.index()
        };
        if prefix.is_empty()
            || !suffix_layout(
                suffix,
                self.facts,
                slot + 3,
                slot + 1,
                after_prefix + usize::from(call.fastcall.is_none()),
            )
            || call.source_site?.instr.index() != after_prefix + suffix.len() + 1
        {
            return None;
        }
        let body = HirLuauInliningBody::ScalarNotCall {
            prefix: prefix.len() + 1,
            suffix: suffix.len(),
            fastcall: call.fastcall.is_some(),
        };
        let callee = callees.get(&(body, global.key.clone()))?;
        if !self.facts.operation_result_reference_unaliased(lookup)
            || (slot..slot + 3 + suffix.len())
                .any(|slot| context.closed.contains(&HomeSlotKey::new(slot, 0)))
        {
            return None;
        }
        for (index, unary) in prefix.iter().enumerate() {
            if !single_not_write(unary, self.facts, slot + 1)
                || self.facts.unary_operand_home(unary) != Some(HomeSlotKey::new(slot + 1, 0))
                || unary.source_site?.instr.index() + index + 1 != after_prefix
            {
                return None;
            }
        }
        let initial = prefix.last()?.source_site?;
        let (_, initial_home) = self.facts.operation_input_preparation(initial, leaf)?;
        if initial_home != HomeSlotKey::new(slot + 1, 0)
            || callee.creation.proto != initial.proto
            || callee.creation.instr.index() >= initial.instr.index()
        {
            return None;
        }
        let mut restored = call.clone();
        restored.required_luau_inlining = call.source_site;
        prepare_invocation(callee, &mut restored, HirExpr::Boolean(!value));
        let mut definitions = prefix_definition
            .into_iter()
            .chain(callee_definition.map(|(index, _)| index))
            .collect::<Vec<_>>();
        definitions.sort_unstable();
        definitions.dedup();
        for index in definitions {
            self.finish_event(index)?;
        }
        Some(restored)
    }

    fn scalar_definition(&self, local: LocalId, before: usize) -> Option<(usize, &HirExpr)> {
        let context = self.native?;
        let index = self.definition(local, before)?;
        if index < self.next_event
            || context.proto.local_debug_hints[local.index()].is_some()
            || context.proto.local_debug_scopes[local.index()].is_some()
            || matches!(context.proto.inline_dispositions.local(local),
                crate::hir::common::HirInlineDisposition::Preserve(reasons)
                if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))
        {
            return None;
        }
        match self.run[index] {
            HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none() => {}
            HirStmt::Assign(assign)
                if !assign.is_phi_transfer
                    && assign.initializer_merge_transaction.is_none()
                    && assign.generic_for_initializer_producer.is_none()
                    && assign.generic_for_dispatch_release.is_none()
                    && assign.method_rewrite_transaction.is_none() => {}
            _ => return None,
        }
        Some((index, scalar_local(self.run[index])?.1))
    }
}
