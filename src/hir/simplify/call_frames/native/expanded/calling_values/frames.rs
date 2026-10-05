//! 在共享调用帧中消费嵌套调用的原参数 COPY 与结果预写。
//! 候选来自未发布草稿；只有外层观察帧完整退休这些事件后才能签发 occurrence。

use super::*;

pub(in crate::hir::simplify::call_frames) struct Frames<'a> {
    invocations: BTreeMap<crate::hir::HirSourceSite, &'a index::Invocation>,
    pairs: BTreeMap<crate::hir::HirSourceSite, &'a index::PairInvocation>,
    nil: BTreeMap<crate::hir::HirSourceSite, &'a index::NilInvocation>,
    shared: BTreeMap<crate::hir::HirSourceSite, &'a index::SharedInvocation>,
    observed: BTreeMap<crate::hir::HirSourceSite, &'a observed::Invocation>,
    anonymous: BTreeMap<crate::hir::HirSourceSite, &'a anonymous::Invocation>,
    original_nil: BTreeSet<LocalId>,
}

struct Collapsed<'a> {
    flag: HirExpr,
    flag_value: Option<TempId>,
    callee: &'a index::Function,
    reader: Option<&'a index::Function>,
    argument: pairs::ArgumentCopy,
    result: TempId,
}

impl<'a> Frames<'a> {
    pub(super) fn new(
        invocations: &'a [index::Invocation],
        pairs: &'a [index::PairInvocation],
        nil: &'a [index::NilInvocation],
        shared: &'a [index::SharedInvocation],
        observed: &'a [observed::Invocation],
        anonymous: &'a [anonymous::Invocation],
        facts: &ProtoPromotionFacts,
    ) -> Self {
        Self {
            anonymous: anonymous
                .iter()
                .map(|invocation| (invocation.source, invocation))
                .collect(),
            observed: observed
                .iter()
                .map(|invocation| (invocation.candidate.source, invocation))
                .collect(),
            shared: shared
                .iter()
                .map(|invocation| (invocation.candidate.source, invocation))
                .collect(),
            nil: nil
                .iter()
                .map(|invocation| (invocation.candidate.source, invocation))
                .collect(),
            pairs: pairs
                .iter()
                .map(|invocation| (invocation.candidate.source, invocation))
                .collect(),
            invocations: invocations
                .iter()
                .map(|invocation| (invocation.candidate.source, invocation))
                .collect(),
            original_nil: facts
                .nil_write_groups()
                .flat_map(|group| {
                    group
                        .iter()
                        .filter_map(|temp| facts.promoted_local_for_temp(*temp))
                })
                .collect(),
        }
    }

    pub(in crate::hir::simplify::call_frames::native::expanded) fn dependency(
        &self,
        source: crate::hir::HirSourceSite,
    ) -> Option<crate::hir::common::HirLuauCallableArgument> {
        if let Some(invocation) = self.anonymous.get(&source) {
            let reader = &invocation.reader;
            return Some(crate::hir::HirLuauCallableArgument {
                parameter: 2,
                source: crate::hir::HirLuauCallableSource::Expression {
                    site: reader.source_site?,
                    creation: reader.creation?,
                },
                child: reader.proto,
                captures: reader.captures.clone(),
                pair_constant: None,
            });
        }
        let reader = self
            .invocations
            .get(&source)
            .map(|invocation| &invocation.reader)
            .or_else(|| {
                self.observed
                    .get(&source)
                    .map(|invocation| &invocation.reader)
            })
            .or_else(|| self.pairs.get(&source).map(|invocation| &invocation.reader))
            .or_else(|| {
                self.shared
                    .get(&source)
                    .map(|invocation| &invocation.reader)
            })
            .or_else(|| {
                self.nil
                    .get(&source)
                    .and_then(|invocation| invocation.reader.as_ref())
            })?;
        Some(crate::hir::common::HirLuauCallableArgument {
            parameter: 2,
            source: crate::hir::HirLuauCallableSource::Declared(reader.local),
            child: reader.child,
            captures: reader.captures.clone(),
            pair_constant: self
                .pairs
                .get(&source)
                .filter(|invocation| invocation.candidate.argument.is_none())
                .and_then(|invocation| crate::hir::luau_inlining::small_integer(&invocation.value)),
        })
    }

    pub(in crate::hir::simplify::call_frames::native::expanded) fn nil_guard(
        &self,
        source: crate::hir::HirSourceSite,
    ) -> bool {
        self.nil.contains_key(&source)
    }

    pub(in crate::hir::simplify::call_frames::native::expanded) fn result(
        &self,
        source: crate::hir::HirSourceSite,
    ) -> Option<TempId> {
        if let Some(invocation) = self.anonymous.get(&source) {
            return Some(invocation.result);
        }
        self.invocations
            .get(&source)
            .map(|invocation| invocation.candidate.result)
            .or_else(|| {
                self.observed
                    .get(&source)
                    .map(|invocation| invocation.candidate.result)
            })
            .or_else(|| {
                self.pairs
                    .get(&source)
                    .map(|invocation| invocation.candidate.result_values[0])
            })
            .or_else(|| {
                self.nil
                    .get(&source)
                    .map(|invocation| invocation.candidate.result)
            })
            .or_else(|| {
                self.shared
                    .get(&source)
                    .map(|invocation| invocation.candidate.result)
            })
    }

    fn collapsed_invocation(&self, call: &HirCallExpr) -> Option<Collapsed<'_>> {
        let source = call.required_luau_inlining?;
        let invocation = self
            .nil
            .get(&source)
            .map(|invocation| {
                let candidate = &invocation.candidate;
                Collapsed {
                    flag: HirExpr::Nil,
                    flag_value: None,
                    callee: &invocation.callee,
                    reader: invocation.reader.as_ref(),
                    result: candidate.result,
                    argument: pairs::ArgumentCopy {
                        body_pc: candidate.source_pc,
                        local: candidate.value,
                        input: candidate.value_input,
                        source: candidate.value_source,
                    },
                }
            })
            .or_else(|| {
                self.shared.get(&source).map(|invocation| Collapsed {
                    flag: invocation.candidate.flag(),
                    flag_value: invocation
                        .candidate
                        .live
                        .as_ref()
                        .map(|value| value.flag_value),
                    callee: &invocation.callee,
                    reader: Some(&invocation.reader),
                    result: invocation.candidate.result,
                    argument: invocation.candidate.argument,
                })
            })?;
        (call.source_site.is_none()
            && call.callee == HirExpr::LocalRef(invocation.callee.local)
            && !call.is_method()
            && call.fastcall.is_none()
            && call.args.tail.is_none())
        .then_some(invocation)
    }

    fn invocation(&self, call: &HirCallExpr) -> Option<&index::Invocation> {
        let invocation = self.invocations.get(&call.required_luau_inlining?)?;
        (call.source_site.is_none()
            && call.callee == HirExpr::LocalRef(invocation.callee.local)
            && !call.is_method()
            && call.fastcall.is_none()
            && call.args.tail.is_none())
        .then_some(*invocation)
    }

    fn observed_invocation(&self, call: &HirCallExpr) -> Option<&observed::Invocation> {
        let invocation = self.observed.get(&call.required_luau_inlining?)?;
        (call.source_site.is_none()
            && call.callee == HirExpr::LocalRef(invocation.callee.local)
            && !call.is_method()
            && call.fastcall.is_none()
            && call.args.tail.is_none())
        .then_some(*invocation)
    }

    /// 草稿中的原返回 COPY 仍属于紧邻的完整调用，不先作为独立低槽赋值提交。
    pub(in crate::hir::simplify::call_frames) fn observed_prewrite(
        &self,
        stmt: &HirStmt,
        next: &HirStmt,
        after: Option<&HirStmt>,
    ) -> bool {
        let matched = (|| {
            let (call, empty) = match next {
                HirStmt::LocalDecl(decl) if decl.values.is_empty() => {
                    (shared::call(after?)?, Some(decl))
                }
                _ => (shared::call(next)?, None),
            };
            let invocation = self.observed_invocation(call)?;
            let candidate = &invocation.candidate;
            (pairs::scalar_write(stmt)
                && scalar_local(stmt)
                    == Some((candidate.initial, &HirExpr::LocalRef(candidate.flag)))
                && empty.is_none_or(|decl| {
                    decl.bindings == [candidate.local]
                        && decl.initializer_merge_transaction.is_none()
                        && decl.generic_for_initializer_producer.is_none()
                }))
            .then_some(())
        })();
        matched.is_some()
    }
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn calling_value_result(
        &self,
        call: &HirCallExpr,
    ) -> Option<TempId> {
        if let Some(invocation) = self.native?.calling_values?.observed_invocation(call) {
            return Some(invocation.candidate.result);
        }
        if let Some(invocation) = self.native?.calling_values?.collapsed_invocation(call) {
            return Some(invocation.result);
        }
        Some(
            self.native?
                .calling_values?
                .invocation(call)?
                .candidate
                .result,
        )
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_calling_value(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        producer: Option<TempId>,
    ) -> Option<HirCallExpr> {
        let context = self.native?;
        if let Some(invocation) = context.calling_values?.observed_invocation(call) {
            return observed::expand(
                self,
                call,
                before,
                slot,
                producer,
                invocation,
                &context.calling_values?.original_nil,
            );
        }
        if let Some(invocation) = context.calling_values?.collapsed_invocation(call) {
            let argument = invocation.argument;
            let home = self.facts.trusted_temp_home_slot(invocation.result)?;
            let source = self.facts.promoted_local_for_temp(argument.source)?;
            let value_write = self.definition(argument.local, before)?;
            if let Some(value) = invocation.flag_value {
                let HirExpr::LocalRef(local) = invocation.flag else {
                    return None;
                };
                if self.facts.promoted_local_for_temp(value) != Some(local)
                    || self.facts.trusted_temp_home_slot(value)
                        != self.facts.trusted_local_home_slot(local)
                {
                    return None;
                }
            }
            // 候选拒绝[ProofIncomplete:CallFrame]：原操作证据不能替代当前草稿的
            // COPY、结果 home 和实参身份；未清除的 debug 声明仍有独立归属。
            if producer != Some(invocation.result)
                || home.slot() != slot
                || context.barred.contains(&home)
                || context.closed.contains(&home)
                || value_write + 1 != before
                || !self.homes_match(
                    argument.local,
                    value_write,
                    slot + 1,
                    None,
                    Some(argument.input),
                )
                || context.proto.local_debug_hints[argument.local.index()].is_some()
                || context.proto.local_debug_scopes[argument.local.index()].is_some()
                || self.facts.trusted_local_home_slot(source)
                    != self.facts.trusted_temp_home_slot(argument.source)
                || scalar_local(self.run[value_write])
                    != Some((argument.local, &HirExpr::LocalRef(source)))
                || call.args.fixed.as_slice()
                    != [
                        invocation.flag,
                        HirExpr::LocalRef(argument.local),
                        invocation
                            .reader
                            .as_ref()
                            .map_or(HirExpr::Nil, |reader| HirExpr::LocalRef(reader.local)),
                    ]
            {
                return None;
            }
            self.finish_event(value_write)?;
            let mut rebuilt = call.clone();
            rebuilt.args.fixed[1] = HirExpr::LocalRef(source);
            return Some(rebuilt);
        }
        let invocation = context.calling_values?.invocation(call)?;
        let candidate = &invocation.candidate;
        let result_home = self.facts.trusted_temp_home_slot(candidate.result)?;
        let initial = self.facts.promoted_local_for_temp(candidate.initial)?;
        let source = self.facts.promoted_local_for_temp(candidate.value_source)?;
        let initial_write = self.definition(initial, before)?;
        let value_write = self.definition(candidate.value, initial_write)?;
        let frame = self.facts.branch_value_frame_at(candidate.predicate)?;
        let result = frame
            .results
            .iter()
            .chain(frame.edge_results(self.facts))
            .find(|result| result.value == candidate.result)?;
        let initial_value = result
            .incoming
            .iter()
            .find(|input| input.value == candidate.initial)?;
        let (HirBinding::Temp(flag), flag_home) = initial_value.copy? else {
            return None;
        };
        let flag = self.facts.promoted_local_for_temp(flag)?;
        if producer != Some(candidate.result)
            || result_home != HomeSlotKey::new(slot, 0)
            || context.barred.contains(&result_home)
            || context.closed.contains(&result_home)
            || flag_home.slot() >= slot
            || self.facts.trusted_local_home_slot(flag) != Some(flag_home)
            || self.facts.trusted_local_home_slot(source)
                != self.facts.trusted_temp_home_slot(candidate.value_source)
            || !self.homes_match(
                candidate.value,
                value_write,
                slot + 1,
                None,
                Some(candidate.value_input),
            )
            || !self.homes_match(initial, initial_write, slot, None, Some(candidate.initial))
            || context.proto.local_debug_hints[candidate.value.index()].is_some()
            || context.proto.local_debug_scopes[candidate.value.index()].is_some()
            || context.proto.local_debug_hints[initial.index()].is_some()
            || context.proto.local_debug_scopes[initial.index()].is_some()
            || scalar_local(self.run[value_write])
                != Some((candidate.value, &HirExpr::LocalRef(source)))
            || scalar_local(self.run[initial_write]) != Some((initial, &HirExpr::LocalRef(flag)))
            || call.args.fixed.as_slice()
                != [
                    HirExpr::LocalRef(flag),
                    HirExpr::LocalRef(candidate.value),
                    HirExpr::LocalRef(invocation.reader.local),
                ]
        {
            return None;
        }
        let empty_result = if initial_write + 1 == before {
            None
        } else {
            let [HirStmt::LocalDecl(decl)] = &self.run[initial_write + 1..before] else {
                return None;
            };
            let result = self.facts.promoted_local_for_temp(candidate.result)?;
            if decl.bindings != [result]
                || !decl.values.is_empty()
                || decl.initializer_merge_transaction.is_some()
                || decl.generic_for_initializer_producer.is_some()
                || !self.facts.is_phi_carrier_temp(candidate.result)
                || context.calling_values?.original_nil.contains(&result)
                || context.proto.local_debug_hints[result.index()].is_some()
                || context.proto.local_debug_scopes[result.index()].is_some()
            {
                return None;
            }
            Some(initial_write + 1)
        };
        // 原 value COPY 先于短路结果预写；独立 phi 只有无原 LOADNIL 的空声明可一并退休。
        self.finish_event(value_write)?;
        self.finish_event(initial_write)?;
        if let Some(empty) = empty_result {
            self.finish_event(empty)?;
        }
        let mut rebuilt = call.clone();
        rebuilt.args.fixed[1] = HirExpr::LocalRef(source);
        Some(rebuilt)
    }
}
