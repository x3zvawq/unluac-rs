//! 从原 NAMECALL、固定参数及立即结果 COPY 恢复 Luau 插值调用。
//!
//! 模板片段在完整帧内签发；后层仍把节点视为调用，不重新猜测原槽布局。

use super::*;
use crate::LuaString;
use crate::hir::common::{HirInlineDisposition, HirInlineRetentionReason, TempId};

impl FrameBuilder<'_> {
    fn interpolation_template(&self, call: &HirCallExpr, before: usize) -> Option<()> {
        if !call.is_method()
            || call.method_key.as_ref()?.as_bytes() != b"format"
            || call.args.tail.is_some()
        {
            return None;
        }
        let (receiver, _) = call.method_receiver()?;
        match receiver {
            HirExpr::String(_) => {}
            HirExpr::LocalRef(receiver) => {
                let index = self.definition(*receiver, before)?;
                match scalar_local(self.run[index])?.1 {
                    HirExpr::String(_) => {}
                    HirExpr::LocalRef(source) => {
                        let HirCallRootHandoff::MethodCallee(protocol) = call.callee_root_handoff?;
                        let original = self.facts.method_setup_protocol(protocol)?.receiver_temp?;
                        if self.facts.promoted_local_for_temp(original) != Some(*source)
                            || self
                                .facts
                                .call_argument_value(call, 0)
                                .and_then(|temp| self.facts.promoted_local_for_temp(temp))
                                != Some(*receiver)
                        {
                            return None;
                        }
                        // NAMECALL 的 SELF 副本可能保留为独立赋值；沿协议指定的原 receiver
                        // 找模板，不把该副本误当成动态模板，也不追踪任意别名链。
                        let source_index = self.definition(*source, index)?;
                        if !matches!(scalar_local(self.run[source_index])?.1, HirExpr::String(_)) {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
            HirExpr::TempRef(receiver) => {
                let index = *self.temp_definitions.get(receiver)?;
                if index >= before
                    || !matches!(self.run[index].scalar_temp_assignment(),
                        Some((temp, HirExpr::String(_))) if temp == *receiver)
                {
                    return None;
                }
            }
            _ => return None,
        }
        Some(())
    }

    /// 已树化的 CALL 仍可携带原低槽 COPY；使用消费点给出的目标 Def，不能仅凭槽距猜插值。
    pub(super) fn is_interpolation_copy(
        &self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
        producer: Option<TempId>,
    ) -> bool {
        let matched = || {
            if self.dialect != DecompileDialect::Luau || self.native.is_none() {
                return None;
            }
            self.interpolation_template(call, before)?;
            let result = self.facts.operation_result_temp(call.source_site?)?;
            let [copy] = self.facts.trusted_immediate_moves(result)? else {
                return None;
            };
            (producer == Some(copy.target)
                && copy.source == Some(result)
                && copy.target_home.slot() == slot
                && copy.source_home.slot()
                    == self.declaration_reserved_top.unwrap_or(0).max(slot + 1)
                && self.facts.trusted_temp_home_slot(result) == Some(copy.source_home)
                && self.facts.trusted_temp_home_slot(copy.target) == Some(copy.target_home)
                && self.facts.temp_definition_reference_unaliased(result)
                && self.facts.temp_definition_reference_unaliased(copy.target)
                && self
                    .facts
                    .complete_temp_definition_write_homes(result)
                    .iter()
                    .all(|home| *home == copy.source_home || *home == copy.target_home)
                && call.args.fixed.len() > usize::from(call.method == HirMethodCall::Explicit))
            .then_some(())
        };
        matched().is_some()
    }

    pub(super) fn interpolation_source(
        &self,
        local: LocalId,
        before: usize,
    ) -> Option<(&HirCallExpr, usize, usize, TempId)> {
        self.native?;
        if self.dialect != DecompileDialect::Luau {
            return None;
        }
        let copy_index = self.definition(local, before)?;
        let (_, value) = scalar_local(self.run[copy_index])?;
        let (call_index, call) = match value {
            HirExpr::Call(call) => (copy_index, call.as_ref()),
            HirExpr::LocalRef(source) => {
                let call_index = self.definition(*source, copy_index)?;
                let (_, HirExpr::Call(call)) = scalar_local(self.run[call_index])? else {
                    return None;
                };
                if copy_index != call_index + 1 {
                    return None;
                }
                (call_index, call.as_ref())
            }
            _ => return None,
        };
        self.interpolation_template(call, call_index)?;
        let result = self.facts.operation_result_temp(call.source_site?)?;
        let [copy] = self.facts.trusted_immediate_moves(result)? else {
            return None;
        };
        (copy.source == Some(result)
            && (self.facts.promoted_local_for_temp(copy.target) == Some(local)
                || call_index == copy_index
                    && self.facts.promoted_local_for_temp(result) == Some(local))
            && self.facts.trusted_temp_home_slot(result) == Some(copy.source_home)
            && self.facts.trusted_temp_home_slot(copy.target) == Some(copy.target_home)
            && copy.source_home.slot() > copy.target_home.slot())
        .then_some((call, call_index, copy_index, copy.target))
    }

    pub(super) fn interpolation_local(
        &mut self,
        local: LocalId,
        before: usize,
        slot: usize,
        original: Option<TempId>,
        retain_target: bool,
    ) -> Option<HirExpr> {
        let (call, call_index, copy_index, target) = self.interpolation_source(local, before)?;
        let result = self.facts.operation_result_temp(call.source_site?)?;
        let result_home = self.facts.trusted_temp_home_slot(result)?;
        let target_home = self.facts.trusted_temp_home_slot(target)?;
        let context = self.native?;
        let (owner, _) = scalar_local(self.run[call_index])?;
        if original.is_some_and(|original| original != target)
            || target_home.slot() != slot
            || result_home.slot() != self.declaration_reserved_top.unwrap_or(0).max(slot + 1)
            || !self.facts.temp_definition_reference_unaliased(target)
            || !self.facts.temp_definition_reference_unaliased(result)
            // COPY 已合入 CALL 声明时，当前身份属于原低槽目标；原结果可已退休，
            // 不能要求它仍独立映射。两语句尚分离时仍须核对高槽 CALL 自己的 owner。
            || !(self.facts.promoted_local_for_temp(result) == Some(owner)
                || call_index == copy_index
                    && self.facts.promoted_local_for_temp(target) == Some(owner))
            || self.facts.complete_temp_definition_write_homes(result).iter().any(|home| *home != result_home && *home != target_home)
            || [local, owner].iter().any(|binding|
                !(retain_target && *binding == local)
                && (context.proto.local_debug_hints[binding.index()].is_some()
                || context.proto.local_debug_scopes[binding.index()].is_some()
                || matches!(context.proto.inline_dispositions.local(*binding), HirInlineDisposition::Preserve(reasons)
                    if reasons.iter().any(|reason| *reason != HirInlineRetentionReason::PhysicalFramePrefix))))
        {
            // 候选拒绝[ProofIncomplete]：插值必须重发原结果 COPY；debug/capture 或额外保留义务不能由语法替换消费。
            return None;
        }
        let call = call.clone();
        let rebuilt = self.call(
            &call,
            call_index,
            result_home.slot(),
            false,
            CallWidth::Single,
        );
        let mut rebuilt = rebuilt?;
        let (HirExpr::String(template), _) = rebuilt.method_receiver()? else {
            return None;
        };
        let offset = usize::from(rebuilt.method == HirMethodCall::Explicit);
        let args = &rebuilt.args.fixed[offset..];
        // 候选拒绝[TargetConstraint]：编译器把字面量字符串插值折入模板，不能藉此删掉原参数准备。
        if args.iter().any(|arg| matches!(arg, HirExpr::String(_))) {
            return None;
        }
        rebuilt.interpolation = Some(segments(template, args.len())?);
        self.finish_event(call_index)?;
        if copy_index != call_index {
            self.finish_event(copy_index)?;
        }
        Some(HirExpr::Call(Box::new(rebuilt)))
    }

    /// 调用方已证明 prepared 槽的完整 CALL；新声明只重发其低槽 COPY，实参帧不变。
    pub(super) fn interpolation_initializer_call(
        &self,
        call: &HirCallExpr,
        local: LocalId,
        home: HomeSlotKey,
        prepared: HomeSlotKey,
    ) -> Option<HirCallExpr> {
        let result = self.facts.operation_result_temp(call.source_site?)?;
        let [copy] = self.facts.trusted_immediate_moves(result)? else {
            return None;
        };
        if copy.source != Some(result)
            || copy.target_home != home
            || copy.source_home != prepared
            || prepared.slot() != home.slot() + 1
            || self.facts.trusted_temp_home_slot(result) != Some(prepared)
            || self.facts.promoted_local_for_temp(copy.target) != Some(local)
            || !self.facts.temp_definition_reference_unaliased(result)
            || !self.facts.temp_definition_reference_unaliased(copy.target)
            || call.args.tail.is_some()
        {
            // 候选拒绝[ProofIncomplete]：恢复的声明必须是原固定单结果 COPY，不能改写开放 cell。
            return None;
        }
        let (HirExpr::String(template), key) = call.method_receiver()? else {
            return None;
        };
        let offset = usize::from(call.method == HirMethodCall::Explicit);
        let args = &call.args.fixed[offset..];
        if key.as_bytes() != b"format"
            || args.is_empty()
            || args.iter().any(|arg| matches!(arg, HirExpr::String(_)))
        {
            // 候选拒绝[TargetConstraint]：空插值或字符串参数会被编译器折叠，无法重发原 CALL。
            return None;
        }
        let mut source = call.clone();
        source.interpolation = Some(segments(template, args.len())?);
        Some(source)
    }

    pub(super) fn interpolation_call(
        &mut self,
        call: &HirCallExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirCallExpr> {
        let result = self.facts.operation_result_temp(call.source_site?)?;
        let [copy] = self.facts.trusted_immediate_moves(result)? else {
            return None;
        };
        let high = self.declaration_reserved_top.unwrap_or(0).max(slot + 1);
        if copy.target_home.slot() != slot || copy.source_home.slot() != high {
            return None;
        }
        let mut rebuilt = self.call(call, before, high, false, CallWidth::Single)?;
        rebuilt.interpolation = if call.interpolation.is_some() {
            call.interpolation.clone()
        } else {
            let (HirExpr::String(template), _) = rebuilt.method_receiver()? else {
                return None;
            };
            let offset = usize::from(rebuilt.method == HirMethodCall::Explicit);
            let args = &rebuilt.args.fixed[offset..];
            if args.iter().any(|arg| matches!(arg, HirExpr::String(_))) {
                // 候选拒绝[TargetConstraint]：字符串实参会折入模板，不能省掉原参数准备。
                return None;
            }
            Some(segments(template, args.len())?)
        };
        Some(rebuilt)
    }
}

/// 编译器只用 %% 表示字面量百分号、%* 表示单值插值；不接受其它 format 转换。
fn segments(template: &LuaString, arguments: usize) -> Option<Vec<LuaString>> {
    let mut chunks = Vec::new();
    let mut current = Vec::new();
    let mut bytes = template.as_bytes().iter().copied();
    while let Some(byte) = bytes.next() {
        if byte != b'%' {
            current.push(byte);
            continue;
        }
        match bytes.next()? {
            b'%' => current.push(b'%'),
            b'*' => chunks.push(template.derived_bytes(std::mem::take(&mut current))),
            _ => return None,
        }
    }
    chunks.push(template.derived_bytes(current));
    (chunks.len() == arguments + 1).then_some(chunks)
}
