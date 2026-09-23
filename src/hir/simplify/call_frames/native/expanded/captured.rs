//! 恢复写入捕获 cell 后返回算术值的 Luau 展开帧。
//!
//! 以捕获身份和原指令布局配对既存闭包；参数与调用帧须整体重放，保留更新顺序、
//! 返回宽度以及元方法可观察的引用存活时间。

use super::*;
use crate::hir::common::{HirBinaryExpr, HirBinaryOpKind, UpvalueId};

pub(super) fn body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if let Some(key) = identity_body_key(proto, facts) {
        return Some(key);
    }
    if proto.signature.is_vararg
        || proto.params.len() != 3
        || proto.upvalues.len() != 1
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Assign(assign), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Upvalue(upvalue)], [HirExpr::Binary(concat)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let ([HirExpr::Binary(sum)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    let HirExpr::Binary(first) = &sum.lhs else {
        return None;
    };
    let HirExpr::String(suffix) = &concat.rhs else {
        return None;
    };
    let source = concat.source_site?;
    let buffer = facts.native_concat_buffer(concat)?;
    let first_layout = facts.native_binary_layout(first)?;
    let sum_layout = facts.native_binary_layout(sum)?;
    let returned = facts.native_return_frame(ret)?;
    if *upvalue != UpvalueId(0)
        || source.instr.index() != 2
        || concat.op != HirBinaryOpKind::Concat
        || concat.lhs != HirExpr::UpvalueRef(*upvalue)
        || buffer.start.index() != 4
        || buffer.len != 2
        || facts.operation_result_home(source) != Some(HomeSlotKey::new(3, 0))
        || facts.operation_input_preparation(source, &concat.lhs)?.1 != HomeSlotKey::new(4, 0)
        || first.op != HirBinaryOpKind::Add
        || sum.op != HirBinaryOpKind::Add
        || first.lhs != HirExpr::ParamRef(proto.params[0])
        || first.rhs != HirExpr::ParamRef(proto.params[1])
        || sum.rhs != HirExpr::ParamRef(proto.params[2])
        || first.source_site?.instr.index() != source.instr.index() + 2
        || sum.source_site?.instr.index() != source.instr.index() + 3
        || facts.operation_result_home(first.source_site?) != Some(HomeSlotKey::new(4, 0))
        || facts.operation_result_home(sum.source_site?) != Some(HomeSlotKey::new(3, 0))
        || first_layout.lhs != Some(HomeSlotKey::new(0, 0))
        || first_layout.rhs != Some(HomeSlotKey::new(1, 0))
        || sum_layout.lhs != Some(HomeSlotKey::new(4, 0))
        || sum_layout.rhs != Some(HomeSlotKey::new(2, 0))
        || returned.home != HomeSlotKey::new(3, 0)
        || !matches!(returned.values, ValuePack::Fixed(range) if range.start.index() == 3 && range.len == 1)
    {
        return None;
    }
    Some((HirLuauInliningBody::CapturedConcatSum, suffix.clone()))
}

fn identity_body_key(
    proto: &HirProto,
    facts: &ProtoPromotionFacts,
) -> Option<(HirLuauInliningBody, crate::LuaString)> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || proto.upvalues.len() != 1
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Assign(assign), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Upvalue(upvalue)], [HirExpr::Binary(add)], None) = (
        assign.targets.as_slice(),
        assign.values.fixed.as_slice(),
        &assign.values.tail,
    ) else {
        return None;
    };
    let parameter = HirExpr::ParamRef(proto.params[0]);
    let layout = facts.native_binary_layout(add)?;
    let returned = facts.native_return_frame(ret)?;
    if *upvalue != UpvalueId(0)
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::UpvalueRef(*upvalue)
        || add.rhs != parameter
        || add.source_site?.instr.index() != 1
        || facts.operation_result_home(add.source_site?) != Some(HomeSlotKey::new(1, 0))
        || layout.lhs != Some(HomeSlotKey::new(2, 0))
        || layout.rhs != Some(HomeSlotKey::new(0, 0))
        || ret.values.fixed != [parameter]
        || ret.values.tail.is_some()
        || !matches!(returned.values, ValuePack::Fixed(range) if range.start.index() == 0 && range.len == 1)
    {
        return None;
    }
    Some((
        HirLuauInliningBody::CapturedAddIdentity,
        crate::LuaString::from(""),
    ))
}

impl FrameBuilder<'_> {
    pub(in crate::hir::simplify::call_frames) fn expanded_captured_argument(
        &mut self,
        call: &HirCallExpr,
        argument: usize,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let callee = context.expanded_callees?.get(&(
            HirLuauInliningBody::CapturedAddIdentity,
            crate::LuaString::from(""),
        ))?;
        if self.dialect != DecompileDialect::Luau {
            return None;
        }
        let arg = call.args.fixed.get(argument)?;
        let definition = match arg {
            HirExpr::LocalRef(local) => {
                if self
                    .facts
                    .promoted_local_for_temp(self.facts.call_argument_value(call, argument)?)
                    != Some(*local)
                    || context.proto.local_debug_hints[local.index()].is_some()
                    || context.proto.local_debug_scopes[local.index()].is_some()
                {
                    return None;
                }
                Some(self.definition(*local, before)?)
            }
            _ => None,
        };
        let value = definition.map_or(Some(arg), |index| {
            scalar_local(self.run[index]).map(|(_, value)| value)
        })?;
        if !matches!(value, HirExpr::Integer(value) if (0..=32767).contains(value)) {
            return None;
        }
        let prepared = self
            .facts
            .call_argument_preparation_instruction(call, argument, value)?;
        let preceding = if let Some(index) = definition {
            index
        } else if call.is_method() {
            let HirExpr::LocalRef(receiver) = call.args.fixed[0] else {
                return None;
            };
            self.definition(receiver, before)?
        } else {
            before
        };
        let update = preceding.checked_sub(1)?;
        let (target, HirExpr::Binary(add)) = scalar_local(self.run[update])? else {
            return None;
        };
        let source = add.source_site?;
        let home = self.facts.trusted_local_home_slot(target)?;
        let layout = self.facts.native_binary_layout(add)?;
        if !matches!(self.run[update], HirStmt::Assign(assign)
            if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
            || callee.capture != Some(target)
            || add.op != HirBinaryOpKind::Add
            || add.lhs != HirExpr::LocalRef(target)
            || !(add.rhs == *value
                || matches!((&add.rhs, value),
                (HirExpr::Number(number), HirExpr::Integer(integer)) if number.to_bits() == (*integer as f64).to_bits()))
            || source.proto != callee.creation.proto
            || source.instr.index() <= callee.creation.instr.index()
            || prepared.index() != source.instr.index() + 1
            || self.facts.call_argument_preparation(call, argument, value)
                != Some(HomeSlotKey::new(slot, 0))
            || self.facts.operation_result_home(source) != Some(home)
            || layout.lhs != Some(home)
            || layout.rhs.is_some()
            || home.slot() >= self.base
            || context.closed.contains(&HomeSlotKey::new(slot, 0))
            || context.barred.contains(&HomeSlotKey::new(slot, 0))
        {
            return None;
        }
        let mut restored = call.clone();
        prepare_invocation(callee, &mut restored, value.clone());
        restored.method = crate::hir::common::HirMethodCall::None;
        restored.required_luau_inlining = Some(source);
        // 原 ADD 与参数 LOADINT 是同一展开体；只在整个调用帧按原事件顺序消费时退休。
        let cursor = (self.first_event, self.next_event);
        if self.finish_event(update).is_none()
            || definition.is_some_and(|index| self.finish_event(index).is_none())
        {
            (self.first_event, self.next_event) = cursor;
            return None;
        }
        Some(HirExpr::Call(Box::new(restored)))
    }

    pub(in crate::hir::simplify::call_frames) fn expanded_captured_comparison(
        &mut self,
        binary: &HirBinaryExpr,
        before: usize,
        slot: usize,
    ) -> Option<HirExpr> {
        let context = self.native?;
        let callees = context.expanded_callees?;
        if binary.op != HirBinaryOpKind::Eq || self.dialect != DecompileDialect::Luau {
            return None;
        }
        let update = before.checked_sub(1)?;
        let (target, HirExpr::Binary(concat)) = scalar_local(self.run[update])? else {
            return None;
        };
        if !matches!(self.run[update], HirStmt::Assign(assign)
            if !assign.is_phi_transfer && assign.initializer_merge_transaction.is_none())
            || concat.op != HirBinaryOpKind::Concat
        {
            return None;
        }
        let HirExpr::String(suffix) = &concat.rhs else {
            return None;
        };
        let callee = callees.get(&(HirLuauInliningBody::CapturedConcatSum, suffix.clone()))?;
        let source = concat.source_site?;
        let comparison = binary.source_site?;
        let result = self.boolean_operand_start(slot);
        let buffer = self.facts.captured_concat_buffer(concat, target)?;
        let layout = self.facts.native_binary_layout(binary)?;
        if callee.capture != Some(target)
            || source.proto != callee.creation.proto
            || callee.creation.instr.index() >= source.instr.index()
            || buffer.start.index() != result + 1
            || buffer.len != 2
            || layout.lhs != Some(HomeSlotKey::new(result, 0))
            || (result..result + 3).any(|slot| {
                let home = HomeSlotKey::new(slot, 0);
                context.barred.contains(&home) || context.closed.contains(&home)
            })
        {
            return None;
        }
        let args = match &binary.lhs {
            HirExpr::Binary(sum) => {
                let HirExpr::Binary(first) = &sum.lhs else {
                    return None;
                };
                let first_layout = self.facts.native_binary_layout(first)?;
                let sum_layout = self.facts.native_binary_layout(sum)?;
                let input = self.direct_home(&first.lhs)?;
                if first.op != HirBinaryOpKind::Add
                    || sum.op != HirBinaryOpKind::Add
                    || first.source_site?.instr.index() != source.instr.index() + 1
                    || sum.source_site?.instr.index() != source.instr.index() + 2
                    || comparison.instr.index() != source.instr.index() + 3
                    || self.facts.operation_result_home(first.source_site?)
                        != Some(HomeSlotKey::new(result + 1, 0))
                    || self.facts.operation_result_home(sum.source_site?)
                        != Some(HomeSlotKey::new(result, 0))
                    || first_layout.lhs != Some(input)
                    || input.slot() >= self.base
                    || context.barred.contains(&input)
                    || first_layout.rhs.is_some()
                    || sum_layout.rhs.is_some()
                    || sum_layout.lhs != Some(HomeSlotKey::new(result + 1, 0))
                    || !matches!(first.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
                    || !matches!(sum.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
                    || self.direct_home(&binary.rhs) != layout.rhs
                    || layout.rhs.is_none_or(|home| home.slot() >= self.base)
                {
                    return None;
                }
                vec![first.lhs.clone(), first.rhs.clone(), sum.rhs.clone()]
            }
            HirExpr::Integer(value) if (0..=32767).contains(value) => {
                let (_, home) =
                    self.facts
                        .comparison_operand_preparation(binary, 0, &binary.lhs)?;
                if home != HomeSlotKey::new(result, 0)
                    || self
                        .facts
                        .comparison_preparation_instruction(binary, 0, &binary.lhs)?
                        .index()
                        != source.instr.index() + 1
                    || comparison.instr.index() != source.instr.index() + 2
                    || layout.rhs.is_some()
                    || !matches!(binary.rhs, HirExpr::Integer(_) | HirExpr::Number(_))
                {
                    return None;
                }
                // 原实参已被常量折叠。非负小整数 n+0+0 精确重发同一个 LOADINT，
                // 不宣称恢复原实参；强制内联使两个 ADD 不进入运行时字节码。
                vec![
                    HirExpr::Integer(*value),
                    HirExpr::Integer(0),
                    HirExpr::Integer(0),
                ]
            }
            _ => return None,
        };
        let call = HirCallExpr {
            source_site: None,
            required_luau_inlining: Some(source),
            argument_roots: Vec::new(),
            frame_root_ends: Vec::new(),
            callee: HirExpr::LocalRef(callee.local),
            args: args.into(),
            method: crate::hir::common::HirMethodCall::None,
            fastcall: None,
            method_key: None,
            callee_root_handoff: None,
            method_rewrite_transaction: None,
            plain_method_syntax: false,
            boolean_prewrite_arguments: Vec::new(),
        };
        let mut rebuilt = binary.clone();
        rebuilt.lhs = HirExpr::Call(Box::new(call));
        self.finish_event(update)?;
        Some(HirExpr::Binary(Box::new(rebuilt)))
    }
}
