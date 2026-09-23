//! 恢复同时捕获实参与外层参数的嵌套闭包工厂。
//!
//! 两个捕获值即使相等，也仍属于不同词法来源；恢复内层调用后，Luau 才会按原顺序
//! 重发各自的常量捕获准备。函数体改写只随完整 caller 帧的提交生效。

use super::*;
use crate::hir::common::{HirCapture, HirReturn, UpvalueId};

fn returned_closure(proto: &HirProto) -> Option<(&HirReturn, &HirClosureExpr)> {
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirExpr::Closure(closure)], None) = (ret.values.fixed.as_slice(), &ret.values.tail)
    else {
        return None;
    };
    Some((ret, closure))
}

fn value_capture(binding: HirBinding) -> HirCapture {
    HirCapture {
        mode: HirCaptureMode::ByValue,
        binding,
    }
}

pub(super) fn body(
    proto: &HirProto,
    promotion: &[ProtoPromotionFacts],
    protos: &[HirProto],
) -> Option<Factory> {
    if proto.signature.is_vararg
        || proto.params.len() != 1
        || !proto.upvalues.is_empty()
        || proto.children.len() != 2
        || proto.failure.is_some()
    {
        return None;
    }
    let [initial @ HirStmt::LocalDecl(_), HirStmt::Return(ret)] = proto.body.stmts.as_slice()
    else {
        return None;
    };
    let (inner, HirExpr::Closure(factory)) = scalar_local(initial)? else {
        return None;
    };
    let ([HirExpr::Closure(result)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    let (
        Some(HirClosureCreation::Fresh {
            template: intermediate,
        }),
        Some(HirClosureCreation::Fresh { template: output }),
    ) = (factory.creation, result.creation)
    else {
        return None;
    };
    let parameter = value_capture(HirBinding::Param(proto.params[0]));
    let facts = &promotion[proto.id.index()];
    if factory.captures.as_slice() != [parameter]
        || result.captures.as_slice() != [parameter, parameter]
        || facts.trusted_local_home_slot(inner) != Some(HomeSlotKey::new(1, 0))
        || facts.operation_result_home(factory.source_site?) != Some(HomeSlotKey::new(1, 0))
        || facts.operation_result_home(result.source_site?) != Some(HomeSlotKey::new(2, 0))
        || result.source_site?.instr.index() != factory.source_site?.instr.index() + 1
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(range) if range.start.index() == 2 && range.len == 1)
        || !value_result_body(&protos[result.proto.index()])
    {
        return None;
    }

    let child = &protos[factory.proto.index()];
    if child.signature.is_vararg
        || child.params.len() != 1
        || child.upvalues.len() != 1
        || child.children.len() != 1
        || !child.mutable_upvalues.is_empty()
        || child.failure.is_some()
    {
        return None;
    }
    let (child_return, leaf) = returned_closure(child)?;
    let child_facts = &promotion[child.id.index()];
    if leaf.creation != Some(HirClosureCreation::Fresh { template: output })
        || leaf.captures.as_slice()
            != [
                value_capture(HirBinding::Param(child.params[0])),
                HirCapture {
                    mode: HirCaptureMode::ByReference,
                    binding: HirBinding::Upvalue(UpvalueId(0)),
                },
            ]
        || !value_result_body(&protos[leaf.proto.index()])
        || child_facts.operation_result_home(leaf.source_site?) != Some(HomeSlotKey::new(1, 0))
        || !matches!(child_facts.native_return_frame(child_return)?.values, ValuePack::Fixed(range) if range.start.index() == 1 && range.len == 1)
    {
        return None;
    }
    Some(Factory::NestedValue {
        intermediate,
        result: output,
        inner,
    })
}

pub(super) fn plans(context: NativeFrameContext<'_>, facts: &ProtoPromotionFacts) -> Vec<Plan> {
    let mut reads = BTreeMap::<LocalId, usize>::new();
    let mut writes = BTreeMap::<LocalId, usize>::new();
    visit_stmts(
        &context.proto.body.stmts,
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
    // 候选拒绝[PolicyBoundary]：被消费的准备区不能仍有其它读写、debug 身份或已证明须保留的根。
    let input = |local: LocalId, home: HomeSlotKey, expected_reads: usize| {
        reads.get(&local).copied().unwrap_or(0) == expected_reads
            && writes.get(&local) == Some(&1)
            && context.proto.local_debug_hints[local.index()].is_none()
            && context.proto.local_debug_scopes[local.index()].is_none()
            && !context
                .proto
                .inline_dispositions
                .local(local)
                .must_preserve()
            && facts.trusted_local_home_slot(local) == Some(home)
            && facts
                .complete_local_definition_write_homes(local)
                .iter()
                .copied()
                .eq([home])
            && !context.closed.contains(&home)
    };
    let mut plans = Vec::new();
    for (start, window) in context.proto.body.stmts.windows(5).enumerate() {
        let candidate = (|| {
            let (first, value @ HirExpr::Integer(number)) = scalar_local(&window[0])? else {
                return None;
            };
            let (unused, HirExpr::Closure(intermediate)) = scalar_local(&window[1])? else {
                return None;
            };
            let (argument, second) = scalar_local(&window[2])?;
            let (capture, third) = scalar_local(&window[3])?;
            let (result, HirExpr::Closure(closure)) = scalar_local(&window[4])? else {
                return None;
            };
            let (
                Some(HirClosureCreation::Fresh {
                    template: inner_template,
                }),
                Some(HirClosureCreation::Fresh {
                    template: output_template,
                }),
            ) = (intermediate.creation, closure.creation)
            else {
                return None;
            };
            let callee = context.expanded_callees?.get(&(
                HirLuauInliningBody::NestedValueClosureFactory {
                    intermediate: inner_template,
                    result: output_template,
                },
                "".into(),
            ))?;
            let base = facts.trusted_local_home_slot(result)?;
            let first_home = HomeSlotKey::new(base.slot() + 2, 0);
            let inner_home = HomeSlotKey::new(base.slot() + 1, 0);
            let source = closure.source_site?;
            // 候选拒绝[ProofIncomplete]：模板相同还不足以恢复调用；捕获映射、连续原操作和完整槽写必须全部匹配。
            if !(-32768..=32767).contains(number) || second != value || third != value
                || callee.declaration >= start || callee.creation.proto != source.proto
                || !window.iter().all(|stmt| matches!(stmt, HirStmt::LocalDecl(decl) if decl.initializer_merge_transaction.is_none()))
                || !input(first, first_home, 1) || !input(argument, first_home, 1)
                || !input(capture, HomeSlotKey::new(base.slot() + 3, 0), 1)
                || !input(unused, inner_home, 0)
                || intermediate.captures.as_slice() != [value_capture(HirBinding::Local(first))]
                || closure.captures.as_slice() != [value_capture(HirBinding::Local(argument)), value_capture(HirBinding::Local(capture))]
                || facts.operation_result_home(intermediate.source_site?) != Some(inner_home)
                || facts.operation_result_home(source) != Some(base)
                || source.instr.index() != intermediate.source_site?.instr.index() + 3
                || context.closed.contains(&base)
            { return None; }
            let mut plan = invocation(callee, source, base, result, start, start + 4);
            let HirExpr::Call(call) = &mut plan.values.fixed[0] else {
                unreachable!()
            };
            call.args.fixed.push(value.clone());
            Some(plan)
        })();
        plans.extend(candidate);
    }
    plans
}

pub(in crate::hir::simplify::call_frames::native::expanded) fn restore_body(
    proto: &mut HirProto,
    inner: LocalId,
) {
    let parameter = proto.params[0];
    let [_, HirStmt::Return(ret)] = proto.body.stmts.as_mut_slice() else {
        unreachable!()
    };
    // 此调用与外层工厂同属一个编译合同；Generate 必须同时核对两层函数体与固定返回宽度。
    ret.values.fixed[0] = factory_call(inner, None, vec![HirExpr::ParamRef(parameter)].into());
    proto
        .inline_dispositions
        .preserve_local(inner, HirInlineRetentionReason::PhysicalFramePrefix);
}
