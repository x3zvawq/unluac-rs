//! 核对捕获表追加和 cell 交接的最终函数体及固定实参槽。
//! 只接受 HIR 已签证的捕获顺序、观察标签和返回值，不改变外围调用顺序。

use super::*;

pub(super) fn body(
    func: &AstFunctionExpr,
    proto: &crate::hir::HirProto,
    closure: &crate::hir::HirClosureExpr,
) -> bool {
    use crate::hir::{HirBinding, HirCaptureMode, UpvalueId};
    let Some((label, returned)) = crate::hir::luau_inlining::captured_transfers::template(proto)
    else {
        return false;
    };
    let [trace, target, source] = closure.captures.as_slice() else {
        return false;
    };
    let [
        HirBinding::Local(trace_local),
        HirBinding::Local(target_local),
        HirBinding::Local(source_local),
    ] = [trace.binding, target.binding, source.binding]
    else {
        return false;
    };
    if func.function != proto.id
        || closure.proto != proto.id
        || !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || trace.mode != HirCaptureMode::ByValue
        || source.mode != HirCaptureMode::ByValue
        || target.mode != HirCaptureMode::ByReference
        || func.captured_bindings
            != BTreeSet::from([
                AstBindingRef::Local(trace_local),
                AstBindingRef::Local(target_local),
                AstBindingRef::Local(source_local),
            ])
        || !func.captured_params.is_empty()
        || func.capture_write_names != BTreeSet::from([AstNameRef::Local(target_local)])
    {
        return false;
    }
    let [
        AstStmt::Assign(append),
        AstStmt::Assign(transfer),
        AstStmt::Return(ret),
    ] = func.body.stmts.as_slice()
    else {
        return false;
    };
    let ([AstLValue::IndexAccess(access)], [AstExpr::String(actual)]) =
        (append.targets.as_slice(), append.values.as_slice())
    else {
        return false;
    };
    let AstExpr::Binary(key) = &access.index else {
        return false;
    };
    let AstExpr::Unary(length) = &key.lhs else {
        return false;
    };
    // 封闭函数体没有参数、循环或子闭包，pinned CostModel 成本低于基础内联阈值。
    actual == label
        && access.base == AstExpr::Var(AstNameRef::Upvalue(UpvalueId(0)))
        && key.op == AstBinaryOpKind::Add
        && counter_repeat::integer(&key.rhs) == Some(1)
        && length.op == AstUnaryOpKind::Length
        && length.expr == access.base
        && transfer.targets == [AstLValue::Name(AstNameRef::Upvalue(UpvalueId(1)))]
        && transfer.values == [AstExpr::Var(AstNameRef::Upvalue(UpvalueId(2)))]
        && matches!(ret.values.as_slice(), [AstExpr::String(actual)] if actual == returned)
}

pub(super) fn slots(
    outer: &AstCallExpr,
    base: usize,
    occurrences: &BTreeMap<crate::hir::HirSourceSite, crate::hir::LocalId>,
    bodies: &BTreeMap<crate::hir::LocalId, HirLuauInliningBody>,
    slots: &BTreeMap<crate::hir::HirSourceSite, usize>,
    seen: &mut BTreeSet<crate::hir::HirSourceSite>,
) -> bool {
    for (argument, value) in outer.args.iter().enumerate() {
        let value = match value {
            AstExpr::SingleValue(inner) => inner.as_ref(),
            other => other,
        };
        let AstExpr::Call(call) = value else {
            continue;
        };
        let Some(site) = call.required_luau_inlining else {
            continue;
        };
        if matches!(
            occurrences.get(&site).and_then(|local| bodies.get(local)),
            Some(HirLuauInliningBody::CapturedAppendTransfer { .. })
        ) && (outer.method_key.is_some()
            || outer.required_luau_inlining.is_some()
            || slots.get(&site) != Some(&(base + argument + 1))
            || !seen.insert(site))
        {
            return false;
        }
    }
    true
}
