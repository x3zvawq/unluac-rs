//! 核对固定双结果展开调用的最终函数体及不透明捕获依赖。

use super::*;

pub(super) fn body(
    func: &AstFunctionExpr,
    label: &crate::LuaString,
    opaque: &opaque::Functions<'_>,
) -> bool {
    if !func.params.is_empty()
        || func.is_vararg
        || func.named_vararg.is_some()
        || !func.capture_write_names.is_empty()
        || !func.captured_params.is_empty()
    {
        return false;
    }
    let Some((AstStmt::Return(ret), prefix)) = func.body.stmts.split_last() else {
        return false;
    };
    let [AstExpr::String(actual_label), AstExpr::Call(last)] = ret.values.as_slice() else {
        return false;
    };
    if actual_label != label || !ordinary(last) || !last.args.is_empty() {
        return false;
    }
    let mut aliases = BTreeSet::new();
    let mut producer = false;
    for stmt in prefix {
        let AstStmt::LocalDecl(decl) = stmt else {
            return false;
        };
        let ([binding], [value]) = (decl.bindings.as_slice(), decl.values.as_slice()) else {
            return false;
        };
        let AstBindingRef::Local(local) = binding.id else {
            return false;
        };
        match value {
            AstExpr::Call(call) if !producer && producer_call(call, func, opaque) => {
                producer = true
            }
            AstExpr::Var(AstNameRef::Local(source)) if aliases.contains(source) => {}
            _ => return false,
        }
        aliases.insert(local);
    }
    // 至多一次 producer、两次 COPY、标签与零参结果调用：cost < 25，stack < 32。
    producer
        && prefix.len() <= 3
        && matches!(last.callee, AstExpr::Var(AstNameRef::Local(local)) if aliases.contains(&local))
}

fn ordinary(call: &AstCallExpr) -> bool {
    call.required_luau_inlining.is_none() && call.method_key.is_none()
}

fn captured_call(
    call: &AstCallExpr,
    func: &AstFunctionExpr,
    opaque: &opaque::Functions<'_>,
) -> bool {
    ordinary(call)
        && call.args.is_empty()
        && matches!(call.callee, AstExpr::Var(AstNameRef::Upvalue(upvalue)) if opaque.opaque_capture(func, upvalue))
}

fn producer_call(
    call: &AstCallExpr,
    func: &AstFunctionExpr,
    opaque: &opaque::Functions<'_>,
) -> bool {
    if let (AstExpr::FunctionExpr(identity), [AstExpr::SingleValue(argument)]) =
        (&call.callee, call.args.as_slice())
    {
        // 直接函数字面量在 tryCompileInlinedCall 中消失，保留原高槽形参及低槽 COPY。
        // 新闭包不得真正创建，也不能增加捕获；内层资源生产者仍保持普通 CALL。
        return call
            .required_luau_inlining
            .is_some_and(|site| site.proto == func.function)
            && call.method_key.is_none()
            && identity.creation.is_none()
            && identity.params.len() == 1
            && !identity.is_vararg
            && identity.named_vararg.is_none()
            && identity.captured_bindings.is_empty()
            && identity.captured_params.is_empty()
            && identity.capture_write_names.is_empty()
            && matches!(identity.body.stmts.as_slice(), [AstStmt::Return(ret)]
                if ret.values == [AstExpr::Var(AstNameRef::Param(identity.params[0]))])
            && matches!(argument.as_ref(), AstExpr::Call(inner) if captured_call(inner, func, opaque));
    }
    if captured_call(call, func, opaque) {
        return true;
    }
    let (AstExpr::IndexAccess(access), [argument]) = (&call.callee, call.args.as_slice()) else {
        return false;
    };
    // 括号保留非末尾参数的单结果宽度；索引调用不会被 Luau 解析为静态函数。
    let AstExpr::SingleValue(argument) = argument else {
        return false;
    };
    ordinary(call)
        && matches!(access.base, AstExpr::Var(AstNameRef::Upvalue(_)))
        && matches!(access.index, AstExpr::Integer(1..=256))
        && matches!(argument.as_ref(), AstExpr::Call(inner) if captured_call(inner, func, opaque))
}
