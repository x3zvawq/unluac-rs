//! 这个子模块负责把“构造器尾部立刻安装方法/字段函数”的模式收成更自然的函数 sugar。
//!
//! 它依赖前缀 local alias、可写 capture 快照和已经合法化的 AST，只吸收终端构造器链
//! 上的局部模式，不会在这里重写一般赋值语句。
//! 例如：
//! - `local t = {}; t.pick = function(...) end; return t`
//!   -> `local t = { pick = function(...) end }; return t`
//! - `local meta = {}; local methods = {}; function methods.bump(...) end; meta.__index = methods;
//!    local ctor = ffi.metatype("x", meta)`
//!   -> `local ctor = ffi.metatype("x", { __index = { bump = function(...) end } })`
//! - `local f=ctor; local t={}; return f(stable, t)`
//!   -> `return ctor(stable, {})`，其中 `stable` 必须是不受 initializer 回调影响的快照
//!
//! 这里不会去猜任意跨语句的数据流；只有“构造器 local -> 构造器字段接线”仍保持机械
//! 脚手架形状时，才会收回源码结构。非 plain 字段函数的语句自然终止连续前缀，不由本
//! pass 改写。

use std::collections::BTreeSet;

use super::super::binding_flow::{BindingUseIndex, MutableSnapshotNames, binding_mentions_in_stmt};
use super::super::binding_ref::{binding_from_name_ref, name_matches_binding};
use super::super::expr_analysis::is_stable_context_expr;
use super::super::installer_iife::function_expr_is_substantial;
use crate::ast::common::{
    AstAssign, AstBindingRef, AstCallKind, AstExpr, AstFieldAccess, AstFunctionExpr,
    AstFunctionName, AstLValue, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstReturn, AstStmt,
    AstTableField, AstTableKey,
};

pub(super) fn try_inline_terminal_constructor_fields(
    stmts: &[AstStmt],
) -> Option<(AstStmt, usize)> {
    let AstStmt::LocalDecl(local_decl) = stmts.first()? else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    let binding = local_decl.bindings[0].id;
    let AstExpr::TableConstructor(_) = &local_decl.values[0] else {
        return None;
    };

    let mut rewritten = local_decl.as_ref().clone();
    let AstExpr::TableConstructor(table) = &mut rewritten.values[0] else {
        unreachable!("matched constructor value above")
    };
    let mut consumed = 1usize;
    let (field, func) = inlineable_local_table_function_stmt(stmts.get(consumed)?, binding)?;
    if !table_can_append_record_field(table) {
        return None;
    }
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: AstTableKey::Name(field),
            value: AstExpr::FunctionExpr(Box::new(func)),
        }));
    consumed += 1;

    while let Some(stmt) = stmts.get(consumed) {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, binding) else {
            break;
        };
        table
            .fields
            .push(AstTableField::Record(crate::ast::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        consumed += 1;
    }

    Some((AstStmt::LocalDecl(Box::new(rewritten)), consumed))
}

pub(super) fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let callee = single_local_alias_decl(stmts.first()?)?;
    let mut consumed = 1usize;
    let mut arg_locals = Vec::<ConstructorArg>::new();

    while let Some(stmt) = stmts.get(consumed) {
        let Some(arg) = single_local_alias_decl(stmt) else {
            break;
        };
        arg_locals.push(ConstructorArg {
            binding: arg.binding,
            value: arg.value,
            pass_to_sink: true,
        });
        consumed += 1;
    }
    if arg_locals.is_empty() {
        return None;
    }

    while let Some(stmt) = stmts.get(consumed) {
        if inline_arg_local_table_function(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        if inline_nested_arg_local_table(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        break;
    }

    let sink = stmts.get(consumed)?;
    let rewritten_sink = rewrite_terminal_constructor_call_sink(
        sink,
        callee.binding.id,
        &callee.value,
        &arg_locals,
        mutable_snapshots,
    )?;

    // Removal-only gates intentionally run after the exact sink call has accepted the local
    // sequence. A standalone `<close>`/debug-root local is not a constructor-handoff candidate.
    if !constructor_local_can_be_removed(&callee.binding)
        || arg_locals
            .iter()
            .any(|arg| !constructor_local_can_be_removed(&arg.binding))
    {
        return None;
    }
    // This rule exists to remove constructor scaffolding, not to turn a readable named function
    // back into a multiline result-position IIFE. Short callees still benefit from the compact
    // terminal form.
    if let AstExpr::FunctionExpr(function) = &callee.value
        && function_expr_is_substantial(function)
    {
        // 候选拒绝[PolicyBoundary]：多语句/控制流 closure 内联到结果位置会制造难读 IIFE，语义上并非禁止。
        return None;
    }

    if use_index.count_uses_in_range(
        stmt_base + consumed,
        stmt_base + consumed + 1,
        callee.binding.id,
    ) != 1
        || arg_locals.iter().any(|arg| {
            use_index.count_uses_in_range(
                stmt_base + consumed,
                stmt_base + consumed + 1,
                arg.binding.id,
            ) != usize::from(arg.pass_to_sink)
        })
    {
        // 候选拒绝[SemanticBarrier:Scope]：sink 内除目标 call 外再读 callee/arg 时，删除声明会留下未绑定 use；每个 active handoff 必须恰好出现一次，已嵌套消费的 arg 必须为零次。
        return None;
    }
    let removed_bindings = std::iter::once(callee.binding.id)
        .chain(arg_locals.iter().map(|arg| arg.binding.id))
        .collect::<BTreeSet<_>>();
    if !binding_mentions_in_stmt(&rewritten_sink).is_disjoint(&removed_bindings) {
        // 候选拒绝[SemanticBarrier:Scope]：折叠后 sink 若仍直接或经字段闭包引用任一被删 binding，消除声明会留下未绑定引用；regress_362 是闭包捕获 arg 的具体反例。
        return None;
    }
    if !matches!(sink, AstStmt::Return(_))
        && !removed_constructor_locals_are_dead_after_sink(
            use_index,
            stmt_base + consumed + 1,
            callee.binding.id,
            &arg_locals,
        )
    {
        // 候选拒绝[SemanticBarrier:Scope]：非终端 sink 后若仍引用被消除的 callee/arg local，内联会留下未绑定 use。
        return None;
    }
    Some((rewritten_sink, consumed + 1))
}

#[derive(Clone)]
struct ConstructorArg {
    binding: AstLocalBinding,
    value: AstExpr,
    pass_to_sink: bool,
}

struct ConstructorLocal {
    binding: AstLocalBinding,
    value: AstExpr,
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<ConstructorLocal> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    Some(ConstructorLocal {
        binding: local_decl.bindings[0].clone(),
        value: local_decl.values[0].clone(),
    })
}

fn constructor_local_can_be_removed(binding: &AstLocalBinding) -> bool {
    match binding.attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：`local x <close>=acquire(); return ctor(x)`
            // 删除 alias 后不再在原 block 出口调用 x 的关闭动作。
            return false;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：`<const>` 的源码声明身份继续由声明 owner 保留。
            return false;
        }
    }
    if binding.origin.is_debug_hinted() {
        // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted alias 会抹掉调用期间 debug.getlocal 可见的名字与区间，反例见 regress_351。
        return false;
    }
    if binding.origin.is_physical_root() {
        // 候选拒绝[SemanticBarrier:Lifetime]：删除 PhysicalRoot 会让值在 sink 后、原 block 结束前提前离开 GC root，弱表/`__gc` 可观察，反例见 regress_353。
        return false;
    }
    true
}

fn inlineable_local_table_function_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    match stmt {
        AstStmt::Assign(assign) => inlineable_local_table_function_assign(assign, binding),
        AstStmt::FunctionDecl(function_decl) => {
            let AstFunctionName::Plain(path) = &function_decl.target else {
                return None;
            };
            if path.fields.len() != 1 || !name_matches_binding(&path.root, binding) {
                return None;
            }
            // 同 assign 分支：闭包捕获了 constructor binding 时不能折入
            if function_decl.func.captured_bindings.contains(&binding) {
                // 候选拒绝[SemanticBarrier:Capture]：`local obj={}; function obj.f() return obj end` 中 closure 原本捕获 local；折进 `local obj={f=function() return obj end}` 后该 local 尚未进入 initializer 作用域，引用会改绑外层名字。
                return None;
            }
            Some((path.fields[0].clone(), function_decl.func.clone()))
        }
        _ => None,
    }
}

fn inlineable_local_table_function_assign(
    assign: &AstAssign,
    binding: AstBindingRef,
) -> Option<(String, AstFunctionExpr)> {
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstFieldAccess { base, field } = access.as_ref();
    let AstExpr::Var(name) = base else {
        return None;
    };
    if !name_matches_binding(name, binding) {
        return None;
    }
    let AstExpr::FunctionExpr(function) = &assign.values[0] else {
        return None;
    };
    // 如果闭包体捕获了 constructor binding 自身（如 `obj.inc = function() obj.count = ... end`），
    // 折入 constructor initializer 后该 local 尚未进入词法作用域，闭包引用会改绑。
    if function.captured_bindings.contains(&binding) {
        // 候选拒绝[SemanticBarrier:Capture]：`local obj={}; obj.f=function() return obj end` 折叠后 closure 不再捕获同一个 local。
        return None;
    }
    Some((field.clone(), function.as_ref().clone()))
}

fn inline_arg_local_table_function(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    for arg_local in arg_locals {
        let AstExpr::TableConstructor(table) = &mut arg_local.value else {
            continue;
        };
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, arg_local.binding.id)
        else {
            continue;
        };
        if !table_can_append_record_field(table) {
            return false;
        }
        table
            .fields
            .push(AstTableField::Record(crate::ast::common::AstRecordField {
                key: AstTableKey::Name(field),
                value: AstExpr::FunctionExpr(Box::new(func)),
            }));
        return true;
    }
    false
}

fn inline_nested_arg_local_table(stmt: &AstStmt, arg_locals: &mut [ConstructorArg]) -> bool {
    let Some((outer_binding, field, inner_binding)) = inlineable_nested_table_assign(stmt) else {
        return false;
    };
    let Some(inner_index) = arg_locals
        .iter()
        .position(|arg| arg.binding.id == inner_binding)
    else {
        return false;
    };
    let Some(outer_index) = arg_locals
        .iter()
        .position(|arg| arg.binding.id == outer_binding)
    else {
        return false;
    };
    if !matches!(&arg_locals[inner_index].value, AstExpr::TableConstructor(_))
        || !matches!(&arg_locals[outer_index].value, AstExpr::TableConstructor(_))
    {
        return false;
    }
    if inner_index == outer_index || !arg_locals[inner_index].pass_to_sink {
        // 候选拒绝[SemanticBarrier:Identity]：`outer.self=outer` 原本保持自引用，克隆成嵌套字面量会产生另一个 table；同一 inner 接到两字段时再次克隆也会把共享身份拆成两个值。
        return false;
    }
    if outer_index + 1 != inner_index {
        // 只有声明顺序中紧邻的 `outer`、`inner` 接线属于本 pass 的 constructor
        // handoff 形状；反向或跨 initializer 的普通接线留给原语句表达。
        return false;
    }

    let inner_value = arg_locals[inner_index].value.clone();
    let AstExpr::TableConstructor(table) = &mut arg_locals[outer_index].value else {
        unreachable!("checked outer constructor above")
    };
    if !table_can_append_record_field(table) {
        return false;
    }

    // 这里专门收回“先建内层 methods table，再接到外层 metadata 字段”的机械接线。
    // 它只在内层 table 仍是独立 constructor local 时触发，不会把任意普通变量赋值猜成
    // 嵌套表字面量。
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: AstTableKey::Name(field),
            value: inner_value,
        }));
    arg_locals[inner_index].pass_to_sink = false;
    true
}

fn table_can_append_record_field(table: &crate::ast::common::AstTableConstructor) -> bool {
    // 候选拒绝[SemanticBarrier:ValueArity]：追加字段会让原末尾 open call/vararg 不再展开，具体反例见 regress_401。
    !matches!(
        table.fields.last(),
        Some(AstTableField::Array(
            AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
        ))
    )
}

fn inlineable_nested_table_assign(
    stmt: &AstStmt,
) -> Option<(AstBindingRef, String, AstBindingRef)> {
    let AstStmt::Assign(assign) = stmt else {
        return None;
    };
    if assign.targets.len() != 1 || assign.values.len() != 1 {
        return None;
    }
    let AstLValue::FieldAccess(access) = &assign.targets[0] else {
        return None;
    };
    let AstExpr::Var(outer_name) = &access.base else {
        return None;
    };
    let AstExpr::Var(inner_name) = &assign.values[0] else {
        return None;
    };
    Some((
        binding_from_name_ref(outer_name)?,
        access.field.clone(),
        binding_from_name_ref(inner_name)?,
    ))
}

fn rewrite_terminal_constructor_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::Return(ret) => {
            let mut rewritten: AstReturn = ret.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                ret.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::LocalDecl(local_decl) => {
            let mut rewritten: AstLocalDecl = local_decl.as_ref().clone();
            rewritten.values[0] = rewrite_terminal_constructor_call_expr(
                local_decl.values.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::CallStmt(call_stmt) => {
            let AstCallKind::Call(call) = &call_stmt.call else {
                return None;
            };
            let AstExpr::Call(call) = rewrite_terminal_constructor_call_expr(
                &AstExpr::Call(call.clone()),
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?
            else {
                unreachable!("terminal constructor helper preserves the outer call")
            };
            let mut rewritten = call_stmt.as_ref().clone();
            rewritten.call = AstCallKind::Call(call);
            // 候选接受[EvalOrderProof]：CallStmt 没有外层求值前缀，constructor initializer 仍在 callee/实参位置按原顺序执行一次。
            Some(AstStmt::CallStmt(Box::new(rewritten)))
        }
        AstStmt::If(if_stmt) => {
            let mut rewritten = if_stmt.as_ref().clone();
            rewritten.cond = rewrite_terminal_constructor_call_expr(
                &if_stmt.cond,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            // 候选接受[EvalOrderProof/ValueArityProof]：if 条件是一次性标量 owner，且没有先行运行时事件。
            Some(AstStmt::If(Box::new(rewritten)))
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut rewritten = numeric_for.as_ref().clone();
            rewritten.start = rewrite_terminal_constructor_call_expr(
                &numeric_for.start,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            // 候选接受[EvalOrderProof/ValueArityProof]：start 是 header 首个一次性标量事件，limit/step 顺序不动。
            Some(AstStmt::NumericFor(Box::new(rewritten)))
        }
        AstStmt::GenericFor(generic_for) => {
            let mut rewritten = generic_for.as_ref().clone();
            let first = rewrite_terminal_constructor_call_expr(
                generic_for.iterator.first()?,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            rewritten.iterator[0] = first;
            // 候选接受[EvalOrderProof/ValueArityProof]：首 iterator 无前缀；单项时保留 open pack，多项时前后都截成单值。
            Some(AstStmt::GenericFor(Box::new(rewritten)))
        }
        AstStmt::While(while_stmt) => {
            rewrite_terminal_constructor_call_expr(
                &while_stmt.cond,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            // 候选拒绝[SemanticBarrier:EvalCount]：`local f=make_f(); local a=make_a(); while f(a) do end` 中两个 initializer 原本各执行一次，搬入条件后会逐轮执行。
            None
        }
        AstStmt::Repeat(repeat_stmt) => {
            rewrite_terminal_constructor_call_expr(
                &repeat_stmt.cond,
                callee_binding,
                callee_expr,
                arg_locals,
                mutable_snapshots,
            )?;
            // 候选拒绝[SemanticBarrier:EvalCount]：`local f=make_f(); local a=make_a(); repeat until f(a)` 中两个 initializer 原本各执行一次，搬入条件后会逐轮执行。
            None
        }
        _ => None,
    }
}

fn rewrite_terminal_constructor_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    let active_args = arg_locals
        .iter()
        .filter(|arg| arg.pass_to_sink)
        .collect::<Vec<_>>();
    if !name_matches_binding(name, callee_binding) {
        return None;
    }

    // First recognize the complete handoff. Missing constructor locals are an ordinary
    // non-candidate; only a concrete reversal between two participating locals is an
    // observable ordering barrier.
    let positions = active_args
        .iter()
        .map(|expected| {
            call.args.iter().position(
                |arg| matches!(arg, AstExpr::Var(name) if name_matches_binding(name, expected.binding.id)),
            )
        })
        .collect::<Option<Vec<_>>>()?;
    if positions.windows(2).any(|pair| pair[0] >= pair[1]) {
        // 候选拒绝[SemanticBarrier:EvalOrder]：sink 以相反顺序承接两个 constructor local 时，内联会按实参顺序执行 initializer，反转原声明时的事件顺序。
        return None;
    }

    let mut expected_args = active_args.iter().copied().peekable();
    let mut rewritten_args = Vec::with_capacity(call.args.len());
    let mut last_arg_is_inlined_constructor = false;
    for arg in &call.args {
        if let Some(expected) = expected_args.peek()
            && matches!(arg, AstExpr::Var(name) if name_matches_binding(name, expected.binding.id))
        {
            rewritten_args.push(expected.value.clone());
            expected_args.next();
            last_arg_is_inlined_constructor = true;
            continue;
        }
        if expected_args.peek().is_some() && !is_stable_context_expr(arg, mutable_snapshots) {
            // 候选拒绝[SemanticBarrier:EvalOrder]：尚有 constructor handoff 时，额外实参会从其后移到其前；调用/lookup、global/upvalue 或可写 capture 的快照都可能被 initializer 改变，regress_423 的 prefix case 可观察到顺序反转。
            return None;
        }
        // 候选接受[EvalOrderProof]：无协议且不读取可写 capture/upvalue 的稳定表达式可安全
        // 位于待下沉 initializer 前；最后一个 handoff 之后的实参没有被任何 initializer
        // 跨越，可按原位保留任意表达式。
        rewritten_args.push(arg.clone());
        last_arg_is_inlined_constructor = false;
    }
    debug_assert!(expected_args.next().is_none());

    let mut rewritten = call.as_ref().clone();
    rewritten.callee = callee_expr.clone();
    rewritten.args = rewritten_args;
    if last_arg_is_inlined_constructor
        && let Some(last) = rewritten.args.last_mut()
        && matches!(
            last,
            AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
        )
    {
        // 候选接受[ValueArityProof]：constructor local 的 initializer 原本被单目标声明
        // 截成一个值；移到最终实参位置后必须显式保留该边界，不能恢复 open tail。
        let value = std::mem::replace(last, AstExpr::Nil);
        *last = AstExpr::SingleValue(Box::new(value));
    }
    Some(AstExpr::Call(Box::new(rewritten)))
}

fn removed_constructor_locals_are_dead_after_sink(
    use_index: &BindingUseIndex,
    suffix_start: usize,
    callee_binding: AstBindingRef,
    arg_locals: &[ConstructorArg],
) -> bool {
    if use_index.count_uses_in_suffix(suffix_start, callee_binding) != 0 {
        // 候选拒绝[SemanticBarrier:Scope]：callee local 在 sink 后仍有 use，不能随 constructor 壳一起删除。
        return false;
    }
    // 候选拒绝[SemanticBarrier:Scope]：任一 constructor arg local 在 sink 后仍有 use，都不能从词法作用域删除。
    arg_locals
        .iter()
        .all(|arg| use_index.count_uses_in_suffix(suffix_start, arg.binding.id) == 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{
        AstBlock, AstLocalBinding, AstLocalOrigin, AstNameRef, AstTableConstructor,
    };
    use crate::hir::{HirProtoRef, LocalId};

    fn function_value() -> AstExpr {
        AstExpr::FunctionExpr(Box::new(AstFunctionExpr {
            function: HirProtoRef(0),
            params: Vec::new(),
            is_vararg: false,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_names_by_upvalue: std::collections::BTreeMap::new(),
            capture_write_names: BTreeSet::new(),
        }))
    }

    #[test]
    fn field_folding_preserves_local_attributes() {
        for attr in [AstLocalAttr::Const, AstLocalAttr::Close] {
            let binding = AstBindingRef::Local(LocalId(0));
            let stmts = vec![
                AstStmt::LocalDecl(Box::new(AstLocalDecl {
                    bindings: vec![AstLocalBinding {
                        id: binding,
                        attr,
                        origin: AstLocalOrigin::Recovered,
                    }],
                    values: vec![AstExpr::TableConstructor(Box::new(AstTableConstructor {
                        fields: Vec::new(),
                    }))],
                })),
                AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(AstNameRef::Local(LocalId(0))),
                        field: "read".to_owned(),
                    }))],
                    values: vec![function_value()],
                })),
            ];

            let (AstStmt::LocalDecl(rewritten), consumed) =
                try_inline_terminal_constructor_fields(&stmts)
                    .expect("field folding keeps the declaration owner")
            else {
                panic!("field folding should keep a local declaration")
            };
            assert_eq!(consumed, 2);
            assert_eq!(rewritten.bindings[0].attr, attr);
        }
    }
}
