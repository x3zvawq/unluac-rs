//! 将构造器尾部连续安装的方法/字段函数收回函数 sugar。
//!
//! 消费合法 AST、前缀 alias 与可写 capture 快照，只处理终端构造器的连续接线，
//! 不推断任意跨语句数据流。
//! 例如 local t={}; t.pick=function(...) end; return t 在证明成立时可收成
//! local t={pick=function(...) end}; return t。

use std::collections::{BTreeMap, BTreeSet};

use super::super::binding_flow::{BindingUseIndex, MutableSnapshotNames, binding_mentions_in_stmt};
use super::super::expr_analysis::is_stable_context_expr;
use super::super::installer_iife::function_expr_is_substantial;
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstExpr, AstFunctionExpr, AstFunctionName, AstLValue,
    AstLocalAttr, AstLocalBinding, AstLocalDecl, AstReturn, AstStmt, AstTableField,
};

/// 当前 block 的连续单声明段边界及潜在终端 callee，不提供字段接线或删除许可。
/// 所有 owner 只消费原数组前缀，未消费后缀不变；下一次 block 改写重新发布。
pub(super) struct ConstructorRunFacts {
    starts: Vec<Option<(usize, AstBindingRef)>>,
}

impl ConstructorRunFacts {
    pub(super) fn for_stmts(stmts: &[AstStmt]) -> Self {
        let mut starts = vec![None; stmts.len()];
        let mut index = 0;
        while index < stmts.len() {
            if single_local_alias_decl(&stmts[index]).is_none() {
                index += 1;
                continue;
            }
            let begin = index;
            while index < stmts.len() && single_local_alias_decl(&stmts[index]).is_some() {
                index += 1;
            }
            let end = index;
            let mut sink = end;
            // 接线只会消费这两类，且它们不能充当 constructor sink。中途接线失败
            // 仍由原验证拒绝；这里越过它们仅寻找成功候选必需的终端，不授权接线。
            while matches!(
                stmts.get(sink),
                Some(AstStmt::Assign(_) | AstStmt::FunctionDecl(_))
            ) {
                sink += 1;
            }
            if let Some(call) = stmts.get(sink).and_then(terminal_constructor_call)
                && let AstExpr::Var(name) = &call.callee
                && let Some(callee) = AstBindingRef::from_name_ref(name)
            {
                starts[begin..end].fill(Some((end, callee)));
            }
        }
        Self { starts }
    }

    fn declaration_end(&self, index: usize, binding: AstBindingRef) -> Option<usize> {
        let (end, callee) = self.starts[index]?;
        (callee == binding).then_some(end)
    }
}

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
    if !table_can_append_record_field(table, field) {
        return None;
    }
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: crate::ast::table_layout::record_key(&table.allocation, field.to_owned()),
            value: AstExpr::FunctionExpr(Box::new(func.clone())),
        }));
    consumed += 1;

    while let Some(stmt) = stmts.get(consumed) {
        let Some((field, func)) = inlineable_local_table_function_stmt(stmt, binding) else {
            break;
        };
        if !table_can_append_record_field(table, field) {
            break;
        }
        table
            .fields
            .push(AstTableField::Record(crate::ast::AstRecordField {
                key: crate::ast::table_layout::record_key(&table.allocation, field.to_owned()),
                value: AstExpr::FunctionExpr(Box::new(func.clone())),
            }));
        consumed += 1;
    }

    if !crate::ast::table_layout::matches_preallocation(table) {
        return None;
    }
    Some((AstStmt::LocalDecl(Box::new(rewritten)), consumed))
}

pub(super) fn try_inline_terminal_constructor_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    run_facts: &ConstructorRunFacts,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let callee = single_local_alias_decl(stmts.first()?)?;
    let mut consumed = run_facts.declaration_end(stmt_base, callee.binding.id)? - stmt_base;
    if consumed < 2 {
        return None;
    }
    let mut arg_locals = stmts[1..consumed]
        .iter()
        .map(|stmt| {
            let arg = single_local_alias_decl(stmt)
                .expect("run boundary belongs to unchanged declarations");
            ConstructorArg {
                binding: arg.binding.clone(),
                value: arg.value.clone(),
                pass_to_sink: true,
                fields_extended: false,
            }
        })
        .collect::<Vec<_>>();

    let mut table_positions = None;
    while let Some(stmt) = stmts.get(consumed) {
        if inline_arg_local_table_function(stmt, &mut arg_locals, &mut table_positions) {
            consumed += 1;
            continue;
        }
        if inline_nested_arg_local_table(stmt, &mut arg_locals) {
            consumed += 1;
            continue;
        }
        break;
    }

    // 原分配容量约束完整字段批次；局部候选尚未安装，失败时整次回滚。
    if arg_locals.iter().any(|arg| {
        arg.fields_extended
            && matches!(&arg.value, AstExpr::TableConstructor(table)
                if !crate::ast::table_layout::matches_preallocation(table))
    }) {
        return None;
    }
    let sink = stmts.get(consumed)?;
    let rewritten_sink = rewrite_terminal_constructor_call_sink(
        sink,
        callee.binding.id,
        callee.value,
        &arg_locals,
        mutable_snapshots,
    )?;

    // Removal-only gates intentionally run after the exact sink call has accepted the local
    // sequence. A standalone `<close>`/debug-root local is not a constructor-handoff candidate.
    if !constructor_local_can_be_removed(callee.binding)
        || arg_locals
            .iter()
            .any(|arg| !constructor_local_can_be_removed(&arg.binding))
    {
        return None;
    }
    // This rule exists to remove constructor scaffolding, not to turn a readable named function
    // back into a multiline result-position IIFE. Short callees still benefit from the compact
    // terminal form.
    if let AstExpr::FunctionExpr(function) = callee.value
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
    fields_extended: bool,
}

struct ConstructorLocal<'a> {
    binding: &'a AstLocalBinding,
    value: &'a AstExpr,
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<ConstructorLocal<'_>> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    Some(ConstructorLocal {
        binding: &local_decl.bindings[0],
        value: &local_decl.values[0],
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
    if !binding.rewrite_authority.may_remove_binding() {
        // 候选拒绝[LayerBoundary]：constructor sugar 会删除独立 binding；HIR Preserve
        // 只能原样转交，不能由 AST 的表构造语法重新证明。
        return false;
    }
    true
}

fn inlineable_local_table_function_stmt(
    stmt: &AstStmt,
    binding: AstBindingRef,
) -> Option<(&str, &AstFunctionExpr)> {
    let (target, field, function) = local_table_function(stmt)?;
    (target == binding).then_some((field, function))
}

/// 从当前接线语句读取一次目标身份和函数；不从实参位置反推目标。
fn local_table_function(stmt: &AstStmt) -> Option<(AstBindingRef, &str, &AstFunctionExpr)> {
    let (name, field, function) = match stmt {
        AstStmt::Assign(assign) => {
            if assign.targets.len() != 1 || assign.values.len() != 1 {
                return None;
            }
            let AstLValue::FieldAccess(access) = &assign.targets[0] else {
                return None;
            };
            let AstExpr::Var(name) = &access.base else {
                return None;
            };
            let AstExpr::FunctionExpr(function) = &assign.values[0] else {
                return None;
            };
            (name, access.field.as_str(), function.as_ref())
        }
        AstStmt::FunctionDecl(decl) => {
            let AstFunctionName::Plain(path) = &decl.target else {
                return None;
            };
            if path.fields.len() != 1 {
                return None;
            }
            (&path.root, path.fields[0].as_str(), &decl.func)
        }
        _ => return None,
    };
    let binding = AstBindingRef::from_name_ref(name)?;
    if function.captured_bindings.contains(&binding) {
        // 候选拒绝[SemanticBarrier:Capture]：`local obj={}; obj.f=function() return obj end`
        // 折入 initializer 后 obj 尚未进入作用域，closure 会改绑外层名字。
        return None;
    }
    Some((binding, field, function))
}

fn inline_arg_local_table_function(
    stmt: &AstStmt,
    arg_locals: &mut [ConstructorArg],
    table_positions: &mut Option<BTreeMap<AstBindingRef, usize>>,
) -> bool {
    let Some((binding, field, func)) = local_table_function(stmt) else {
        return false;
    };
    // 接线只追加字段，不改变实参值的种类。索引属于当前候选，首次字段接线才建立；
    // 保留旧扫描的首个同身份 table，包括已经接入其他 table 的实参。
    let positions = table_positions.get_or_insert_with(|| {
        let mut positions = BTreeMap::new();
        for (index, arg) in arg_locals.iter().enumerate() {
            if matches!(arg.value, AstExpr::TableConstructor(_)) {
                positions.entry(arg.binding.id).or_insert(index);
            }
        }
        positions
    });
    let Some(&index) = positions.get(&binding) else {
        return false;
    };
    let arg_local = &mut arg_locals[index];
    let AstExpr::TableConstructor(table) = &mut arg_local.value else {
        unreachable!("field wiring preserves indexed table values")
    };
    if !table_can_append_record_field(table, field) {
        return false;
    }
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: crate::ast::table_layout::record_key(&table.allocation, field.to_owned()),
            value: AstExpr::FunctionExpr(Box::new(func.clone())),
        }));
    arg_local.fields_extended = true;
    true
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
    if !table_can_append_record_field(table, &field) {
        return false;
    }

    // 这里专门收回“先建内层 methods table，再接到外层 metadata 字段”的机械接线。
    // 它只在内层 table 仍是独立 constructor local 时触发，不会把任意普通变量赋值猜成
    // 嵌套表字面量。
    table
        .fields
        .push(AstTableField::Record(crate::ast::AstRecordField {
            key: crate::ast::table_layout::record_key(&table.allocation, field),
            value: inner_value,
        }));
    arg_locals[inner_index].pass_to_sink = false;
    arg_locals[outer_index].fields_extended = true;
    true
}

fn table_can_append_record_field(
    table: &crate::ast::common::AstTableConstructor,
    field: &str,
) -> bool {
    if !table.allocation.permits_record_key(Some(
        crate::value_semantics::table::TableTemplateKey::String(field.into()),
    )) {
        return false;
    }
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
        AstBindingRef::from_name_ref(outer_name)?,
        access.field.clone(),
        AstBindingRef::from_name_ref(inner_name)?,
    ))
}

fn terminal_constructor_call(stmt: &AstStmt) -> Option<&AstCallExpr> {
    let expr = match stmt {
        AstStmt::Return(stmt) => stmt.values.first()?,
        AstStmt::LocalDecl(stmt) => stmt.values.first()?,
        AstStmt::If(stmt) => &stmt.cond,
        AstStmt::NumericFor(stmt) => &stmt.start,
        AstStmt::GenericFor(stmt) => stmt.iterator.first()?,
        AstStmt::CallStmt(stmt) => {
            return match &stmt.call {
                AstCallKind::Call(call) => Some(call),
                AstCallKind::MethodCall(_) => None,
            };
        }
        // 循环会重复 initializer，Assign/FunctionDecl 只能是接线而不是终端。
        _ => return None,
    };
    match expr {
        AstExpr::Call(call) => Some(call),
        _ => None,
    }
}

fn rewrite_terminal_constructor_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstStmt> {
    let call = Box::new(rewrite_terminal_constructor_call(
        terminal_constructor_call(stmt)?,
        callee_binding,
        callee_expr,
        arg_locals,
        mutable_snapshots,
    )?);
    match stmt {
        AstStmt::Return(ret) => {
            let value = AstExpr::Call(call);
            let mut rewritten: AstReturn = ret.as_ref().clone();
            rewritten.values[0] = value;
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::LocalDecl(local_decl) => {
            let value = AstExpr::Call(call);
            let mut rewritten: AstLocalDecl = local_decl.as_ref().clone();
            rewritten.values[0] = value;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::CallStmt(_) => {
            // 候选接受[EvalOrderProof]：直属 call 没有外层前缀，按原序求值一次。
            Some(AstStmt::CallStmt(Box::new(
                crate::ast::common::AstCallStmt {
                    call: AstCallKind::Call(call),
                },
            )))
        }
        AstStmt::If(if_stmt) => {
            let cond = AstExpr::Call(call);
            let mut rewritten = if_stmt.as_ref().clone();
            rewritten.cond = cond;
            // 候选接受[EvalOrderProof/ValueArityProof]：condition 是无前缀的一次性标量位置。
            Some(AstStmt::If(Box::new(rewritten)))
        }
        AstStmt::NumericFor(numeric_for) => {
            let start = AstExpr::Call(call);
            let mut rewritten = numeric_for.as_ref().clone();
            rewritten.start = start;
            // 候选接受[EvalOrderProof/ValueArityProof]：start 是 header 首个一次性标量事件。
            Some(AstStmt::NumericFor(Box::new(rewritten)))
        }
        AstStmt::GenericFor(generic_for) => {
            let first = AstExpr::Call(call);
            let mut rewritten = generic_for.as_ref().clone();
            rewritten.iterator[0] = first;
            // 候选接受[EvalOrderProof/ValueArityProof]：首 iterator 无前缀；原有单值/open 边界保持。
            Some(AstStmt::GenericFor(Box::new(rewritten)))
        }
        AstStmt::While(_) | AstStmt::Repeat(_) => {
            // 候选拒绝[SemanticBarrier:EvalCount]：initializer 搬入条件会变成逐轮求值。
            None
        }
        _ => None,
    }
}

fn rewrite_terminal_constructor_call(
    call: &AstCallExpr,
    callee_binding: AstBindingRef,
    callee_expr: &AstExpr,
    arg_locals: &[ConstructorArg],
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<AstCallExpr> {
    let AstExpr::Var(name) = &call.callee else {
        return None;
    };
    let active_args = arg_locals
        .iter()
        .filter(|arg| arg.pass_to_sink)
        .collect::<Vec<_>>();
    if !callee_binding.matches_name_ref(name) {
        return None;
    }

    // 首次出现位置必须按声明顺序递增。删除已命中的键可忽略后续重复实参；
    // 不能贪心寻找下一个 expected，否则 [b,a,b] 会错误承接 [a,b]。
    let mut pending = BTreeMap::new();
    for (ordinal, expected) in active_args.iter().enumerate() {
        if pending.insert(expected.binding.id, ordinal).is_some() {
            return None;
        }
    }
    let mut next = 0;
    for arg in &call.args {
        if let AstExpr::Var(name) = arg
            && let Some(binding) = AstBindingRef::from_name_ref(name)
            && let Some(ordinal) = pending.remove(&binding)
        {
            if ordinal != next {
                // 候选拒绝[SemanticBarrier:EvalOrder]：实参首次承接顺序反转会反转 initializer 事件。
                return None;
            }
            next += 1;
        }
    }
    if !pending.is_empty() {
        return None;
    }

    let mut expected_args = active_args.iter().copied().peekable();
    let mut rewritten_args = Vec::with_capacity(call.args.len());
    let mut last_arg_is_inlined_constructor = false;
    for arg in &call.args {
        if let Some(expected) = expected_args.peek()
            && matches!(arg, AstExpr::Var(name) if expected.binding.id.matches_name_ref(name))
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

    if last_arg_is_inlined_constructor
        && let Some(last) = rewritten_args.last_mut()
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
    Some(AstCallExpr {
        callee: callee_expr.clone(),
        args: rewritten_args,
        method_key: call.method_key.clone(),
        callee_root_handoff: call.callee_root_handoff,
        method_rewrite_transaction: call.method_rewrite_transaction,
    })
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
