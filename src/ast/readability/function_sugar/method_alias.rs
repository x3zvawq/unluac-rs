//! 收回 method-call 的局部别名脚手架。
//!
//! 这个 pass 只处理 AST build 明确留下来的机械壳：
//! - `local r = expr; local f = r.method; local x = f(r)` -> `local x = expr:method()`
//! - `local r = expr; local f = r.method; local x = wrap(f(r))` 在外层前缀稳定时收回嵌套调用
//! - `local r = expr; local x = r.method(r)` -> `local x = expr:method()`
//! - `local r = ...; local x = { r.method(r) }` -> `local x = { (...):method() }`
//! - `local r = expr; for x in r.iter(r), state do` -> `for x in expr:iter(), state do`
//!
//! 普通 `obj.method(obj)` 不足以证明 method call：字段查询可能通过 `__index` 改写
//! `obj`，而冒号调用只会求值一次 receiver。没有独立 receiver 快照的形状必须保留。
//! alias 原本只求值一次，因此也不能搬入 while/repeat，或越过外层调用、左侧操作数、
//! 复杂赋值目标等可观察前缀。

use super::super::binding_flow::{BindingUseIndex, MutableSnapshotNames};
use super::super::binding_ref::name_matches_binding;
use super::super::expr_analysis::expr_requires_ordered_snapshot;
use super::super::visit::{self, AstVisitor};
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstFunctionName, AstGlobalDecl,
    AstIf, AstLValue, AstLocalAttr, AstLocalOrigin, AstMethodCallExpr, AstNameRef, AstReturn,
    AstStmt,
};

pub(super) fn try_recover_method_alias_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts, use_index, stmt_base, mutable_snapshots).or_else(|| {
        try_recover_receiver_alias_direct_method_call(
            stmts,
            use_index,
            stmt_base,
            mutable_snapshots,
        )
    })
}

pub(in crate::ast::readability) fn run_belongs_to_method_alias_owner(
    stmts: &[AstStmt],
    index: usize,
    sink_index: usize,
    use_index: &BindingUseIndex,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    if stmts.get(sink_index).is_none() {
        return false;
    }
    let run = &stmts[index..];
    match sink_index.checked_sub(index) {
        Some(1) => {
            try_recover_receiver_alias_direct_method_call(run, use_index, index, mutable_snapshots)
                .is_some()
        }
        Some(2) => {
            try_recover_with_receiver_alias(run, use_index, index, mutable_snapshots).is_some()
        }
        _ => false,
    }
}

fn try_recover_with_receiver_alias(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let [receiver_alias, field_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_binding, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    let (field_binding, field_access) = single_field_alias_decl(field_alias)?;
    let AstExpr::Var(receiver_name) = &field_access.base else {
        return None;
    };
    if !name_matches_binding(receiver_name, receiver_binding) {
        return None;
    }
    if binding_is_written_in_suffix(stmts, 1, receiver_binding)
        || binding_is_written_in_suffix(stmts, 2, field_binding)
    {
        // 候选拒绝[SemanticBarrier:Scope]：删除 alias declaration 会让后续 direct write 解析到外层 binding，不能只按读取次数判断。
        return None;
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 2
        || use_index.count_uses_in_suffix(stmt_base + 2, field_binding) != 1
    {
        // 候选拒绝[SemanticBarrier:EvalCount]：receiver 必须只供字段 lookup 与首参各一次，field alias 也只能作为唯一 callee；否则删除 local 会复制/丢失 use。
        return None;
    }
    if receiver_alias_source_may_drop_root(stmts, receiver_expr, mutable_snapshots) {
        return None;
    }

    Some((
        recover_method_call_sink(
            sink,
            field_binding,
            field_access.field.clone(),
            receiver_expr.clone(),
            mutable_snapshots,
            |arg| matches!(arg, AstExpr::Var(name) if name_matches_binding(name, receiver_binding)),
        )?,
        3,
    ))
}

fn try_recover_receiver_alias_direct_method_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let [receiver_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_binding, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    if binding_is_written_in_suffix(stmts, 1, receiver_binding) {
        // 候选拒绝[SemanticBarrier:Scope]：删除 receiver local 会把 sink/后缀的 direct write 绑定到外层名称。
        return None;
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 2 {
        // 候选拒绝[SemanticBarrier:EvalCount]：direct 形状仍要求 receiver 恰好用于 lookup 和首参，额外 use 不能随 alias 删除。
        return None;
    }
    if receiver_alias_source_may_drop_root(stmts, receiver_expr, mutable_snapshots) {
        return None;
    }
    let rewritten = rewrite_single_expr_sink_stmt(sink, |value| {
        rewrite_method_call_expr_in_order(
            value,
            mutable_snapshots,
            expr_prefix_is_stable(receiver_expr, mutable_snapshots),
            |expr| {
                recover_direct_method_call_with_receiver_alias_expr(
                    expr,
                    receiver_binding,
                    receiver_expr,
                )
            },
        )
    })?;
    Some((rewritten, 2))
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(AstBindingRef, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1
        || local_decl.values.len() != 1
        || local_decl.bindings[0].attr != AstLocalAttr::None
        || local_decl.bindings[0].origin != AstLocalOrigin::Recovered
    {
        return None;
    }
    Some((local_decl.bindings[0].id, &local_decl.values[0]))
}

fn single_field_alias_decl(
    stmt: &AstStmt,
) -> Option<(AstBindingRef, &crate::ast::common::AstFieldAccess)> {
    let (binding, value) = single_local_alias_decl(stmt)?;
    let AstExpr::FieldAccess(access) = value else {
        return None;
    };
    Some((binding, access))
}

fn binding_is_written_in_suffix(stmts: &[AstStmt], start: usize, binding: AstBindingRef) -> bool {
    name_is_written_in_suffix(stmts, start, &binding.to_name_ref())
}

fn name_is_written_in_suffix(stmts: &[AstStmt], start: usize, name: &AstNameRef) -> bool {
    stmts.get(start..).is_some_and(|suffix| {
        suffix.iter().any(|stmt| {
            let mut finder = NameWriteFinder {
                name: name.clone(),
                found: false,
            };
            visit::visit_stmt(stmt, &mut finder);
            finder.found
        })
    })
}

fn receiver_alias_source_may_drop_root(
    stmts: &[AstStmt],
    receiver_expr: &AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    let AstExpr::Var(source) = receiver_expr else {
        return false;
    };
    if matches!(source, AstNameRef::Global(_) | AstNameRef::Upvalue(_)) {
        // 候选拒绝[SemanticBarrier:Lifetime]：global/upvalue 可在 sink 期间换值，删除 alias 会提前释放旧 receiver root。
        return true;
    }
    if mutable_snapshots.contains(source) || name_is_written_in_suffix(stmts, 1, source) {
        // 候选拒绝[SemanticBarrier:Lifetime/ProofIncomplete]：后缀写会丢失旧 root；capture 尚无只读 provenance，反例见 regress_406。
        return true;
    }
    false
}

struct NameWriteFinder {
    name: AstNameRef,
    found: bool,
}

impl AstVisitor for NameWriteFinder {
    fn visit_function_expr(&mut self, _function: &crate::ast::common::AstFunctionExpr) -> bool {
        // LocalId/SyntheticLocalId are function-local. Child bodies can only refer to the
        // outer binding through capture provenance, not through a same-numbered direct write.
        false
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        match stmt {
            AstStmt::FunctionDecl(function_decl) => {
                let AstFunctionName::Plain(path) = &function_decl.target else {
                    return;
                };
                if path.fields.is_empty() && path.root == self.name {
                    self.found = true;
                }
            }
            AstStmt::LocalFunctionDecl(function_decl)
                if function_decl.name.to_name_ref() == self.name =>
            {
                self.found = true;
            }
            _ => {}
        }
    }

    fn visit_lvalue(&mut self, lvalue: &AstLValue) {
        if let AstLValue::Name(name) = lvalue && name == &self.name {
            self.found = true;
        }
    }
}

fn recover_method_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    method: String,
    receiver: AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstStmt> {
    rewrite_single_expr_sink_stmt(stmt, |value| {
        recover_method_call_expr(
            value,
            callee_binding,
            &method,
            &receiver,
            mutable_snapshots,
            &receiver_matches,
        )
    })
}

fn recover_method_call_expr(
    expr: &AstExpr,
    callee_binding: AstBindingRef,
    method: &str,
    receiver: &AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
    receiver_matches: &dyn Fn(&AstExpr) -> bool,
) -> Option<AstExpr> {
    rewrite_method_call_expr_in_order(expr, mutable_snapshots, false, |expr| {
        if let AstExpr::Call(call) = expr
            && let Some(method_call) = recover_method_call(
                call,
                callee_binding,
                method.to_owned(),
                receiver.clone(),
                receiver_matches,
            )
        {
            return Some(AstExpr::MethodCall(Box::new(method_call)));
        }

        None
    })
}

fn recover_method_call(
    call: &AstCallExpr,
    callee_binding: AstBindingRef,
    method: String,
    receiver: AstExpr,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstMethodCallExpr> {
    let AstExpr::Var(callee_name) = &call.callee else {
        return None;
    };
    if !name_matches_binding(callee_name, callee_binding) {
        return None;
    }
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    if !receiver_matches(receiver_arg) {
        return None;
    }
    Some(AstMethodCallExpr {
        receiver,
        method,
        args: args.to_vec(),
    })
}

fn rewrite_method_call_expr_in_order<F>(
    expr: &AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
    can_cross_table_allocation: bool,
    try_rewrite_here: F,
) -> Option<AstExpr>
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    if let Some(rewritten) = try_rewrite_here(expr) {
        return Some(rewritten);
    }

    let mut rewritten = expr.clone();
    match &mut rewritten {
        AstExpr::Unary(unary) => {
            unary.expr = rewrite_method_call_expr_in_order(
                &unary.expr,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Binary(binary) => {
            if let Some(lhs) = rewrite_method_call_expr_in_order(
                &binary.lhs,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            ) {
                binary.lhs = lhs;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&binary.lhs, mutable_snapshots) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：把 alias initializer 搬到 rhs 会越过 lhs；`f()` 或可变快照读取可改变调用/lookup 顺序与读值。
                return None;
            }
            binary.rhs = rewrite_method_call_expr_in_order(
                &binary.rhs,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            // 候选拒绝[SemanticBarrier:ControlFlow]：只搜索必求值的 lhs；若搬入短路 rhs，原先无条件执行的 alias initializer 会变成条件执行。
            logical.lhs = rewrite_method_call_expr_in_order(
                &logical.lhs,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Call(call) => {
            if let Some(callee) = rewrite_method_call_expr_in_order(
                &call.callee,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            ) {
                call.callee = callee;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&call.callee, mutable_snapshots) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：嵌入某个 arg 前必须越过 callee 求值；调用/lookup 或可变快照不能交换。
                return None;
            }
            for arg in &mut call.args {
                if let Some(value) = rewrite_method_call_expr_in_order(
                    arg,
                    mutable_snapshots,
                    can_cross_table_allocation,
                    try_rewrite_here,
                ) {
                    *arg = value;
                    return Some(rewritten);
                }
                if !expr_prefix_is_stable(arg, mutable_snapshots) {
                    // 候选拒绝[SemanticBarrier:EvalOrder]：目标位于后续 arg 时，所有前缀 arg 必须无可观察事件且不读取可变快照。
                    return None;
                }
            }
            None
        }
        AstExpr::MethodCall(call) => {
            // 候选拒绝[SemanticBarrier:EvalOrder]：只搜索 receiver；冒号调用的 method lookup 位于 args 之前，把 alias initializer 搬进 args 会跨越 lookup。
            call.receiver = rewrite_method_call_expr_in_order(
                &call.receiver,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::FieldAccess(access) => {
            access.base = rewrite_method_call_expr_in_order(
                &access.base,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::IndexAccess(access) => {
            if let Some(base) = rewrite_method_call_expr_in_order(
                &access.base,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            ) {
                access.base = base;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&access.base, mutable_snapshots) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：搬入 index 前会跨过 base 求值，必须证明该前缀没有调用/lookup/可变快照读取。
                return None;
            }
            access.index = rewrite_method_call_expr_in_order(
                &access.index,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::SingleValue(inner) => {
            **inner = rewrite_method_call_expr_in_order(
                inner,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Nil
        | AstExpr::Boolean(_)
        | AstExpr::Integer(_)
        | AstExpr::Number(_)
        | AstExpr::String(_)
        | AstExpr::Int64(_)
        | AstExpr::UInt64(_)
        | AstExpr::Vector(_)
        | AstExpr::Complex { .. }
        | AstExpr::Var(_)
        | AstExpr::VarArg
        | AstExpr::FunctionExpr(_)
        | AstExpr::Error(_) => None,
        AstExpr::TableConstructor(table) => {
            if !can_cross_table_allocation {
                // 候选拒绝[SemanticBarrier:EvalOrder]：table 在首字段前已分配；三语句 alias 会把先前的 `r.method` lookup 搬到分配后，两语句 direct 形状也只有稳定 receiver initializer 才能跨过它。
                return None;
            }
            for field in &mut table.fields {
                match field {
                    crate::ast::common::AstTableField::Array(value) => {
                        if let Some(next) = rewrite_method_call_expr_in_order(
                            value,
                            mutable_snapshots,
                            can_cross_table_allocation,
                            try_rewrite_here,
                        ) {
                            *value = next;
                            return Some(rewritten);
                        }
                        if !expr_prefix_is_stable(value, mutable_snapshots) {
                            return None;
                        }
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &mut record.key {
                            if let Some(next) = rewrite_method_call_expr_in_order(
                                key,
                                mutable_snapshots,
                                can_cross_table_allocation,
                                try_rewrite_here,
                            ) {
                                *key = next;
                                return Some(rewritten);
                            }
                            if !expr_prefix_is_stable(key, mutable_snapshots) {
                                return None;
                            }
                        }
                        if let Some(next) = rewrite_method_call_expr_in_order(
                            &record.value,
                            mutable_snapshots,
                            can_cross_table_allocation,
                            try_rewrite_here,
                        ) {
                            record.value = next;
                            return Some(rewritten);
                        }
                        if !expr_prefix_is_stable(&record.value, mutable_snapshots) {
                            return None;
                        }
                    }
                }
            }
            None
        }
    }
}

fn expr_prefix_is_stable(expr: &AstExpr, mutable_snapshots: &MutableSnapshotNames) -> bool {
    !expr_requires_ordered_snapshot(expr, mutable_snapshots)
}

fn recover_direct_method_call_with_receiver_alias_expr(
    expr: &AstExpr,
    receiver_binding: AstBindingRef,
    receiver_expr: &AstExpr,
) -> Option<AstExpr> {
    let AstExpr::Call(call) = expr else {
        return None;
    };
    let AstExpr::FieldAccess(access) = &call.callee else {
        return None;
    };
    let AstExpr::Var(receiver_base_name) = &access.base else {
        return None;
    };
    if !name_matches_binding(receiver_base_name, receiver_binding) {
        return None;
    }
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Var(receiver_arg_name) = receiver_arg else {
        return None;
    };
    if !name_matches_binding(receiver_arg_name, receiver_binding) {
        return None;
    }

    Some(AstExpr::MethodCall(Box::new(AstMethodCallExpr {
        receiver: receiver_expr.clone(),
        method: access.field.clone(),
        args: args.to_vec(),
    })))
}

fn rewrite_single_expr_sink_stmt(
    stmt: &AstStmt,
    mut rewrite_expr: impl FnMut(&AstExpr) -> Option<AstExpr>,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let [value] = local_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten = (**local_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::GlobalDecl(global_decl) => {
            let [value] = global_decl.values.as_slice() else {
                return None;
            };
            let mut rewritten: AstGlobalDecl = (**global_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            Some(AstStmt::GlobalDecl(Box::new(rewritten)))
        }
        AstStmt::Assign(assign) => {
            let value = assign.values.first()?;
            if assign
                .targets
                .iter()
                .any(|target| !matches!(target, crate::ast::common::AstLValue::Name(_)))
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：Lua 先求值复杂 lvalue 地址再求 RHS；把 alias initializer 移入 RHS 会越过 table/key lookup（如 `t[f()] = alias()`）。
                return None;
            }
            let mut rewritten = (**assign).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：纯 Name targets 没有地址求值，
            // 首 RHS 前无运行时前缀；存在后续 RHS 时该位置前后都截成单值。
            Some(AstStmt::Assign(Box::new(rewritten)))
        }
        AstStmt::Return(ret) => {
            let value = ret.values.first()?;
            let mut rewritten: AstReturn = (**ret).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：首项前没有求值前缀；存在后续
            // return value 时该位置前后都截成单值，作为唯一项时则都保留 open tail。
            Some(AstStmt::Return(Box::new(rewritten)))
        }
        AstStmt::If(if_stmt) => Some(AstStmt::If(Box::new(AstIf {
            cond: rewrite_expr(&if_stmt.cond)?,
            then_block: if_stmt.then_block.clone(),
            else_block: if_stmt.else_block.clone(),
        }))),
        AstStmt::CallStmt(call_stmt) => {
            let call_expr = match &call_stmt.call {
                AstCallKind::Call(call) => AstExpr::Call(call.clone()),
                AstCallKind::MethodCall(call) => AstExpr::MethodCall(call.clone()),
            };
            let rewritten_call = match rewrite_expr(&call_expr)? {
                AstExpr::Call(call) => AstCallKind::Call(call),
                AstExpr::MethodCall(call) => AstCallKind::MethodCall(call),
                _ => return None,
            };
            // 候选接受[EvalOrderProof]：CallStmt 只提供表达式容器；callee、先行实参、
            // method lookup 与短路边界仍全部由 ordered walker 逐项验证。
            Some(AstStmt::CallStmt(Box::new(AstCallStmt {
                call: rewritten_call,
            })))
        }
        AstStmt::NumericFor(numeric_for) => {
            let mut rewritten = (**numeric_for).clone();
            rewritten.start = rewrite_expr(&numeric_for.start)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：start 是 NumericFor header 的
            // 首个且只执行一次的事件；该标量位置的调用宽度前后均为一个值。
            Some(AstStmt::NumericFor(Box::new(rewritten)))
        }
        AstStmt::GenericFor(generic_for) => {
            let first = generic_for.iterator.first()?;
            let mut rewritten = (**generic_for).clone();
            rewritten.iterator[0] = rewrite_expr(first)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：iterator[0] 是 header 的首个且
            // 只执行一次的事件；有后续项时前后均截为单值，作为唯一项时均保持 open pack。
            Some(AstStmt::GenericFor(Box::new(rewritten)))
        }
        AstStmt::While(_)
        | AstStmt::Repeat(_)
        | AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => None,
    }
}
