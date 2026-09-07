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
//! field alias lookup 与事件型 receiver initializer 原本只求值一次，因此不能搬入
//! while/repeat；所有 alias 也不能越过外层调用、左侧操作数、复杂赋值目标等可观察前缀。

use super::super::binding_flow::{BindingUseIndex, BindingWriteIndex, MutableSnapshotNames};
use super::super::expr_analysis::is_stable_context_expr;
use crate::ast::common::{
    AstBindingRef, AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstGlobalDecl, AstIf,
    AstLocalAttr, AstLocalBinding, AstLocalOrigin, AstMethodCallExpr, AstModule, AstNameRef,
    AstReturn, AstStmt,
};
use crate::ast::readability::walk::{self, AstRewritePass};
use crate::ast::visit::{AstVisitor, visit_block};
use crate::hir::HirMethodRewriteTransactionId;

#[derive(Default)]
struct MethodTransactionEndpointCount {
    producers: usize,
    calls: usize,
}

pub(super) struct MethodRewriteTransactionIndex {
    function: crate::hir::HirProtoRef,
    endpoints:
        std::collections::BTreeMap<HirMethodRewriteTransactionId, MethodTransactionEndpointCount>,
}

impl MethodRewriteTransactionIndex {
    pub(super) fn for_function_body(
        function: crate::hir::HirProtoRef,
        block: &crate::ast::common::AstBlock,
    ) -> Self {
        let mut index = Self {
            function,
            endpoints: std::collections::BTreeMap::new(),
        };
        visit_block(block, &mut index);
        index
    }

    fn is_unique(
        &self,
        transaction: HirMethodRewriteTransactionId,
        protocol: crate::hir::HirMethodSetupProtocolId,
    ) -> bool {
        transaction.matches_protocol(self.function, protocol)
            && self
                .endpoints
                .get(&transaction)
                .is_some_and(|count| count.producers == 1 && count.calls == 1)
    }
}

impl AstVisitor for MethodRewriteTransactionIndex {
    fn visit_function_expr(&mut self, _function: &crate::ast::common::AstFunctionExpr) -> bool {
        // 事务身份按 HIR proto 签发；嵌套函数会在进入自身 proto 时另建索引，外层统计必须止步。
        false
    }

    fn visit_stmt(&mut self, stmt: &AstStmt) {
        if let AstStmt::Assign(assign) = stmt
            && let Some(transaction) = assign.method_rewrite_transaction
        {
            self.endpoints.entry(transaction).or_default().producers += 1;
        }
    }

    fn visit_expr(&mut self, expr: &AstExpr) {
        if let AstExpr::Call(call) = expr
            && let Some(transaction) = call.method_rewrite_transaction
        {
            self.endpoints.entry(transaction).or_default().calls += 1;
        }
    }

    fn visit_call(&mut self, call: &AstCallKind) {
        if let AstCallKind::Call(call) = call
            && let Some(transaction) = call.method_rewrite_transaction
        {
            self.endpoints.entry(transaction).or_default().calls += 1;
        }
    }
}

/// 消费 HIR 已保留的 raw method key，把最终 AST 中已经同点求值的调用写成冒号语法。
///
/// 这里只改写 call 节点本身，不删除 receiver/callee producer。字段访问已经位于 call
/// prefix 时，`receiver.field(receiver, args)` 与 `receiver:field(args)` 的求值点、次数和
/// 顺序完全一致；raw key 则排除普通点调用的形状猜测。
pub(super) fn recover_proven_direct_method_calls(module: &mut AstModule) -> bool {
    walk::rewrite_module(module, &mut ProvenDirectMethodCallPass)
}

struct ProvenDirectMethodCallPass;

impl AstRewritePass for ProvenDirectMethodCallPass {
    fn rewrite_stmt(&mut self, stmt: &mut AstStmt) -> bool {
        let AstStmt::CallStmt(call_stmt) = stmt else {
            return false;
        };
        let AstCallKind::Call(call) = &call_stmt.call else {
            return false;
        };
        let Some(method_call) = proven_direct_method_call(call) else {
            return false;
        };
        call_stmt.call = AstCallKind::MethodCall(Box::new(method_call));
        true
    }

    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        let AstExpr::Call(call) = expr else {
            return false;
        };
        let Some(method_call) = proven_direct_method_call(call) else {
            return false;
        };
        *expr = AstExpr::MethodCall(Box::new(method_call));
        true
    }
}

fn proven_direct_method_call(call: &AstCallExpr) -> Option<AstMethodCallExpr> {
    let method_key = call.method_key.as_ref()?.as_utf8()?;
    let AstExpr::FieldAccess(access) = &call.callee else {
        return None;
    };
    if access.field != method_key {
        return None;
    }
    let [receiver, args @ ..] = call.args.as_slice() else {
        return None;
    };
    if receiver != &access.base {
        return None;
    }
    Some(AstMethodCallExpr {
        receiver: access.base.clone(),
        method: access.field.clone(),
        args: args.to_vec(),
    })
}

pub(super) fn try_recover_method_alias_stmt(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    try_recover_with_receiver_alias(stmts, use_index, write_index, stmt_base, mutable_snapshots)
        .or_else(|| {
            try_recover_receiver_alias_direct_method_call(
                stmts,
                use_index,
                write_index,
                stmt_base,
                mutable_snapshots,
            )
        })
}

pub(super) fn try_recover_certified_method_setup(
    stmts: &[AstStmt],
    transactions: &MethodRewriteTransactionIndex,
) -> Option<(AstStmt, usize)> {
    let [AstStmt::Assign(assign), AstStmt::CallStmt(call_stmt), ..] = stmts else {
        return None;
    };
    let transaction = assign.method_rewrite_transaction?;
    let AstCallKind::Call(call) = &call_stmt.call else {
        return None;
    };
    let Some(crate::hir::HirCallRootHandoff::MethodCallee(protocol)) = call.callee_root_handoff
    else {
        return None;
    };
    if call.method_rewrite_transaction != Some(transaction)
        || !transactions.is_unique(transaction, protocol)
    {
        return None;
    }
    let ([crate::ast::common::AstLValue::Name(target)], [AstExpr::FieldAccess(access)]) =
        (assign.targets.as_slice(), assign.values.as_slice())
    else {
        return None;
    };
    let AstExpr::Var(callee) = &call.callee else {
        return None;
    };
    let [receiver, args @ ..] = call.args.as_slice() else {
        return None;
    };
    let method = call.method_key.as_ref()?.as_utf8()?;
    if target != callee || receiver != &access.base || method != access.field {
        return None;
    }
    if args
        .iter()
        .any(|arg| matches!(arg, AstExpr::Var(name) if name == target))
    {
        return None;
    }

    Some((
        AstStmt::CallStmt(Box::new(AstCallStmt {
            call: AstCallKind::MethodCall(Box::new(AstMethodCallExpr {
                receiver: access.base.clone(),
                method: access.field.clone(),
                args: args.to_vec(),
            })),
        })),
        2,
    ))
}

pub(in crate::ast::readability) fn run_belongs_to_method_alias_owner(
    stmts: &[AstStmt],
    index: usize,
    sink_index: usize,
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    if stmts.get(sink_index).is_none() {
        return false;
    }
    let run = &stmts[index..];
    match sink_index.checked_sub(index) {
        Some(1) => try_recover_receiver_alias_direct_method_call(
            run,
            use_index,
            write_index,
            index,
            mutable_snapshots,
        )
        .is_some(),
        Some(2) => {
            try_recover_with_receiver_alias(run, use_index, write_index, index, mutable_snapshots)
                .is_some()
        }
        _ => false,
    }
}

fn try_recover_with_receiver_alias(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let [receiver_alias, field_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_local, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    let receiver_binding = receiver_local.id;
    let (field_local, field_access) = single_field_alias_decl(field_alias)?;
    let field_binding = field_local.id;
    let AstExpr::Var(receiver_name) = &field_access.base else {
        return None;
    };
    if !receiver_binding.matches_name_ref(receiver_name) {
        return None;
    }
    let rewritten = recover_method_call_sink(
        sink,
        field_binding,
        field_access.field.clone(),
        receiver_expr.clone(),
        mutable_snapshots,
        |arg| matches!(arg, AstExpr::Var(name) if receiver_binding.matches_name_ref(name)),
    )?;
    let source_may_drop_receiver_root = receiver_alias_source_may_drop_root(
        write_index,
        stmt_base,
        receiver_expr,
        mutable_snapshots,
    );
    let source_preserves_receiver_root =
        matches!(receiver_expr, AstExpr::Var(_)) && !source_may_drop_receiver_root;
    if !method_alias_local_can_be_removed(receiver_local, source_preserves_receiver_root)
        || !method_alias_local_can_be_removed(field_local, false)
    {
        return None;
    }
    if write_index.has_rebinding_after(stmt_base, receiver_binding)
        || write_index.has_rebinding_after(stmt_base + 1, field_binding)
    {
        // 候选拒绝[SemanticBarrier:Scope]：删除 alias declaration 会让后续 direct write 解析到外层 binding，不能只按读取次数判断。
        return None;
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 2
        || use_index.count_uses_in_suffix(stmt_base + 2, field_binding) != 1
    {
        // 候选拒绝[SemanticBarrier:Scope]：receiver 必须只供字段 lookup 与首参各一次，field alias 也只能作为唯一 callee；额外 direct/captured use 会在删除声明后失去 local owner。
        return None;
    }
    if source_may_drop_receiver_root {
        return None;
    }

    Some((rewritten, 3))
}

fn try_recover_receiver_alias_direct_method_call(
    stmts: &[AstStmt],
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(AstStmt, usize)> {
    let [receiver_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_local, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    let receiver_binding = receiver_local.id;
    let receiver_is_repeatable =
        direct_receiver_initializer_is_repeatable(receiver_expr, mutable_snapshots);
    let rewritten = rewrite_single_expr_sink_stmt(sink, receiver_is_repeatable, |value| {
        rewrite_method_call_expr_in_order(
            value,
            mutable_snapshots,
            receiver_is_repeatable,
            |expr| {
                recover_direct_method_call_with_receiver_alias_expr(
                    expr,
                    receiver_binding,
                    receiver_expr,
                )
            },
        )
    })?;
    let source_may_drop_receiver_root = receiver_alias_source_may_drop_root(
        write_index,
        stmt_base,
        receiver_expr,
        mutable_snapshots,
    );
    let source_preserves_receiver_root =
        matches!(receiver_expr, AstExpr::Var(_)) && !source_may_drop_receiver_root;
    if !method_alias_local_can_be_removed(receiver_local, source_preserves_receiver_root) {
        return None;
    }
    if write_index.has_rebinding_after(stmt_base, receiver_binding) {
        // 候选拒绝[SemanticBarrier:Scope]：删除 receiver local 会把 sink/后缀的 direct write 绑定到外层名称。
        return None;
    }
    if use_index.count_uses_in_suffix(stmt_base + 1, receiver_binding) != 2 {
        // 候选拒绝[SemanticBarrier:Scope]：direct 形状仍要求 receiver 恰好用于 lookup 和首参，额外 direct/captured use 不能随 alias declaration 删除。
        return None;
    }
    if source_may_drop_receiver_root {
        return None;
    }
    Some((rewritten, 2))
}

fn single_local_alias_decl(stmt: &AstStmt) -> Option<(&AstLocalBinding, &AstExpr)> {
    let AstStmt::LocalDecl(local_decl) = stmt else {
        return None;
    };
    if local_decl.bindings.len() != 1 || local_decl.values.len() != 1 {
        return None;
    }
    Some((&local_decl.bindings[0], &local_decl.values[0]))
}

fn single_field_alias_decl(
    stmt: &AstStmt,
) -> Option<(&AstLocalBinding, &crate::ast::common::AstFieldAccess)> {
    let (binding, value) = single_local_alias_decl(stmt)?;
    let AstExpr::FieldAccess(access) = value else {
        return None;
    };
    Some((binding, access))
}

fn method_alias_local_can_be_removed(
    binding: &AstLocalBinding,
    source_preserves_receiver_root: bool,
) -> bool {
    if !binding.rewrite_authority.may_remove_binding() {
        // 候选拒绝[LayerBoundary]：method sugar 会删除 receiver/field binding；HIR
        // Preserve 不能被 AST 的 receiver 求值次数证明覆盖。
        return false;
    }
    match binding.attr {
        AstLocalAttr::None => {}
        AstLocalAttr::Close => {
            // 候选拒绝[SemanticBarrier:Lifetime]：删除 `<close>` receiver/field alias 会同时删除原 block 出口的关闭动作。
            return false;
        }
        AstLocalAttr::Const => {
            // 候选拒绝[PolicyBoundary]：`<const>` 的显式源码声明身份由原 local owner 保留。
            return false;
        }
    }
    match binding.origin {
        AstLocalOrigin::Recovered => true,
        AstLocalOrigin::DebugHinted | AstLocalOrigin::DebugHintedPhysicalRoot => {
            // 候选拒绝[SemanticBarrier:DebugScope]：删除 DebugHinted alias 会改变调用期间 debug.getlocal 可见的名字与区间，反例见 regress_351。
            false
        }
        AstLocalOrigin::PhysicalRoot => {
            // 候选接受[StableRootHandoff]：receiver 的直接 Param/Local source 若在整个后缀
            // 无写入且不是可变 reference snapshot，会持续保存同一对象到原 block 末端；
            // 删除重复 PhysicalRoot alias 不缩短强根区间。否则弱表/`__gc` 可观察提前释放，
            // regress_406 同时覆盖稳定 source 的可删形状与 loop-body 覆盖 source 的拒绝形状。
            source_preserves_receiver_root
        }
    }
}

fn receiver_alias_source_may_drop_root(
    write_index: &BindingWriteIndex,
    stmt_base: usize,
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
    if write_index.name_has_rebinding_after(stmt_base, source) {
        // 候选拒绝[SemanticBarrier:Lifetime]：后缀写会丢失旧 root，反例见 regress_406。
        return true;
    }
    if mutable_snapshots.contains(source) {
        // 候选拒绝[SemanticBarrier:Lifetime]：可写 reference capture 能在 sink 期间换值，删除 alias 会提前释放旧 receiver root。
        return true;
    }
    false
}

fn recover_method_call_sink(
    stmt: &AstStmt,
    callee_binding: AstBindingRef,
    method: String,
    receiver: AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
    receiver_matches: impl Fn(&AstExpr) -> bool,
) -> Option<AstStmt> {
    rewrite_single_expr_sink_stmt(stmt, false, |value| {
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
    if !callee_binding.matches_name_ref(callee_name) {
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
    if !expr_contains_method_call_rewrite(expr, try_rewrite_here) {
        return None;
    }
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
            if expr_contains_method_call_rewrite(&binary.lhs, try_rewrite_here) {
                binary.lhs = rewrite_method_call_expr_in_order(
                    &binary.lhs,
                    mutable_snapshots,
                    can_cross_table_allocation,
                    try_rewrite_here,
                )?;
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
            if !expr_contains_method_call_rewrite(&logical.lhs, try_rewrite_here) {
                // 候选拒绝[SemanticBarrier:ControlFlow]：目标位于短路 rhs 时，原先无条件执行的 alias initializer 搬入后会变成条件执行。
                return None;
            }
            logical.lhs = rewrite_method_call_expr_in_order(
                &logical.lhs,
                mutable_snapshots,
                can_cross_table_allocation,
                try_rewrite_here,
            )?;
            Some(rewritten)
        }
        AstExpr::Call(call) => {
            if expr_contains_method_call_rewrite(&call.callee, try_rewrite_here) {
                call.callee = rewrite_method_call_expr_in_order(
                    &call.callee,
                    mutable_snapshots,
                    can_cross_table_allocation,
                    try_rewrite_here,
                )?;
                return Some(rewritten);
            }
            if !expr_prefix_is_stable(&call.callee, mutable_snapshots) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：嵌入某个 arg 前必须越过 callee 求值；调用/lookup 或可变快照不能交换。
                return None;
            }
            for arg in &mut call.args {
                if expr_contains_method_call_rewrite(arg, try_rewrite_here) {
                    *arg = rewrite_method_call_expr_in_order(
                        arg,
                        mutable_snapshots,
                        can_cross_table_allocation,
                        try_rewrite_here,
                    )?;
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
            if !expr_contains_method_call_rewrite(&call.receiver, try_rewrite_here) {
                // 候选拒绝[SemanticBarrier:EvalOrder]：目标位于冒号调用 args 时，alias initializer 会越过 receiver 与 method lookup。
                return None;
            }
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
            if expr_contains_method_call_rewrite(&access.base, try_rewrite_here) {
                access.base = rewrite_method_call_expr_in_order(
                    &access.base,
                    mutable_snapshots,
                    can_cross_table_allocation,
                    try_rewrite_here,
                )?;
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
                        if expr_contains_method_call_rewrite(value, try_rewrite_here) {
                            *value = rewrite_method_call_expr_in_order(
                                value,
                                mutable_snapshots,
                                can_cross_table_allocation,
                                try_rewrite_here,
                            )?;
                            return Some(rewritten);
                        }
                        if !expr_prefix_is_stable(value, mutable_snapshots) {
                            // 候选拒绝[SemanticBarrier:EvalOrder]：目标 method call 位于后续字段时，先行 array value 的调用/lookup/可变快照不能被 alias initializer 跨越。
                            return None;
                        }
                    }
                    crate::ast::common::AstTableField::Record(record) => {
                        if let crate::ast::common::AstTableKey::Expr(key) = &mut record.key {
                            if expr_contains_method_call_rewrite(key, try_rewrite_here) {
                                *key = rewrite_method_call_expr_in_order(
                                    key,
                                    mutable_snapshots,
                                    can_cross_table_allocation,
                                    try_rewrite_here,
                                )?;
                                return Some(rewritten);
                            }
                            if !expr_prefix_is_stable(key, mutable_snapshots) {
                                // 候选拒绝[SemanticBarrier:EvalOrder]：后续目标不能把 alias initializer 搬过先行 record key 的调用/lookup/可变快照。
                                return None;
                            }
                        }
                        if expr_contains_method_call_rewrite(&record.value, try_rewrite_here) {
                            record.value = rewrite_method_call_expr_in_order(
                                &record.value,
                                mutable_snapshots,
                                can_cross_table_allocation,
                                try_rewrite_here,
                            )?;
                            return Some(rewritten);
                        }
                        if !expr_prefix_is_stable(&record.value, mutable_snapshots) {
                            // 候选拒绝[SemanticBarrier:EvalOrder]：后续字段中的目标不能跨越当前 record value 的可观察求值。
                            return None;
                        }
                    }
                }
            }
            None
        }
    }
}

fn expr_contains_method_call_rewrite<F>(expr: &AstExpr, try_rewrite_here: F) -> bool
where
    F: Fn(&AstExpr) -> Option<AstExpr> + Copy,
{
    if try_rewrite_here(expr).is_some() {
        return true;
    }
    match expr {
        AstExpr::Unary(unary) => expr_contains_method_call_rewrite(&unary.expr, try_rewrite_here),
        AstExpr::Binary(binary) => {
            expr_contains_method_call_rewrite(&binary.lhs, try_rewrite_here)
                || expr_contains_method_call_rewrite(&binary.rhs, try_rewrite_here)
        }
        AstExpr::LogicalAnd(logical) | AstExpr::LogicalOr(logical) => {
            expr_contains_method_call_rewrite(&logical.lhs, try_rewrite_here)
                || expr_contains_method_call_rewrite(&logical.rhs, try_rewrite_here)
        }
        AstExpr::Call(call) => {
            expr_contains_method_call_rewrite(&call.callee, try_rewrite_here)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_method_call_rewrite(arg, try_rewrite_here))
        }
        AstExpr::MethodCall(call) => {
            expr_contains_method_call_rewrite(&call.receiver, try_rewrite_here)
                || call
                    .args
                    .iter()
                    .any(|arg| expr_contains_method_call_rewrite(arg, try_rewrite_here))
        }
        AstExpr::FieldAccess(access) => {
            expr_contains_method_call_rewrite(&access.base, try_rewrite_here)
        }
        AstExpr::IndexAccess(access) => {
            expr_contains_method_call_rewrite(&access.base, try_rewrite_here)
                || expr_contains_method_call_rewrite(&access.index, try_rewrite_here)
        }
        AstExpr::SingleValue(inner) => expr_contains_method_call_rewrite(inner, try_rewrite_here),
        AstExpr::TableConstructor(table) => table.fields.iter().any(|field| match field {
            crate::ast::common::AstTableField::Array(value) => {
                expr_contains_method_call_rewrite(value, try_rewrite_here)
            }
            crate::ast::common::AstTableField::Record(record) => {
                let key_contains = match &record.key {
                    crate::ast::common::AstTableKey::Name(_) => false,
                    crate::ast::common::AstTableKey::Expr(key) => {
                        expr_contains_method_call_rewrite(key, try_rewrite_here)
                    }
                };
                key_contains || expr_contains_method_call_rewrite(&record.value, try_rewrite_here)
            }
        }),
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
        | AstExpr::Error(_) => false,
    }
}

fn expr_prefix_is_stable(expr: &AstExpr, mutable_snapshots: &MutableSnapshotNames) -> bool {
    is_stable_context_expr(expr, mutable_snapshots)
}

fn direct_receiver_initializer_is_repeatable(
    expr: &AstExpr,
    mutable_snapshots: &MutableSnapshotNames,
) -> bool {
    is_stable_context_expr(expr, mutable_snapshots)
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
    if !receiver_binding.matches_name_ref(receiver_base_name) {
        return None;
    }
    let [receiver_arg, args @ ..] = call.args.as_slice() else {
        return None;
    };
    let AstExpr::Var(receiver_arg_name) = receiver_arg else {
        return None;
    };
    if !receiver_binding.matches_name_ref(receiver_arg_name) {
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
    loop_rewrite_is_stable: bool,
    mut rewrite_expr: impl FnMut(&AstExpr) -> Option<AstExpr>,
) -> Option<AstStmt> {
    match stmt {
        AstStmt::LocalDecl(local_decl) => {
            let value = local_decl.values.first()?;
            let mut rewritten = (**local_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：首 RHS 前没有求值前缀；存在后续
            // RHS 时该位置前后都截成单值，作为唯一尾项时都保留原 open pack。
            Some(AstStmt::LocalDecl(Box::new(rewritten)))
        }
        AstStmt::GlobalDecl(global_decl) => {
            let value = global_decl.values.first()?;
            let mut rewritten: AstGlobalDecl = (**global_decl).clone();
            rewritten.values[0] = rewrite_expr(value)?;
            // 候选接受[EvalOrderProof/ValueArityProof]：global 首 RHS 没有先行事件；
            // 多 RHS 的标量边界与唯一尾项的 open pack 均由原位置保持。
            Some(AstStmt::GlobalDecl(Box::new(rewritten)))
        }
        AstStmt::Assign(assign) => {
            let value = assign.values.first()?;
            let rewritten_value = rewrite_expr(value)?;
            if assign
                .targets
                .iter()
                .any(|target| !matches!(target, crate::ast::common::AstLValue::Name(_)))
            {
                // 候选拒绝[SemanticBarrier:EvalOrder]：Lua 先求值复杂 lvalue 地址再求 RHS；把 alias initializer 移入 RHS 会越过 table/key lookup（如 `t[f()] = alias()`）。
                return None;
            }
            let mut rewritten = (**assign).clone();
            rewritten.values[0] = rewritten_value;
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
        AstStmt::If(if_stmt) => {
            let rewritten = AstStmt::If(Box::new(AstIf {
                cond: rewrite_expr(&if_stmt.cond)?,
                then_block: if_stmt.then_block.clone(),
                else_block: if_stmt.else_block.clone(),
            }));
            // 候选接受[EvalCountProof/ValueArityProof]：if condition 是一次性标量 owner，
            // 且 condition 前没有运行时事件。
            Some(rewritten)
        }
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
        AstStmt::While(while_stmt) => {
            let rewritten_cond = rewrite_expr(&while_stmt.cond)?;
            if !loop_rewrite_is_stable {
                // 候选拒绝[SemanticBarrier:EvalCount]：三语句 field-alias 会把一次 method
                // lookup 变成逐轮 lookup；两语句 direct 形状的事件型 receiver initializer
                // 也会从一次变逐轮，regress_251 的 make_loop_receiver 可观察该次数变化。
                return None;
            }
            let mut rewritten = (**while_stmt).clone();
            rewritten.cond = rewritten_cond;
            // 候选接受[EvalCountProof]：仅 direct 形状可到达这里；method lookup 原本就
            // 每轮执行，receiver 是无事件且未标记 mutable 的稳定快照，后续 write/use
            // 与 root gate 还会在提交前复核。
            Some(AstStmt::While(Box::new(rewritten)))
        }
        AstStmt::Repeat(repeat_stmt) => {
            let rewritten_cond = rewrite_expr(&repeat_stmt.cond)?;
            if !loop_rewrite_is_stable {
                // 候选拒绝[SemanticBarrier:EvalCount]：field alias lookup 或事件型 receiver
                // initializer 原本在 repeat 前执行一次，搬入 until 后会逐轮执行。
                return None;
            }
            let mut rewritten = (**repeat_stmt).clone();
            rewritten.cond = rewritten_cond;
            // 候选接受[EvalCountProof]：direct lookup 原本逐轮执行，稳定 receiver 的重复
            // 读取不改变值；write/use/root gate 会在提交前排除循环体改写与 capture。
            Some(AstStmt::Repeat(Box::new(rewritten)))
        }
        AstStmt::DoBlock(_)
        | AstStmt::FunctionDecl(_)
        | AstStmt::LocalFunctionDecl(_)
        | AstStmt::Break
        | AstStmt::Continue
        | AstStmt::Goto(_)
        | AstStmt::Label(_)
        | AstStmt::Error(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::common::{AstBlock, AstFieldAccess, AstLocalDecl, AstWhile};
    use crate::hir::{LocalId, ParamId};

    #[test]
    fn direct_method_alias_accepts_stable_while_receiver() {
        let receiver = AstBindingRef::Local(LocalId(0));
        let source = AstNameRef::Param(ParamId(0));
        let stmts = vec![
            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: receiver,
                    attr: AstLocalAttr::None,
                    origin: AstLocalOrigin::Recovered,
                    rewrite_authority: crate::ast::common::AstRewriteAuthority::AstOwned,
                }],
                values: vec![AstExpr::Var(source.clone())],
                initializer_merge_transaction: None,
                initializer_root_profile: None,
            })),
            AstStmt::While(Box::new(AstWhile {
                cond: AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::FieldAccess(Box::new(AstFieldAccess {
                        base: AstExpr::Var(receiver.to_name_ref()),
                        field: "ready".to_owned(),
                    })),
                    args: vec![AstExpr::Var(receiver.to_name_ref())],
                    method_key: None,
                    callee_root_handoff: None,
                    method_rewrite_transaction: None,
                })),
                body: AstBlock::default(),
            })),
        ];
        let use_index = BindingUseIndex::for_stmts(&stmts);

        let (AstStmt::While(rewritten), consumed) = try_recover_method_alias_stmt(
            &stmts,
            &use_index,
            &BindingWriteIndex::for_stmts(&stmts),
            0,
            &MutableSnapshotNames::new(),
        )
        .expect("stable direct receiver can be read once per loop condition") else {
            panic!("method alias should preserve the while owner")
        };
        assert_eq!(consumed, 2);
        assert!(matches!(
            rewritten.cond,
            AstExpr::MethodCall(call)
                if call.receiver == AstExpr::Var(source)
                    && call.method == "ready"
                    && call.args.is_empty()
        ));
    }
}
