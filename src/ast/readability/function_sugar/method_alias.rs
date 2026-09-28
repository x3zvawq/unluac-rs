//! 收回已带原 method 协议证明的 receiver/callee 别名。
//!
//! 消费显式 method key、binding/use 与求值事实，发布获准的冒号调用。

use super::super::binding_flow::{BindingUseIndex, BindingWriteIndex, MutableSnapshotNames};
use super::super::expr_analysis::is_stable_context_expr;
use super::method_plan::{MethodCallParts, MethodSinkPlan};
use crate::ast::common::{
    AstCallExpr, AstCallKind, AstCallStmt, AstExpr, AstLocalAttr, AstLocalBinding, AstLocalOrigin,
    AstMethodCallExpr, AstModule, AstNameRef, AstStmt,
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
    let (plan, consumed) =
        plan_with_receiver_alias(stmts, use_index, write_index, stmt_base, mutable_snapshots)
            .or_else(|| {
                plan_receiver_alias_direct_method_call(
                    stmts,
                    use_index,
                    write_index,
                    stmt_base,
                    mutable_snapshots,
                )
            })?;
    Some((plan.apply(), consumed))
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
        Some(1) => plan_receiver_alias_direct_method_call(
            run,
            use_index,
            write_index,
            index,
            mutable_snapshots,
        )
        .is_some(),
        Some(2) => plan_with_receiver_alias(run, use_index, write_index, index, mutable_snapshots)
            .is_some(),
        _ => false,
    }
}

fn plan_with_receiver_alias<'a>(
    stmts: &'a [AstStmt],
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(MethodSinkPlan<'a>, usize)> {
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
    let plan = MethodSinkPlan::find(sink, false, false, mutable_snapshots, |call| {
        let AstExpr::Var(callee) = &call.callee else {
            return None;
        };
        let [AstExpr::Var(receiver), args @ ..] = call.args.as_slice() else {
            return None;
        };
        if !field_binding.matches_name_ref(callee)
            || !receiver_binding.matches_name_ref(receiver)
            || call.method_key.as_ref().and_then(|key| key.as_utf8())
                != Some(field_access.field.as_str())
        {
            // 候选拒绝[SemanticBarrier:Lifetime]：普通 GETFIELD 后 COPY 与 SELF
            // 的 receiver 预写顺序不同；独立 alias 及同值读取不证明旧 scratch 根不可观察。
            // methods_05 的额外实参弱引用可在 __index 中观察这段差异。
            return None;
        }
        Some(MethodCallParts {
            receiver: receiver_expr,
            method: &field_access.field,
            args,
        })
    })?;
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

    Some((plan, 3))
}

fn plan_receiver_alias_direct_method_call<'a>(
    stmts: &'a [AstStmt],
    use_index: &BindingUseIndex,
    write_index: &BindingWriteIndex,
    stmt_base: usize,
    mutable_snapshots: &MutableSnapshotNames,
) -> Option<(MethodSinkPlan<'a>, usize)> {
    let [receiver_alias, sink, ..] = stmts else {
        return None;
    };
    let (receiver_local, receiver_expr) = single_local_alias_decl(receiver_alias)?;
    let receiver_binding = receiver_local.id;
    let receiver_is_repeatable = is_stable_context_expr(receiver_expr, mutable_snapshots);
    let plan = MethodSinkPlan::find(
        sink,
        receiver_is_repeatable,
        receiver_is_repeatable,
        mutable_snapshots,
        |call| {
            let AstExpr::FieldAccess(access) = &call.callee else {
                return None;
            };
            let AstExpr::Var(base) = &access.base else {
                return None;
            };
            let [AstExpr::Var(receiver), args @ ..] = call.args.as_slice() else {
                return None;
            };
            if !receiver_binding.matches_name_ref(base)
                || !receiver_binding.matches_name_ref(receiver)
                || call.method_key.as_ref().and_then(|key| key.as_utf8())
                    != Some(access.field.as_str())
            {
                return None;
            }
            Some(MethodCallParts {
                receiver: receiver_expr,
                method: &access.field,
                args,
            })
        },
    )?;
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
    Some((plan, 2))
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
