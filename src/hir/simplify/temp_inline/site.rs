//! 这个子模块负责 temp-inline pass 的站点分类。
//!
//! 它依赖 HIR 当前语句/表达式形状，只回答某个 temp 首次被消费的位置属于 direct、callee、
//! condition 还是 loop-head，不会在这里执行内联。无环 Decision 只把唯一入口节点的
//! test 当作必达 condition；其它节点和 target 仍是条件执行的 nested site。method 协议
//! 已经证明 callee base 与隐式首参是同一次 receiver 求值，因此这里把这两个结构引用
//! 合并视为 call 所在的单一站点；普通点调用仍分别扫描 callee 与参数。
//! 例如：`r0(1)` 会把 `r0` 标成 `CallCallee`，`r0:m()` 则把 receiver 标成 call 所在站点。

use super::super::decision::decision_has_cycles;
use super::super::visit::{HirVisitor, visit_stmts};
use super::*;

pub(super) fn inline_site_in_stmt(stmt: &HirStmt, temp: TempId) -> Option<InlineSite> {
    match stmt {
        HirStmt::LocalDecl(local_decl) => {
            find_site_in_exprs(&local_decl.values, temp, InlineSite::Direct)
        }
        HirStmt::Assign(assign) => assign
            .targets
            .iter()
            .find_map(|target| find_site_in_lvalue(target, temp, InlineSite::Direct))
            .or_else(|| find_site_in_exprs(&assign.values, temp, InlineSite::Direct)),
        // 候选拒绝[LayerBoundary]：SETLIST base 的 NewTable origin/home 由 table-constructors 消费，temp-inline 只处理 values。
        // SETLIST carries raw table-write semantics and the physical lifetime of its base
        // register.  Keep that base as a direct binding so the table-constructor pass can prove
        // its NewTable origin/home slot; inlining the producer here loses both facts and used to
        // require materializing an unrelated block-local owner afterward.  Values remain normal
        // direct sites.
        HirStmt::TableSetList(set_list) => (!expr_touches_temp(&set_list.base, temp))
            .then(|| find_site_in_exprs(&set_list.values, temp, InlineSite::Direct))
            .flatten(),
        HirStmt::CallStmt(call_stmt) => {
            find_site_in_call(&call_stmt.call, temp, InlineSite::Direct)
        }
        HirStmt::Return(ret) => direct_fastcall_expr(&ret.values)
            .and_then(|call| find_site_in_call(call, temp, InlineSite::Direct))
            .or_else(|| find_site_in_exprs(&ret.values, temp, InlineSite::ReturnValue)),
        HirStmt::If(if_stmt) => find_site_in_expr(&if_stmt.cond, temp, InlineSite::Condition),
        HirStmt::While(while_stmt) => {
            find_site_in_expr(&while_stmt.cond, temp, InlineSite::LoopCondition)
        }
        HirStmt::Repeat(repeat_stmt) => {
            find_site_in_expr(&repeat_stmt.cond, temp, InlineSite::LoopCondition)
        }
        HirStmt::NumericFor(numeric_for) => {
            find_site_in_expr(&numeric_for.start, temp, InlineSite::LoopHead)
                .or_else(|| find_site_in_expr(&numeric_for.limit, temp, InlineSite::LoopHead))
                .or_else(|| find_site_in_expr(&numeric_for.step, temp, InlineSite::LoopHead))
        }
        HirStmt::GenericFor(generic_for) => {
            find_site_in_exprs(&generic_for.iterator, temp, InlineSite::LoopHead)
        }
        // 候选拒绝[LayerBoundary]：ErrNil、TBC/Close 等 VM/resource 站点由对应 lowering owner 保留，不作为普通表达式 sink。
        // 候选拒绝[SemanticBarrier:ControlFlow]：嵌套 Block 或控制转移内的 use 不是必达站点；把 producer 移入其中会变成条件求值。
        HirStmt::ErrNil(_)
        | HirStmt::ToBeClosed(_)
        | HirStmt::Close(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::Goto(_)
        | HirStmt::Label(_)
        | HirStmt::Block(_) => None,
    }
}

pub(super) fn inline_site_in_repeat_condition(cond: &HirExpr, temp: TempId) -> Option<InlineSite> {
    find_site_in_expr(cond, temp, InlineSite::LoopCondition)
}

/// 判断相邻赋值是否只是在 method 协议前冻结可直接写回源码的 receiver。
///
/// method call 在 HIR 中同时保留 callee base 与隐式首参，因此这里的两个 temp use
/// 最终只对应一次源码 receiver 求值。裸 binding 与以 binding 为根的命名字段链都能
/// 原子收回；普通点调用没有这层协议，不能共享该合同。
pub(super) fn is_method_receiver_snapshot(stmt: &HirStmt, temp: TempId, value: &HirExpr) -> bool {
    if !is_method_receiver_inline_expr(value) {
        return false;
    }
    let call = match stmt {
        HirStmt::CallStmt(call_stmt) => Some(&call_stmt.call),
        HirStmt::LocalDecl(local_decl) => direct_call_expr(&local_decl.values),
        HirStmt::Assign(assign) => direct_call_expr(&assign.values),
        HirStmt::Return(ret) => direct_call_expr(&ret.values),
        _ => None,
    };
    matches!(
        call.and_then(HirCallExpr::method_receiver),
        Some((HirExpr::TempRef(receiver), _)) if *receiver == temp
    )
}

/// 判断 materialization run 中的裸 binding 是否只由某个嵌套 method receiver 对消费。
///
/// 全 proto use-count 由调用方另行限制为两个；这里找到协议匹配的一对引用后，就能排除
/// 普通点调用或第三处消费。字段链不进入这条跨 run 合同，避免重新求 lookup。
pub(super) fn is_bare_method_receiver_snapshot_in_stmt(
    stmt: &HirStmt,
    temp: TempId,
    value: &HirExpr,
) -> bool {
    if !matches!(
        value,
        HirExpr::ParamRef(_) | HirExpr::LocalRef(_) | HirExpr::UpvalueRef(_) | HirExpr::TempRef(_)
    ) {
        return false;
    }

    let mut probe = MethodReceiverTempProbe { temp, found: false };
    visit_stmts(std::slice::from_ref(stmt), &mut probe);
    probe.found
}

struct MethodReceiverTempProbe {
    temp: TempId,
    found: bool,
}

impl HirVisitor for MethodReceiverTempProbe {
    fn visit_call(&mut self, call: &HirCallExpr) {
        self.found |= call.method_receiver().is_some_and(
            |(receiver, _)| matches!(receiver, HirExpr::TempRef(temp) if *temp == self.temp),
        );
    }
}

fn is_method_receiver_inline_expr(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_) => true,
        HirExpr::TableAccess(access) => {
            matches!(&access.key, HirExpr::String(_))
                && is_method_receiver_inline_expr(&access.base)
        }
        _ => false,
    }
}

fn direct_call_expr(values: &crate::hir::common::HirValuePack) -> Option<&HirCallExpr> {
    if values.expr_len() != 1 {
        return None;
    }
    match values.first()? {
        HirExpr::Call(call) => Some(call),
        _ => None,
    }
}

fn direct_fastcall_expr(values: &crate::hir::common::HirValuePack) -> Option<&HirCallExpr> {
    direct_call_expr(values).filter(|call| call.fastcall.is_some())
}

pub(super) fn fastcall_callee_materialization_precedes_temp(stmt: &HirStmt, temp: TempId) -> bool {
    let call = match stmt {
        HirStmt::CallStmt(call_stmt) => &call_stmt.call,
        HirStmt::Return(ret) => {
            let Some(call) = direct_fastcall_expr(&ret.values) else {
                return false;
            };
            call
        }
        _ => return false,
    };
    call.fastcall.is_some() && call.args.iter().any(|arg| expr_touches_temp(arg, temp))
}

pub(super) fn temp_precedes_observable_eval_in_stmt(
    stmt: &HirStmt,
    temp: TempId,
    moved_value_is_observable: bool,
    reference_captured: &ReferenceCapturedBindings,
) -> bool {
    EvalOrderProbe {
        temp,
        mutable_snapshots_are_barriers: moved_value_is_observable,
        reference_captured,
    }
    .stmt(stmt)
}

pub(super) fn temp_precedes_observable_eval_in_expr(
    expr: &HirExpr,
    temp: TempId,
    moved_value_is_observable: bool,
    reference_captured: &ReferenceCapturedBindings,
) -> bool {
    EvalOrderProbe {
        temp,
        mutable_snapshots_are_barriers: moved_value_is_observable,
        reference_captured,
    }
    .expr(expr)
}

/// 返回 PUC Lua 5.2–5.5 标量 upvalue table 左值的 key。
///
/// 这四种方言会先求 key，再读取最终 table upvalue。Lua 5.1、LuaJIT 与 Luau
/// 会先快照 inherited upvalue，因此不能共享这个合同。
pub(super) fn puc_upvalue_table_key_with_deferred_base_read(
    site: InlineSite,
    stmt: &HirStmt,
    dialect: DecompileDialect,
) -> Option<&HirExpr> {
    if site != InlineSite::Index
        || !matches!(
            dialect,
            DecompileDialect::Lua52
                | DecompileDialect::Lua53
                | DecompileDialect::Lua54
                | DecompileDialect::Lua55
        )
    {
        return None;
    }
    let HirStmt::Assign(assign) = stmt else {
        return None;
    };
    let [HirLValue::TableAccess(access)] = assign.targets.as_slice() else {
        return None;
    };
    if !matches!(&access.base, HirExpr::UpvalueRef(_)) {
        return None;
    }
    Some(&access.key)
}

struct EvalOrderProbe<'a> {
    temp: TempId,
    mutable_snapshots_are_barriers: bool,
    reference_captured: &'a ReferenceCapturedBindings,
}

impl EvalOrderProbe<'_> {
    fn stmt(&self, stmt: &HirStmt) -> bool {
        match stmt {
            HirStmt::LocalDecl(local_decl) => self.exprs(&local_decl.values),
            HirStmt::Assign(assign) => {
                let (found, prefix_clear) = self.lvalues(&assign.targets);
                found.unwrap_or_else(|| prefix_clear && self.exprs(&assign.values))
            }
            HirStmt::TableSetList(set_list) => {
                self.exprs(std::iter::once(&set_list.base).chain(&set_list.values))
            }
            HirStmt::CallStmt(call_stmt) => self.call(&call_stmt.call),
            HirStmt::Return(ret) => self.exprs(&ret.values),
            HirStmt::If(if_stmt) => self.expr(&if_stmt.cond),
            HirStmt::While(while_stmt) => self.expr(&while_stmt.cond),
            HirStmt::Repeat(repeat_stmt) => self.expr(&repeat_stmt.cond),
            HirStmt::NumericFor(numeric_for) => {
                self.exprs([&numeric_for.start, &numeric_for.limit, &numeric_for.step])
            }
            HirStmt::GenericFor(generic_for) => self.exprs(&generic_for.iterator),
            HirStmt::ErrNil(_)
            | HirStmt::ToBeClosed(_)
            | HirStmt::Close(_)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::Goto(_)
            | HirStmt::Label(_)
            | HirStmt::Block(_) => false,
        }
    }

    fn exprs<'a>(&self, exprs: impl IntoIterator<Item = &'a HirExpr>) -> bool {
        for expr in exprs {
            if expr_touches_temp(expr, self.temp) {
                return self.expr(expr);
            }
            if !self.prefix_is_clear(expr) {
                return false;
            }
        }
        false
    }

    fn lvalues(&self, lvalues: &[HirLValue]) -> (Option<bool>, bool) {
        let mut prefix_clear = true;
        for lvalue in lvalues {
            if let HirLValue::TableAccess(access) = lvalue {
                for expr in [&access.base, &access.key] {
                    if expr_touches_temp(expr, self.temp) {
                        return (Some(prefix_clear && self.expr(expr)), prefix_clear);
                    }
                    prefix_clear &= self.prefix_is_clear(expr);
                }
            }
        }
        (None, prefix_clear)
    }

    fn call(&self, call: &HirCallExpr) -> bool {
        if let Some(fastcall) = call.fastcall {
            if expr_touches_temp(&call.callee, self.temp) {
                return self.expr(&call.callee);
            }
            for (index, arg) in call.args.fixed.iter().enumerate() {
                if expr_touches_temp(arg, self.temp) {
                    return fastcall.fixed_is_direct(index) && self.expr(arg);
                }
            }
            if let Some(tail) = &call.args.tail
                && expr_touches_temp(tail.as_expr(), self.temp)
            {
                return fastcall.tail_is_direct() && self.expr(tail.as_expr());
            }
            return false;
        }
        self.exprs(std::iter::once(&call.callee).chain(&call.args))
    }

    fn expr(&self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::TempRef(other) => *other == self.temp,
            HirExpr::TableAccess(access) => self.exprs([&access.base, &access.key]),
            HirExpr::Unary(unary) => self.expr(&unary.expr),
            HirExpr::Binary(binary) => self.exprs([&binary.lhs, &binary.rhs]),
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                expr_touches_temp(&logical.lhs, self.temp) && self.expr(&logical.lhs)
            }
            HirExpr::Call(call) => self.call(call),
            HirExpr::TableConstructor(table) => {
                let mut prefix_clear = true;
                for field in &table.fields {
                    match field {
                        HirTableField::Array(value) => {
                            if expr_touches_temp(value, self.temp) {
                                return prefix_clear && self.expr(value);
                            }
                            prefix_clear &= self.prefix_is_clear(value);
                        }
                        HirTableField::Record(field) => {
                            if let HirTableKey::Expr(key) = &field.key {
                                if expr_touches_temp(key, self.temp) {
                                    return prefix_clear && self.expr(key);
                                }
                                prefix_clear &= self.prefix_is_clear(key);
                            }
                            if expr_touches_temp(&field.value, self.temp) {
                                return prefix_clear && self.expr(&field.value);
                            }
                            prefix_clear &= self.prefix_is_clear(&field.value);
                        }
                    }
                }
                table.trailing_multivalue.as_ref().is_some_and(|tail| {
                    let trailing = tail.as_expr();
                    prefix_clear && expr_touches_temp(trailing, self.temp) && self.expr(trailing)
                })
            }
            HirExpr::Decision(decision) => {
                !decision_has_cycles(decision)
                    && decision
                        .nodes
                        .get(decision.entry.index())
                        .is_some_and(|entry| {
                            expr_touches_temp(&entry.test, self.temp) && self.expr(&entry.test)
                        })
            }
            HirExpr::Closure(_)
            | HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => false,
        }
    }

    fn prefix_is_clear(&self, expr: &HirExpr) -> bool {
        !(expr_observes_eval_order(expr)
            || self.mutable_snapshots_are_barriers && self.expr_is_mutable_binding_snapshot(expr))
    }

    fn expr_is_mutable_binding_snapshot(&self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::ParamRef(param) => self.reference_captured.params.contains(param),
            HirExpr::LocalRef(local) => self.reference_captured.locals.contains(local),
            HirExpr::UpvalueRef(_) => true,
            HirExpr::Closure(closure) => closure.captures.iter().any(|capture| {
                capture.mode == crate::hir::common::HirCaptureMode::ByValue
                    && self.expr_is_mutable_binding_snapshot(&capture.value)
            }),
            _ => false,
        }
    }
}

fn find_site_in_exprs<'a>(
    exprs: impl IntoIterator<Item = &'a HirExpr>,
    temp: TempId,
    site: InlineSite,
) -> Option<InlineSite> {
    exprs
        .into_iter()
        .find_map(|expr| find_site_in_expr(expr, temp, site))
}

fn find_site_in_call(call: &HirCallExpr, temp: TempId, site: InlineSite) -> Option<InlineSite> {
    // method receiver 在 HIR 中出现于 callee base 和隐式首参，但 AST lowering 会依赖
    // method fact 只生成一次 receiver；先识别这对引用，避免把源码级单站点误分类成
    // callee 内部的 Nested use。
    if call
        .method_receiver()
        .is_some_and(|(receiver, _)| matches!(receiver, HirExpr::TempRef(other) if *other == temp))
    {
        return Some(site);
    }
    let callee_site = if matches!(site, InlineSite::Direct) {
        if call.fastcall.is_some() {
            InlineSite::FastCallCallee
        } else {
            InlineSite::CallCallee
        }
    } else {
        InlineSite::Nested
    };
    find_site_in_expr(&call.callee, temp, callee_site).or_else(|| {
        if let Some(fastcall) = call.fastcall {
            for (index, arg) in call.args.fixed.iter().enumerate() {
                if let Some(site) = if fastcall.fixed_is_direct(index) {
                    find_site_in_fastcall_arg(arg, temp, InlineSite::FastCallArg)
                } else {
                    find_site_in_expr(arg, temp, InlineSite::CallArg)
                } {
                    return Some(site);
                }
            }
            call.args.tail.as_ref().and_then(|tail| {
                if fastcall.tail_is_direct() {
                    find_site_in_fastcall_arg(tail.as_expr(), temp, InlineSite::FastCallArg)
                } else {
                    find_site_in_expr(tail.as_expr(), temp, InlineSite::CallArg)
                }
            })
        } else {
            find_site_in_exprs(&call.args, temp, InlineSite::CallArg)
        }
    })
}

fn find_site_in_fastcall_arg(
    expr: &HirExpr,
    temp: TempId,
    direct_site: InlineSite,
) -> Option<InlineSite> {
    find_site_in_expr_with_fastcall_context(expr, temp, direct_site)
}

fn find_site_in_expr_with_fastcall_context(
    expr: &HirExpr,
    temp: TempId,
    direct_site: InlineSite,
) -> Option<InlineSite> {
    match expr {
        HirExpr::Call(call) => find_site_in_call(call, temp, InlineSite::Direct),
        HirExpr::Unary(unary) => {
            find_site_in_expr_with_fastcall_context(&unary.expr, temp, direct_site)
        }
        HirExpr::Binary(binary) => {
            find_site_in_expr_with_fastcall_context(&binary.lhs, temp, direct_site)
                .or_else(|| find_site_in_expr_with_fastcall_context(&binary.rhs, temp, direct_site))
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            find_site_in_expr_with_fastcall_context(&logical.lhs, temp, direct_site).or_else(|| {
                find_site_in_expr_with_fastcall_context(&logical.rhs, temp, direct_site)
            })
        }
        // 表构造、表访问与 decision arm 会建立独立求值域，只有纯包装节点继承外层 FASTCALL 参数协议。
        _ => find_site_in_expr(expr, temp, direct_site),
    }
}

fn find_site_in_lvalue(lvalue: &HirLValue, temp: TempId, site: InlineSite) -> Option<InlineSite> {
    match lvalue {
        HirLValue::TableAccess(access) => {
            find_site_in_expr(&access.base, temp, site.descend_access_base())
                .or_else(|| find_site_in_expr(&access.key, temp, InlineSite::Index))
        }
        HirLValue::Param(_)
        | HirLValue::Temp(_)
        | HirLValue::Local(_)
        | HirLValue::Upvalue(_)
        | HirLValue::Global(_) => None,
    }
}

fn find_site_in_expr(expr: &HirExpr, temp: TempId, site: InlineSite) -> Option<InlineSite> {
    match expr {
        HirExpr::TempRef(other) if *other == temp => Some(site),
        HirExpr::TempRef(_) => None,
        HirExpr::TableAccess(access) => {
            find_site_in_expr(&access.base, temp, site.descend_access_base())
                .or_else(|| find_site_in_expr(&access.key, temp, InlineSite::Index))
        }
        HirExpr::Unary(unary) => find_site_in_expr(&unary.expr, temp, site.descend_pure_wrapper()),
        HirExpr::Binary(binary) => {
            let child_site = site.descend_pure_wrapper();
            find_site_in_expr(&binary.lhs, temp, child_site)
                .or_else(|| find_site_in_expr(&binary.rhs, temp, child_site))
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            let child_site = site.descend_pure_wrapper();
            let lhs_site = if site == InlineSite::Direct {
                InlineSite::Condition
            } else {
                child_site
            };
            find_site_in_expr(&logical.lhs, temp, lhs_site)
                .or_else(|| find_site_in_expr(&logical.rhs, temp, child_site))
        }
        HirExpr::Decision(decision) => find_site_in_decision(decision, temp, site),
        HirExpr::Call(call) => find_site_in_call(call, temp, site),
        HirExpr::TableConstructor(table) => table
            .fields
            .iter()
            .find_map(|field| match field {
                HirTableField::Array(value) => find_site_in_expr(value, temp, InlineSite::Nested),
                HirTableField::Record(field) => find_site_in_table_key(&field.key, temp)
                    .or_else(|| find_site_in_expr(&field.value, temp, InlineSite::Nested)),
            })
            .or_else(|| {
                table
                    .trailing_multivalue
                    .as_ref()
                    .and_then(|tail| find_site_in_expr(tail.as_expr(), temp, InlineSite::Nested))
            }),
        HirExpr::Closure(_) => {
            // capture 一旦跨过函数边界，就会直接决定子 proto 的 upvalue provenance。
            // 如果这里把 temp 内联进 capture，后面的 locals / naming 就再也看不到
            // “这是一个单独的局部变量被捕获”这层结构事实了，像
            // `local offset = seed`、`local base = offset + step` 这类源码骨架
            // 会被压扁成参数或裸表达式。这里宁可保留 temp，让后续 locals pass
            // 把它稳定提升成真正的 local。
            None
        }
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => None,
    }
}

fn find_site_in_decision(
    decision: &crate::hir::common::HirDecisionExpr,
    temp: TempId,
    outer_site: InlineSite,
) -> Option<InlineSite> {
    let entry_index = decision.entry.index();
    let entry = decision.nodes.get(entry_index)?;
    let entry_site = if decision_has_cycles(decision) {
        InlineSite::Nested
    } else {
        match outer_site {
            InlineSite::Direct => InlineSite::Condition,
            InlineSite::ReturnValue
            | InlineSite::Condition
            | InlineSite::LoopCondition
            | InlineSite::LoopHead => outer_site,
            InlineSite::Nested
            | InlineSite::Index
            | InlineSite::CallArg
            | InlineSite::FastCallArg
            | InlineSite::CallCallee
            | InlineSite::FastCallCallee
            | InlineSite::AccessBase => InlineSite::Nested,
        }
    };
    find_site_in_expr(&entry.test, temp, entry_site).or_else(|| {
        decision.nodes.iter().enumerate().find_map(|(index, node)| {
            (index != entry_index)
                .then(|| find_site_in_expr(&node.test, temp, InlineSite::Nested))
                .flatten()
                .or_else(|| find_site_in_decision_target(&node.truthy, temp, InlineSite::Nested))
                .or_else(|| find_site_in_decision_target(&node.falsy, temp, InlineSite::Nested))
        })
    })
}

fn find_site_in_decision_target(
    target: &crate::hir::common::HirDecisionTarget,
    temp: TempId,
    site: InlineSite,
) -> Option<InlineSite> {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => find_site_in_expr(expr, temp, site),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => None,
    }
}

fn find_site_in_table_key(key: &HirTableKey, temp: TempId) -> Option<InlineSite> {
    match key {
        HirTableKey::Name(_) => None,
        HirTableKey::Expr(expr) => find_site_in_expr(expr, temp, InlineSite::Index),
    }
}

fn expr_complexity(expr: &HirExpr) -> usize {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => 1,
        HirExpr::Unary(unary) => 1 + expr_complexity(&unary.expr),
        HirExpr::Binary(binary) => 1 + expr_complexity(&binary.lhs) + expr_complexity(&binary.rhs),
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            1 + expr_complexity(&logical.lhs) + expr_complexity(&logical.rhs)
        }
        HirExpr::TableAccess(access) => {
            1 + expr_complexity(&access.base) + expr_complexity(&access.key)
        }
        HirExpr::Decision(decision) => {
            1 + decision
                .nodes
                .iter()
                .map(decision_node_complexity)
                .sum::<usize>()
        }
        HirExpr::Call(call) => {
            1 + expr_complexity(&call.callee) + call.args.iter().map(expr_complexity).sum::<usize>()
        }
        HirExpr::TableConstructor(table) => {
            1 + table
                .fields
                .iter()
                .map(|field| match field {
                    HirTableField::Array(value) => expr_complexity(value),
                    HirTableField::Record(field) => {
                        table_key_complexity(&field.key) + expr_complexity(&field.value)
                    }
                })
                .sum::<usize>()
                + table
                    .trailing_multivalue
                    .as_ref()
                    .map_or(0, |tail| expr_complexity(tail.as_expr()))
        }
        HirExpr::Closure(closure) => {
            1 + closure
                .captures
                .iter()
                .map(|capture| expr_complexity(&capture.value))
                .sum::<usize>()
        }
    }
}

fn decision_node_complexity(node: &crate::hir::common::HirDecisionNode) -> usize {
    1 + expr_complexity(&node.test)
        + decision_target_complexity(&node.truthy)
        + decision_target_complexity(&node.falsy)
}

fn decision_target_complexity(target: &crate::hir::common::HirDecisionTarget) -> usize {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_complexity(expr),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => 1,
    }
}

fn table_key_complexity(key: &HirTableKey) -> usize {
    match key {
        HirTableKey::Name(_) => 1,
        HirTableKey::Expr(expr) => expr_complexity(expr),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum InlineSite {
    Direct,
    Nested,
    ReturnValue,
    Index,
    CallArg,
    FastCallArg,
    CallCallee,
    FastCallCallee,
    AccessBase,
    Condition,
    LoopCondition,
    LoopHead,
}

impl InlineSite {
    pub(super) fn allows(self, replacement: &HirExpr, options: ReadabilityOptions) -> bool {
        match self {
            Self::Direct => true,
            Self::CallCallee | Self::FastCallCallee => true,
            Self::Nested => {
                // 候选拒绝[ProofIncomplete]：nested 分类未区分必达与短路路径；`t=f(); return c and t` 会把 eager call 改成条件求值，应补执行区域事实。
                // 候选拒绝[PolicyBoundary]：纯 nested 表达式仍受固定复杂度阈值限制，避免把机械 temp 换成更难读的嵌套树。
                expr_complexity(replacement) <= NESTED_INLINE_MAX_COMPLEXITY
                    && is_small_pure_nested_inline_expr(replacement)
            }
            Self::AccessBase => {
                // 候选拒绝[PolicyBoundary]：access base 只展示原子值或命名字段链，并服从用户配置的复杂度上限。
                self.complexity_limit(options)
                    .is_some_and(|limit| expr_complexity(replacement) <= limit)
                    && is_access_base_inline_expr(replacement)
            }
            // 条件头 / for 头属于源码结构骨架，保留少量低复杂度表达式能明显减少
            // 机械 temp 噪音；但这里仍然用固定的小阈值，避免把整坨复杂逻辑塞回控制头。
            Self::Condition | Self::LoopCondition => {
                // 候选拒绝[PolicyBoundary]：控制头使用固定展示复杂度上限；该限制不表示表达式不等价。
                expr_complexity(replacement) <= CONTROL_HEAD_INLINE_MAX_COMPLEXITY
            }
            // closure 的复杂度无法概括 child proto 函数体；保留独立 producer，避免把普通
            // local function 压成 loop head 里的多行匿名 iterator。
            Self::LoopHead => {
                // 候选拒绝[PolicyBoundary]：closure 保留命名 producer，避免多行 IIFE；其它 loop-head 值仅受展示复杂度限制。
                !matches!(replacement, HirExpr::Closure(_))
                    && expr_complexity(replacement) <= CONTROL_HEAD_INLINE_MAX_COMPLEXITY
            }
            Self::ReturnValue | Self::Index | Self::CallArg | Self::FastCallArg => {
                // 候选拒绝[PolicyBoundary]：return/index/arg 的用户可配置复杂度阈值只控制源码展示密度。
                self.complexity_limit(options)
                    .is_some_and(|limit| expr_complexity(replacement) <= limit)
            }
        }
    }

    fn complexity_limit(self, options: ReadabilityOptions) -> Option<usize> {
        match self {
            Self::Direct
            | Self::Nested
            | Self::CallCallee
            | Self::FastCallCallee
            | Self::Condition
            | Self::LoopCondition
            | Self::LoopHead => None,
            Self::ReturnValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArg => Some(options.args_inline_max_complexity),
            Self::FastCallArg => Some(options.args_inline_max_complexity),
            Self::AccessBase => Some(options.access_base_inline_max_complexity),
        }
    }

    fn descend_access_base(self) -> Self {
        match self {
            Self::Direct => Self::AccessBase,
            Self::Nested
            | Self::ReturnValue
            | Self::Index
            | Self::CallArg
            | Self::FastCallArg
            | Self::CallCallee
            | Self::FastCallCallee
            | Self::AccessBase
            | Self::Condition
            | Self::LoopCondition
            | Self::LoopHead => Self::Nested,
        }
    }

    fn descend_pure_wrapper(self) -> Self {
        match self {
            // 这里只保留 index 语境向下穿透纯壳层，避免像 `t[(x + 1)]` 这种机械中间 temp
            // 在进入 locals 阶段前就失去折叠机会；而 return/call 等站位仍维持保守边界，
            // 防止上下文再次泄漏成“整坨表达式”。
            Self::Index => Self::Index,
            // 条件头 / loop 头本身就是高价值结构位置，允许低复杂度表达式继续穿过
            // 纯 wrapper，能把 `if ((a + b) % 2 == 0)`、`for i = 1, n, 1` 这类源码形状
            // 从机械 temp 链里收回来。
            Self::Condition => Self::Condition,
            Self::LoopCondition => Self::LoopCondition,
            Self::LoopHead => Self::LoopHead,
            Self::Direct
            | Self::Nested
            | Self::ReturnValue
            | Self::CallArg
            | Self::FastCallArg
            | Self::CallCallee
            | Self::FastCallCallee
            | Self::AccessBase => Self::Nested,
        }
    }

    pub(super) const fn is_call_callee(self) -> bool {
        matches!(self, Self::CallCallee | Self::FastCallCallee)
    }
}

pub(super) fn is_stable_inline_value(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
    )
}

fn is_atomic_nested_inline_expr(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::VarArg
    )
}

fn is_small_pure_nested_inline_expr(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::TempRef(_)
        | HirExpr::GlobalRef(_) => true,
        HirExpr::Unary(unary) => is_small_pure_nested_inline_expr(&unary.expr),
        HirExpr::Binary(binary) => {
            is_small_pure_nested_inline_expr(&binary.lhs)
                && is_small_pure_nested_inline_expr(&binary.rhs)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            is_small_pure_nested_inline_expr(&logical.lhs)
                && is_small_pure_nested_inline_expr(&logical.rhs)
        }
        HirExpr::VarArg
        | HirExpr::TableAccess(_)
        | HirExpr::Decision(_)
        | HirExpr::Call(_)
        | HirExpr::TableConstructor(_)
        | HirExpr::Closure(_)
        | HirExpr::Unresolved(_) => false,
    }
}

fn is_access_base_inline_expr(expr: &HirExpr) -> bool {
    is_atomic_nested_inline_expr(expr) || is_named_field_chain_expr(expr)
}

fn is_named_field_chain_expr(expr: &HirExpr) -> bool {
    let HirExpr::TableAccess(access) = expr else {
        return false;
    };
    matches!(&access.key, HirExpr::String(_))
        && (is_atomic_nested_inline_expr(&access.base) || is_named_field_chain_expr(&access.base))
}

pub(super) fn expr_touches_temp(expr: &HirExpr, temp: TempId) -> bool {
    match expr {
        HirExpr::TempRef(other) => *other == temp,
        HirExpr::TableAccess(access) => {
            expr_touches_temp(&access.base, temp) || expr_touches_temp(&access.key, temp)
        }
        HirExpr::Unary(unary) => expr_touches_temp(&unary.expr, temp),
        HirExpr::Binary(binary) => {
            expr_touches_temp(&binary.lhs, temp) || expr_touches_temp(&binary.rhs, temp)
        }
        HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
            expr_touches_temp(&logical.lhs, temp) || expr_touches_temp(&logical.rhs, temp)
        }
        HirExpr::Decision(decision) => decision.nodes.iter().any(|node| {
            expr_touches_temp(&node.test, temp)
                || decision_target_touches_temp(&node.truthy, temp)
                || decision_target_touches_temp(&node.falsy, temp)
        }),
        HirExpr::Call(call) => {
            expr_touches_temp(&call.callee, temp)
                || call.args.iter().any(|arg| expr_touches_temp(arg, temp))
        }
        HirExpr::TableConstructor(table) => {
            table.fields.iter().any(|field| match field {
                HirTableField::Array(expr) => expr_touches_temp(expr, temp),
                HirTableField::Record(field) => {
                    table_key_touches_temp(&field.key, temp)
                        || expr_touches_temp(&field.value, temp)
                }
            }) || table
                .trailing_multivalue
                .as_ref()
                .is_some_and(|tail| expr_touches_temp(tail.as_expr(), temp))
        }
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_touches_temp(&capture.value, temp)),
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_)
        | HirExpr::Int64(_)
        | HirExpr::UInt64(_)
        | HirExpr::Vector(_)
        | HirExpr::Complex { .. }
        | HirExpr::ParamRef(_)
        | HirExpr::LocalRef(_)
        | HirExpr::UpvalueRef(_)
        | HirExpr::GlobalRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

fn decision_target_touches_temp(
    target: &crate::hir::common::HirDecisionTarget,
    temp: TempId,
) -> bool {
    match target {
        crate::hir::common::HirDecisionTarget::Expr(expr) => expr_touches_temp(expr, temp),
        crate::hir::common::HirDecisionTarget::Node(_)
        | crate::hir::common::HirDecisionTarget::CurrentValue => false,
    }
}

fn table_key_touches_temp(key: &HirTableKey, temp: TempId) -> bool {
    match key {
        HirTableKey::Name(_) => false,
        HirTableKey::Expr(expr) => expr_touches_temp(expr, temp),
    }
}
