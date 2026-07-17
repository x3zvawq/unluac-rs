//! 这个子模块负责 temp-inline pass 的站点分类。
//!
//! 它依赖 HIR 当前语句/表达式形状，只回答某个 temp 首次被消费的位置属于 direct、callee、
//! condition 还是 loop-head，不会在这里执行内联。
//! 例如：`r0(1)` 会把 `r0` 的使用站点标成 `CallCallee`。

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
        HirStmt::TableSetList(set_list) => {
            find_site_in_expr(&set_list.base, temp, InlineSite::Direct)
                .or_else(|| find_site_in_exprs(&set_list.values, temp, InlineSite::Direct))
        }
        HirStmt::CallStmt(call_stmt) => {
            find_site_in_call(&call_stmt.call, temp, InlineSite::Direct)
        }
        HirStmt::Return(ret) => find_site_in_exprs(&ret.values, temp, InlineSite::ReturnValue),
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
            HirExpr::Decision(_)
            | HirExpr::Closure(_)
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
    let callee_site = if matches!(site, InlineSite::Direct) {
        InlineSite::CallCallee
    } else {
        InlineSite::Nested
    };
    find_site_in_expr(&call.callee, temp, callee_site)
        .or_else(|| find_site_in_exprs(&call.args, temp, InlineSite::CallArg))
}

fn find_site_in_lvalue(lvalue: &HirLValue, temp: TempId, site: InlineSite) -> Option<InlineSite> {
    match lvalue {
        HirLValue::Temp(target) if *target == temp => Some(site),
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
            find_site_in_expr(&logical.lhs, temp, child_site)
                .or_else(|| find_site_in_expr(&logical.rhs, temp, child_site))
        }
        HirExpr::Decision(decision) => decision.nodes.iter().find_map(|node| {
            find_site_in_expr(&node.test, temp, InlineSite::Nested)
                .or_else(|| find_site_in_decision_target(&node.truthy, temp, InlineSite::Nested))
                .or_else(|| find_site_in_decision_target(&node.falsy, temp, InlineSite::Nested))
        }),
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
    CallCallee,
    AccessBase,
    Condition,
    LoopCondition,
    LoopHead,
}

impl InlineSite {
    pub(super) fn allows(self, replacement: &HirExpr, options: ReadabilityOptions) -> bool {
        match self {
            Self::Direct => true,
            Self::CallCallee => true,
            Self::Nested => {
                expr_complexity(replacement) <= NESTED_INLINE_MAX_COMPLEXITY
                    && is_small_pure_nested_inline_expr(replacement)
            }
            Self::AccessBase => {
                self.complexity_limit(options)
                    .is_some_and(|limit| expr_complexity(replacement) <= limit)
                    && is_access_base_inline_expr(replacement)
            }
            // 条件头 / for 头属于源码结构骨架，保留少量低复杂度表达式能明显减少
            // 机械 temp 噪音；但这里仍然用固定的小阈值，避免把整坨复杂逻辑塞回控制头。
            Self::Condition | Self::LoopCondition | Self::LoopHead => {
                expr_complexity(replacement) <= CONTROL_HEAD_INLINE_MAX_COMPLEXITY
            }
            Self::ReturnValue | Self::Index | Self::CallArg => self
                .complexity_limit(options)
                .is_some_and(|limit| expr_complexity(replacement) <= limit),
        }
    }

    fn complexity_limit(self, options: ReadabilityOptions) -> Option<usize> {
        match self {
            Self::Direct
            | Self::Nested
            | Self::CallCallee
            | Self::Condition
            | Self::LoopCondition
            | Self::LoopHead => None,
            Self::ReturnValue => Some(options.return_inline_max_complexity),
            Self::Index => Some(options.index_inline_max_complexity),
            Self::CallArg => Some(options.args_inline_max_complexity),
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
            | Self::CallCallee
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
            | Self::CallCallee
            | Self::AccessBase => Self::Nested,
        }
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
