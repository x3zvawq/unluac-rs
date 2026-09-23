//! HIR 求值事件与表达式安全性的共享判断。
//!
//! HIR analyze 和 simplify 都会判断某个表达式是否能被挪动或折进别的表达式。
//! 这个文件只放跨 pass 共用、和具体恢复策略无关的谓词，避免求值序规则散落后漂移。
//! 原始值比较使用共享 `LuaValueSemantics`；本文件只负责 HIR 求值事件和 root relevance。
//! 方言固定的表达式槽能力同样在入口发布：例如 PUC 5.1 CONCAT 保留最右 operand，
//! 不代表中间 operand 或后续表达式仍拥有同一 root。

use super::common::{
    HirBinaryOpKind, HirCallExpr, HirCaptureMode, HirExpr, HirLValue, HirStmt, HirUnaryOpKind,
    HirValuePack,
};
use super::visit::HirVisitor;
use crate::decompile::DecompileDialect;
use crate::value_semantics::{LuaComparison, LuaLiteral, LuaValueSemantics};

fn node_has_original_operation(expr: &HirExpr) -> bool {
    matches!(expr, HirExpr::Binary(binary) if binary.source_site.is_some())
        || matches!(expr, HirExpr::Unary(unary) if unary.source_site.is_some())
        || matches!(expr, HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical)
            if logical.preserves_boolean_prewrite)
}

/// 共享表达式、写目标和调用的观察边界；遍历范围与额外语句事件由消费者决定。
///
/// 例如 generic-for header 的求值与隐式 dispatch 是不同事件，CFG 消费者不能把
/// 整个循环的观察能力提前到初始化；循环间隙分析则可保留自己的 cleanup 屏障。
pub(crate) struct HirEvalEffects<F> {
    safety: HirExprSafety,
    extra_stmt_effect: F,
    found: bool,
}

impl<F: FnMut(&HirStmt) -> bool> HirEvalEffects<F> {
    pub(crate) fn new(safety: HirExprSafety, extra_stmt_effect: F) -> Self {
        Self {
            safety,
            extra_stmt_effect,
            found: false,
        }
    }

    pub(crate) fn found(self) -> bool {
        self.found
    }
}

impl<F: FnMut(&HirStmt) -> bool> HirVisitor<'_> for HirEvalEffects<F> {
    fn is_complete(&self) -> bool {
        self.found
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        self.found |= matches!(stmt, HirStmt::GlobalDecl(_) | HirStmt::Close(_))
            || (self.extra_stmt_effect)(stmt);
    }

    fn visit_expr(&mut self, expr: &HirExpr) {
        self.found |= !matches!(expr, HirExpr::TableAccess(access) if access.metamethod_free)
            && self.safety.node_may_observe_gc_roots(expr);
    }

    fn visit_lvalue(&mut self, lvalue: &HirLValue) {
        self.found |= matches!(lvalue, HirLValue::Global(_) | HirLValue::TableAccess(_));
    }

    fn visit_call(&mut self, _call: &HirCallExpr) {
        self.found = true;
    }
}

/// 一个 HIR-origin local initializer 的逐槽 stack-root relevance 证明。
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HirInitializerRootProfile {
    slots: Vec<HirStackRootRelevance>,
}

impl HirInitializerRootProfile {
    /// 缺失或越界事实必须 fail closed。
    pub(crate) fn may_affect_collectable_lifetime(&self, slot: usize) -> bool {
        self.slots.get(slot) != Some(&HirStackRootRelevance::Irrelevant)
    }

    pub(crate) fn truncate(&mut self, len: usize) {
        self.slots.truncate(len);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum HirStackRootRelevance {
    /// 延长承接该结果的 stack slot 不会延长任何可回收对象的生命周期。
    Irrelevant,
    MayAffectCollectableLifetime,
}

pub(crate) fn initializer_root_profile(
    dialect: DecompileDialect,
    values: &HirValuePack,
    target_count: usize,
) -> HirInitializerRootProfile {
    let safety = HirExprSafety::for_dialect(dialect);
    HirInitializerRootProfile {
        slots: (0..target_count)
            .map(|slot| match values.fixed.get(slot) {
                Some(value) if safety.result_is_gc_inert(value) => {
                    HirStackRootRelevance::Irrelevant
                }
                Some(_) => HirStackRootRelevance::MayAffectCollectableLifetime,
                None if values.tail.is_some() => {
                    HirStackRootRelevance::MayAffectCollectableLifetime
                }
                None => HirStackRootRelevance::Irrelevant,
            })
            .collect(),
    }
}

/// 一次 HIR simplify 调用共享的表达式安全能力。
///
/// PUC Lua 与 Luau 的原始值不会和 table/userdata 通过 `__eq` 比较；LuaJIT cdata
/// 则可能在和 nil、boolean、number 或 string 比较时调用 ctype `__eq`。方言能力必须
/// 在递归入口固定，不能由局部 HIR 形状猜测。
#[derive(Debug, Clone, Copy)]
pub(crate) struct HirExprSafety {
    dynamic_primitive_equality_is_stable: bool,
    concat_preserves_rightmost_operand: bool,
    length_result_is_numeric: bool,
    values: LuaValueSemantics,
}

impl HirExprSafety {
    pub(crate) const fn for_dialect(dialect: DecompileDialect) -> Self {
        Self {
            concat_preserves_rightmost_operand: matches!(dialect, DecompileDialect::Lua51),
            length_result_is_numeric: matches!(dialect, DecompileDialect::Luau),
            dynamic_primitive_equality_is_stable: matches!(
                dialect,
                DecompileDialect::Lua51
                    | DecompileDialect::Lua52
                    | DecompileDialect::Lua53
                    | DecompileDialect::Lua54
                    | DecompileDialect::Lua55
                    | DecompileDialect::Luau
            ),
            values: LuaValueSemantics::for_dialect(dialect),
        }
    }

    /// PUC 5.1 的一次 CONCAT 保持 frame top，最右 operand 槽不被部分结果覆盖。
    /// 中间 operand 槽仍会被覆盖；该能力不覆盖另一条 CONCAT 或后续表达式求值。
    pub(crate) const fn concat_preserves_rightmost_operand(self) -> bool {
        self.concat_preserves_rightmost_operand
    }

    /// 只计算结果由目标 VM 合同固定的原始字面量比较。
    pub(crate) fn primitive_literal_comparison_value(
        self,
        op: HirBinaryOpKind,
        lhs: &HirExpr,
        rhs: &HirExpr,
    ) -> Option<bool> {
        let (op, lhs, rhs) = match op {
            HirBinaryOpKind::Eq => (LuaComparison::Eq, lhs, rhs),
            HirBinaryOpKind::Lt => (LuaComparison::Lt, lhs, rhs),
            HirBinaryOpKind::Le => (LuaComparison::Le, lhs, rhs),
            HirBinaryOpKind::Gt => (LuaComparison::Lt, rhs, lhs),
            HirBinaryOpKind::Ge => (LuaComparison::Le, rhs, lhs),
            _ => return None,
        };
        self.values
            .compare(op, primitive_literal(lhs)?, primitive_literal(rhs)?)
    }

    pub(crate) const fn values(self) -> LuaValueSemantics {
        self.values
    }

    fn equality_is_stable(self, op: HirBinaryOpKind, lhs: &HirExpr, rhs: &HirExpr) -> bool {
        if op != HirBinaryOpKind::Eq {
            return false;
        }
        let lhs_is_primitive = is_primitive_literal(lhs);
        let rhs_is_primitive = is_primitive_literal(rhs);
        // 候选拒绝[SemanticBarrier:Metamethod]：LuaJIT cdata 与原始值比较可调用 ctype `__eq`，删除或合并求值会改变 regress_391 的可观察调用次数。
        (lhs_is_primitive && rhs_is_primitive)
            || (self.dynamic_primitive_equality_is_stable && (lhs_is_primitive || rhs_is_primitive))
    }

    /// 当前一元 operator 本身是否可能执行用户代码或触发 GC。
    ///
    /// 子表达式事件由调用方按求值顺序单独处理；这里仅描述 operator 节点本身，避免把
    /// "not table[key]" 的 table lookup 重复算成 not 之后的新观察点。
    pub(crate) const fn unary_operator_may_observe_gc_roots(self, op: HirUnaryOpKind) -> bool {
        !matches!(op, HirUnaryOpKind::Not)
    }

    /// 当前二元 operator 本身是否可能执行用户代码或触发 GC。
    ///
    /// 原始字面量比较以及目标方言已证明稳定的 primitive equality 不会调用元方法；
    /// 其它 operator 保守保留 metamethod 观察边界。子表达式事件不在这里重复计数。
    pub(crate) fn binary_operator_may_observe_gc_roots(
        self,
        op: HirBinaryOpKind,
        lhs: &HirExpr,
        rhs: &HirExpr,
    ) -> bool {
        !primitive_literal_comparison_is_eventless(op, lhs, rhs)
            && !self.equality_is_stable(op, lhs, rhs)
    }
}

fn is_primitive_literal(expr: &HirExpr) -> bool {
    primitive_literal(expr).is_some()
}

fn primitive_literal(expr: &HirExpr) -> Option<LuaLiteral<'_>> {
    match expr {
        HirExpr::Nil => Some(LuaLiteral::Nil),
        HirExpr::Boolean(value) => Some(LuaLiteral::Boolean(*value)),
        HirExpr::Integer(value) => Some(LuaLiteral::Integer(*value)),
        HirExpr::Number(value) => Some(LuaLiteral::Number(*value)),
        HirExpr::String(value) => Some(LuaLiteral::String(value)),
        _ => None,
    }
}

/// 原始字面量比较是否保证完成且不触发用户代码。
///
/// 这里只证明求值事件，不承诺比较结果跨任意 Lua effect 保持不变；PUC Lua 字符串
/// 顺序会随 `LC_COLLATE` 改变，但同一求值点仍不调用 Lua 元方法也不抛错。
fn primitive_literal_comparison_is_eventless(
    op: HirBinaryOpKind,
    lhs: &HirExpr,
    rhs: &HirExpr,
) -> bool {
    if op == HirBinaryOpKind::Eq {
        return match (lhs, rhs) {
            (HirExpr::Integer(_), HirExpr::Integer(_))
            | (HirExpr::String(_), HirExpr::String(_))
            | (HirExpr::Boolean(_), HirExpr::Boolean(_))
            | (HirExpr::Nil, HirExpr::Nil) => true,
            (HirExpr::Number(lhs), HirExpr::Number(rhs)) => lhs.is_finite() && rhs.is_finite(),
            (HirExpr::Integer(_), HirExpr::Number(number))
            | (HirExpr::Number(number), HirExpr::Integer(_)) => number.is_finite(),
            _ => false,
        };
    }
    matches!(
        (op, lhs, rhs),
        (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge,
            HirExpr::Integer(_),
            HirExpr::Integer(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge,
            HirExpr::Number(_),
            HirExpr::Number(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge,
            HirExpr::Integer(_),
            HirExpr::Number(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge,
            HirExpr::Number(_),
            HirExpr::Integer(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le | HirBinaryOpKind::Gt | HirBinaryOpKind::Ge,
            HirExpr::String(_),
            HirExpr::String(_)
        )
    ) && match (lhs, rhs) {
        (HirExpr::Number(lhs), HirExpr::Number(rhs)) => lhs.is_finite() && rhs.is_finite(),
        _ => true,
    }
}

/// Luau 的 number 加法在两个原始数字操作数上走 VM 的 IEEE 754 binary64 路径，
/// 不查用户元方法。
///
/// `HirExpr::Integer` 也可能来自 Luau 的 `LOADN`，并不代表 PUC Lua 的
/// `lua_Integer` 语义；因此这里只在调用方已确认目标是 Luau 时使用，并先把两种
/// HIR 数字统一到 Luau 唯一的 `f64` 数值域。这样由宿主执行同一次 binary64 加法，
/// 会自然保留舍入、溢出和负零结果。
pub(crate) fn luau_literal_addition_value(lhs: &HirExpr, rhs: &HirExpr) -> Option<HirExpr> {
    fn number(expr: &HirExpr) -> Option<f64> {
        match expr {
            HirExpr::Integer(value) => Some(*value as f64),
            HirExpr::Number(value) => Some(*value),
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Neg => {
                number(&unary.expr).map(std::ops::Neg::neg)
            }
            _ => None,
        }
    }

    Some(HirExpr::Number(number(lhs)? + number(rhs)?))
}

impl HirExprSafety {
    /// 表达式能否删除：既没有必须保留的原操作，也不改变 Lua 可观察行为。
    pub(crate) fn is_discard_safe(self, expr: &HirExpr) -> bool {
        self.discard_safe(expr, true)
    }

    /// 表达式既可删除求值，也不承载必须交给 residual owner 的未解析诊断。
    pub(crate) fn is_discard_safe_without_residual(self, expr: &HirExpr) -> bool {
        self.discard_safe(expr, false)
    }

    /// 只检查当前节点；共享 visitor 负责子节点，不能把此结果当作整棵表达式的许可。
    pub(crate) fn node_is_discard_safe_without_residual(self, expr: &HirExpr) -> bool {
        !matches!(expr, HirExpr::Unresolved(_)) && self.node_is_discard_safe(expr)
    }

    /// 源码保留屏障不是 VM 观察事件；它的固定 vararg 读取在原事务内不检查 GC。
    pub(crate) fn node_may_observe_gc_roots(self, expr: &HirExpr) -> bool {
        !matches!(expr, HirExpr::CaptureInitializer(_))
            && !self.node_is_discard_safe_without_residual(expr)
    }

    /// 完整表达式的 VM 观察能力；移动根边界或失效 capture 事实并不删除表达式。
    pub(crate) fn may_observe_gc_roots(self, expr: &HirExpr) -> bool {
        let mut effects = HirEvalEffects::new(self, |_| false);
        super::visit::visit_expr(expr, &mut effects);
        effects.found()
    }

    fn discard_safe(self, expr: &HirExpr, allow_residual: bool) -> bool {
        if node_has_original_operation(expr)
            || !self.node_is_discard_safe(expr)
            || (!allow_residual && matches!(expr, HirExpr::Unresolved(_)))
        {
            return false;
        }
        match expr {
            HirExpr::Unary(unary) => self.discard_safe(&unary.expr, allow_residual),
            HirExpr::Binary(binary) => {
                self.discard_safe(&binary.lhs, allow_residual)
                    && self.discard_safe(&binary.rhs, allow_residual)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.discard_safe(&logical.lhs, allow_residual)
                    && self.discard_safe(&logical.rhs, allow_residual)
            }
            _ => true,
        }
    }

    /// 原操作的存在性独立于值域和 VM 观察事件；控制清理不能借恒值删除原检查。
    pub(crate) fn contains_original_operation(expr: &HirExpr) -> bool {
        struct Original(bool);
        impl HirVisitor<'_> for Original {
            fn is_complete(&self) -> bool {
                self.0
            }
            fn visit_expr(&mut self, expr: &HirExpr) {
                self.0 |= node_has_original_operation(expr);
            }
        }
        let mut original = Original(false);
        super::visit::visit_expr(expr, &mut original);
        original.0
    }

    fn node_is_discard_safe(self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::CaptureInitializer(_) => false,
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
            | HirExpr::VarArg
            | HirExpr::Unresolved(_)
            | HirExpr::LogicalAnd(_)
            | HirExpr::LogicalOr(_) => true,
            HirExpr::Unary(unary) => unary.op == HirUnaryOpKind::Not,
            HirExpr::Binary(binary) => {
                primitive_literal_comparison_is_eventless(binary.op, &binary.lhs, &binary.rhs)
                    || self.equality_is_stable(binary.op, &binary.lhs, &binary.rhs)
            }
            // 全局读取可触发环境表 __index；其余节点可能调用元方法、分配新身份或执行用户代码。
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_) => false,
        }
    }

    /// 表达式的单值结果是否不会承载可观察的 GC 资源生命周期。
    ///
    /// 这个谓词与“可丢弃求值”正交：`not` 和原始比较的结果恒为 boolean，primitive
    /// 字面量运算树的正常结果仍是 number/integer，但运算的错误与事件仍由 `is_discard_safe`
    /// 单独判断；逻辑表达式则可能直接返回任一操作数。String 常量由 chunk 常量表持有，
    /// 不会因为某个栈槽覆盖触发用户可观察的终结行为。LuaJIT 的 Int64/UInt64/Complex 虽由 GCcdata 表示，但
    /// BC_KCDATA 指向 proto 的 KGC 常量且 proto 遍历会持续标记它；Luau vector 同样先由
    /// proto 常量表持有。无论 vector 的宿主表示是内嵌值还是 boxed GC 对象，这些常量的
    /// 存活期都不由某个栈槽是否继续引用决定。
    pub(crate) fn result_is_gc_inert(self, expr: &HirExpr) -> bool {
        super::value_facts::value_facts_with(expr, &|expr| {
            // Luau 的 luaV_dolen 强制 __len 返回 number；其它 VM 不能套用此结果合同。
            (self.length_result_is_numeric
                && matches!(expr, HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Length))
            .then_some(crate::value_semantics::results::LuaValueFacts::NUMERIC)
        })
        .is_gc_inert()
    }

    /// 表达式是否可以在同一个无副作用逻辑区域内合并重复求值。
    ///
    /// 该谓词不等同于“可丢弃”：它只接纳不会调用元方法、不会读取动态环境、也不会
    /// 产生新对象身份的稳定值。代数改写仍需保证被跨越的其他表达式也满足本谓词。
    pub(crate) fn is_repeatable(self, expr: &HirExpr) -> bool {
        self.is_repeatable_with_context(expr, false)
    }

    /// 表达式作为普通单值操作数时，是否可以合并重复求值。
    ///
    /// `HirExpr::VarArg` 在这里已经由逻辑/比较等外层表达式收成首个值，不再具有
    /// value-pack tail 的展开宽度，因此同一函数调用中的两次读取稳定且无事件。
    pub(crate) fn is_repeatable_in_single_value_context(self, expr: &HirExpr) -> bool {
        self.is_repeatable_with_context(expr, true)
    }

    fn is_repeatable_with_context(self, expr: &HirExpr, single_value_vararg: bool) -> bool {
        match expr {
            HirExpr::CaptureInitializer(_) => false,
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
            | HirExpr::TempRef(_) => true,
            HirExpr::VarArg => single_value_vararg,
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                self.is_repeatable_with_context(&unary.expr, single_value_vararg)
            }
            HirExpr::Binary(binary)
                if primitive_literal_comparison_is_eventless(
                    binary.op,
                    &binary.lhs,
                    &binary.rhs,
                ) =>
            {
                true
            }
            HirExpr::Binary(binary)
                if self.equality_is_stable(binary.op, &binary.lhs, &binary.rhs) =>
            {
                self.is_repeatable_with_context(&binary.lhs, single_value_vararg)
                    && self.is_repeatable_with_context(&binary.rhs, single_value_vararg)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                !logical.preserves_boolean_prewrite
                    && self.is_repeatable_with_context(&logical.lhs, single_value_vararg)
                    && self.is_repeatable_with_context(&logical.rhs, single_value_vararg)
            }
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => false,
        }
    }

    /// 单值表达式的结果是否不会被夹在两次读取之间的任意 Lua 求值改写。
    ///
    /// local、param 与 upvalue 都可能被中间调用经 closure capture 写入；temp 是 HIR
    /// 已物化且 Lua 代码无法按名字访问的快照，vararg 则在函数入口固定。
    pub(crate) fn is_effect_invariant_in_single_value_context(self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::CaptureInitializer(_) => false,
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. }
            | HirExpr::TempRef(_)
            | HirExpr::VarArg => true,
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                self.is_effect_invariant_in_single_value_context(&unary.expr)
            }
            HirExpr::Binary(binary)
                if self
                    .primitive_literal_comparison_value(binary.op, &binary.lhs, &binary.rhs)
                    .is_some() =>
            {
                true
            }
            HirExpr::Binary(binary)
                if self.equality_is_stable(binary.op, &binary.lhs, &binary.rhs) =>
            {
                self.is_effect_invariant_in_single_value_context(&binary.lhs)
                    && self.is_effect_invariant_in_single_value_context(&binary.rhs)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.is_effect_invariant_in_single_value_context(&logical.lhs)
                    && self.is_effect_invariant_in_single_value_context(&logical.rhs)
            }
            HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => false,
        }
    }
}

pub(crate) fn expr_observes_eval_order(expr: &HirExpr) -> bool {
    match expr {
        HirExpr::CaptureInitializer(_) => true,
        HirExpr::GlobalRef(_) | HirExpr::TableAccess(_) | HirExpr::Call(_) => true,
        HirExpr::Unary(_) | HirExpr::Binary(_) | HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
            true
        }
        HirExpr::Decision(_) | HirExpr::TableConstructor(_) => true,
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
        | HirExpr::TempRef(_)
        | HirExpr::VarArg
        | HirExpr::Unresolved(_) => false,
    }
}

/// 临时值记录的结果是否必须保留在后续语句中的读取顺序。
///
/// local/upvalue/param/temp 读取本身不是可观察事件，但其结果是定义点的快照；若把这份
/// 快照挪到更晚的调用或 lookup 之后，来源 binding 可能已经被改写。
pub(crate) fn expr_requires_ordered_snapshot(expr: &HirExpr) -> bool {
    expr_observes_eval_order(expr)
        || matches!(expr, HirExpr::Closure(closure) if closure.captures.iter().any(|capture| {
            capture.mode == HirCaptureMode::ByValue
        }))
        || matches!(
            expr,
            HirExpr::ParamRef(_)
                | HirExpr::LocalRef(_)
                | HirExpr::UpvalueRef(_)
                | HirExpr::TempRef(_)
        )
}
