//! HIR 表达式求值安全性的共享判断。
//!
//! HIR analyze 和 simplify 都会判断某个表达式是否能被挪动或折进别的表达式。
//! 这个文件只放跨 pass 共用、和具体恢复策略无关的谓词，避免求值序规则散落后漂移。

use super::common::{HirBinaryOpKind, HirCaptureMode, HirExpr, HirUnaryOpKind};
use crate::decompile::DecompileDialect;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MixedNumericMode {
    Unknown,
    ExactIntegerFloat,
    LuaJitBinary64,
    LuauBinary64,
}

/// 一次 HIR simplify 调用共享的表达式安全能力。
///
/// PUC Lua 与 Luau 的原始值不会和 table/userdata 通过 `__eq` 比较；LuaJIT cdata
/// 则可能在和 nil、boolean、number 或 string 比较时调用 ctype `__eq`。方言能力必须
/// 在递归入口固定，不能由局部 HIR 形状猜测。
#[derive(Debug, Clone, Copy)]
pub(crate) struct HirExprSafety {
    dynamic_primitive_equality_is_stable: bool,
    literal_string_order_is_binary: bool,
    mixed_numeric_mode: MixedNumericMode,
}

impl HirExprSafety {
    pub(crate) const fn for_dialect(dialect: DecompileDialect) -> Self {
        Self {
            dynamic_primitive_equality_is_stable: matches!(
                dialect,
                DecompileDialect::Lua51
                    | DecompileDialect::Lua52
                    | DecompileDialect::Lua53
                    | DecompileDialect::Lua54
                    | DecompileDialect::Lua55
                    | DecompileDialect::Luau
            ),
            literal_string_order_is_binary: dialect.literal_string_order_is_binary(),
            mixed_numeric_mode: match dialect {
                DecompileDialect::Lua53 | DecompileDialect::Lua54 | DecompileDialect::Lua55 => {
                    MixedNumericMode::ExactIntegerFloat
                }
                DecompileDialect::Luajit => MixedNumericMode::LuaJitBinary64,
                DecompileDialect::Luau => MixedNumericMode::LuauBinary64,
                DecompileDialect::Auto | DecompileDialect::Lua51 | DecompileDialect::Lua52 => {
                    MixedNumericMode::Unknown
                }
            },
        }
    }

    /// 只计算结果由目标 VM 合同固定的原始字面量比较。
    pub(crate) fn primitive_literal_comparison_value(
        self,
        op: HirBinaryOpKind,
        lhs: &HirExpr,
        rhs: &HirExpr,
    ) -> Option<bool> {
        primitive_literal_comparison_value(op, lhs, rhs, self)
    }

    pub(crate) fn mixed_integer_number_ordering(
        self,
        integer: i64,
        number: f64,
    ) -> Option<std::cmp::Ordering> {
        mixed_integer_number_ordering(self.mixed_numeric_mode, integer, number)
    }

    pub(crate) fn mixed_integer_number_equal(self, integer: i64, number: f64) -> Option<bool> {
        mixed_integer_number_equal(self.mixed_numeric_mode, integer, number)
    }

    pub(crate) const fn literal_string_order_is_binary(self) -> bool {
        self.literal_string_order_is_binary
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
}

fn is_primitive_literal(expr: &HirExpr) -> bool {
    matches!(
        expr,
        HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
    )
}

/// 计算目标方言能够证明不会触发元方法的原始字面量比较。
///
/// 混合 Integer/Number 只在 `HirExprSafety` 已固定的数值域内使用精确算法；调用方只能
/// 把 `Some` 当作可删除求值的常量事实，`None` 必须继续保留原表达式。
/// dynamic/primitive equality 是否会触发元方法由 [`HirExprSafety`] 的方言能力判定；
/// 这个 helper 只负责完全由字面量决定结果的比较。
fn primitive_literal_comparison_value(
    op: HirBinaryOpKind,
    lhs: &HirExpr,
    rhs: &HirExpr,
    safety: HirExprSafety,
) -> Option<bool> {
    if op == HirBinaryOpKind::Eq {
        let value = match (lhs, rhs) {
            (HirExpr::Integer(lhs), HirExpr::Integer(rhs)) => Some(lhs == rhs),
            (HirExpr::Number(lhs), HirExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
                Some(lhs == rhs)
            }
            (HirExpr::String(lhs), HirExpr::String(rhs)) => Some(lhs == rhs),
            (HirExpr::Boolean(lhs), HirExpr::Boolean(rhs)) => Some(lhs == rhs),
            (HirExpr::Nil, HirExpr::Nil) => Some(true),
            (HirExpr::Integer(integer), HirExpr::Number(number))
            | (HirExpr::Number(number), HirExpr::Integer(integer)) => {
                safety.mixed_integer_number_equal(*integer, *number)
            }
            _ => None,
        };
        if value.is_some() {
            return value;
        }
        if matches!(
            (lhs, rhs),
            (HirExpr::Integer(_), HirExpr::Number(_))
                | (HirExpr::Number(_), HirExpr::Integer(_))
                | (HirExpr::Number(_), HirExpr::Number(_))
        ) || matches!(lhs, HirExpr::Number(value) if !value.is_finite())
            || matches!(rhs, HirExpr::Number(value) if !value.is_finite())
        {
            // 候选拒绝[TargetConstraint]：Integer/Number 的目标数值域或源码物化无法精确证明，不能按宿主表示直接判等。
            return None;
        }
        if is_primitive_literal(lhs) && is_primitive_literal(rhs) {
            return Some(false);
        }
        // 候选拒绝[TargetConstraint]：cdata、vector 与 complex 的 equality 及源码物化是方言专属语义，不能按普通 primitive 类型不匹配处理。
        return None;
    }
    let ordering = match (lhs, rhs) {
        (HirExpr::Integer(lhs), HirExpr::Integer(rhs)) => lhs.cmp(rhs),
        (HirExpr::Number(lhs), HirExpr::Number(rhs)) if lhs.is_finite() && rhs.is_finite() => {
            lhs.partial_cmp(rhs)?
        }
        (HirExpr::Integer(integer), HirExpr::Number(number)) => {
            safety.mixed_integer_number_ordering(*integer, *number)?
        }
        (HirExpr::Number(number), HirExpr::Integer(integer)) => safety
            .mixed_integer_number_ordering(*integer, *number)?
            .reverse(),
        (HirExpr::String(lhs), HirExpr::String(rhs)) => {
            // 候选拒绝[SemanticBarrier:Locale]：PUC Lua 的 `strcoll` 结果可被 `os.setlocale` 改写，regress_392 证明不能用宿主字节序替代。
            if !safety.literal_string_order_is_binary {
                return None;
            }
            lhs.cmp(rhs)
        }
        _ => return None,
    };
    match op {
        HirBinaryOpKind::Lt => Some(ordering == std::cmp::Ordering::Less),
        HirBinaryOpKind::Le => Some(ordering != std::cmp::Ordering::Greater),
        _ => None,
    }
}

fn mixed_integer_number_equal(mode: MixedNumericMode, integer: i64, number: f64) -> Option<bool> {
    if !number.is_finite() {
        return None;
    }
    match mode {
        MixedNumericMode::ExactIntegerFloat => {
            const UPPER: f64 = 9_223_372_036_854_775_808.0;
            Some(
                number.fract() == 0.0
                    && number >= i64::MIN as f64
                    && number < UPPER
                    && number as i64 == integer,
            )
        }
        MixedNumericMode::LuaJitBinary64 | MixedNumericMode::LuauBinary64 => {
            const MAX_EXACT: i64 = 9_007_199_254_740_992;
            let max_integer = if mode == MixedNumericMode::LuaJitBinary64 {
                i64::from(i32::MAX)
            } else {
                MAX_EXACT
            };
            let min_integer = if mode == MixedNumericMode::LuaJitBinary64 {
                i64::from(i32::MIN)
            } else {
                -MAX_EXACT
            };
            (integer >= min_integer && integer <= max_integer).then_some(integer as f64 == number)
        }
        MixedNumericMode::Unknown => {
            // 候选拒绝[TargetConstraint]：目标未声明 Integer/Number 的共同数值域，不能证明比较结果。
            None
        }
    }
}

fn mixed_integer_number_ordering(
    mode: MixedNumericMode,
    integer: i64,
    number: f64,
) -> Option<std::cmp::Ordering> {
    if !number.is_finite() {
        return None;
    }
    match mode {
        MixedNumericMode::LuaJitBinary64 | MixedNumericMode::LuauBinary64 => {
            const MAX_EXACT: i64 = 9_007_199_254_740_992;
            let max_integer = if mode == MixedNumericMode::LuaJitBinary64 {
                i64::from(i32::MAX)
            } else {
                MAX_EXACT
            };
            let min_integer = if mode == MixedNumericMode::LuaJitBinary64 {
                i64::from(i32::MIN)
            } else {
                -MAX_EXACT
            };
            (integer >= min_integer && integer <= max_integer)
                .then(|| (integer as f64).partial_cmp(&number))
                .flatten()
        }
        MixedNumericMode::ExactIntegerFloat => {
            const UPPER: f64 = 9_223_372_036_854_775_808.0;
            const LOWER: f64 = -9_223_372_036_854_775_808.0;
            if number >= UPPER {
                return Some(std::cmp::Ordering::Less);
            }
            if number < LOWER {
                return Some(std::cmp::Ordering::Greater);
            }
            let ceil = number.ceil();
            if ceil >= UPPER {
                return Some(std::cmp::Ordering::Less);
            }
            let floor = number.floor();
            if floor < LOWER {
                return Some(std::cmp::Ordering::Greater);
            }
            if integer < ceil as i64 {
                Some(std::cmp::Ordering::Less)
            } else if integer > floor as i64 {
                Some(std::cmp::Ordering::Greater)
            } else {
                Some(std::cmp::Ordering::Equal)
            }
        }
        MixedNumericMode::Unknown => {
            // 候选拒绝[TargetConstraint]：目标未声明 Integer/Number 的共同数值域，不能证明比较结果。
            None
        }
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
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le,
            HirExpr::Integer(_),
            HirExpr::Integer(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le,
            HirExpr::Number(_),
            HirExpr::Number(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le,
            HirExpr::Integer(_),
            HirExpr::Number(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le,
            HirExpr::Number(_),
            HirExpr::Integer(_)
        ) | (
            HirBinaryOpKind::Lt | HirBinaryOpKind::Le,
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
    /// 表达式的求值能否在不改变 Lua 可观察行为的前提下被删除。
    pub(crate) fn is_discard_safe(self, expr: &HirExpr) -> bool {
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
            | HirExpr::VarArg
            | HirExpr::Unresolved(_) => true,
            HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
                self.is_discard_safe(&unary.expr)
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
                self.is_discard_safe(&binary.lhs) && self.is_discard_safe(&binary.rhs)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.is_discard_safe(&logical.lhs) && self.is_discard_safe(&logical.rhs)
            }
            // 全局读取可触发环境表 __index；其余节点可能调用元方法、分配新身份或执行用户代码。
            HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Unary(_)
            | HirExpr::Binary(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_) => false,
        }
    }

    /// 表达式既可删除求值，也不承载必须交给 residual owner 的未解析诊断。
    pub(crate) fn is_discard_safe_without_residual(self, expr: &HirExpr) -> bool {
        if !self.is_discard_safe(expr) {
            return false;
        }
        match expr {
            HirExpr::Unresolved(_) => false,
            HirExpr::Unary(unary) => self.is_discard_safe_without_residual(&unary.expr),
            HirExpr::Binary(binary) => {
                self.is_discard_safe_without_residual(&binary.lhs)
                    && self.is_discard_safe_without_residual(&binary.rhs)
            }
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.is_discard_safe_without_residual(&logical.lhs)
                    && self.is_discard_safe_without_residual(&logical.rhs)
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
            | HirExpr::TempRef(_)
            | HirExpr::VarArg => true,
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
    /// 这个谓词比“可丢弃求值”更窄：`not` 和原始比较的结果恒为 boolean，逻辑表达式
    /// 则可能直接返回任一操作数。String 常量由 chunk 常量表持有，不会因为某个栈槽覆盖
    /// 触发用户可观察的终结行为。LuaJIT 的 Int64/UInt64/Complex 虽由 GCcdata 表示，但
    /// BC_KCDATA 指向 proto 的 KGC 常量且 proto 遍历会持续标记它；Luau vector 同样先由
    /// proto 常量表持有。无论 vector 的宿主表示是内嵌值还是 boxed GC 对象，这些常量的
    /// 存活期都不由某个栈槽是否继续引用决定。
    pub(crate) fn result_is_gc_inert(self, expr: &HirExpr) -> bool {
        match expr {
            HirExpr::Nil
            | HirExpr::Boolean(_)
            | HirExpr::Integer(_)
            | HirExpr::Number(_)
            | HirExpr::String(_)
            | HirExpr::Int64(_)
            | HirExpr::UInt64(_)
            | HirExpr::Vector(_)
            | HirExpr::Complex { .. } => true,
            HirExpr::Unary(_) | HirExpr::Binary(_) => self.is_discard_safe(expr),
            HirExpr::LogicalAnd(logical) | HirExpr::LogicalOr(logical) => {
                self.result_is_gc_inert(&logical.lhs) && self.result_is_gc_inert(&logical.rhs)
            }
            HirExpr::ParamRef(_)
            | HirExpr::LocalRef(_)
            | HirExpr::UpvalueRef(_)
            | HirExpr::TempRef(_)
            | HirExpr::GlobalRef(_)
            | HirExpr::TableAccess(_)
            | HirExpr::Decision(_)
            | HirExpr::Call(_)
            | HirExpr::VarArg
            | HirExpr::TableConstructor(_)
            | HirExpr::Closure(_)
            | HirExpr::Unresolved(_) => false,
        }
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
                self.is_repeatable_with_context(&logical.lhs, single_value_vararg)
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
        HirExpr::GlobalRef(_) | HirExpr::TableAccess(_) | HirExpr::Call(_) => true,
        HirExpr::Unary(_) | HirExpr::Binary(_) | HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => {
            true
        }
        HirExpr::Decision(_) | HirExpr::TableConstructor(_) => true,
        HirExpr::Closure(closure) => closure
            .captures
            .iter()
            .any(|capture| expr_observes_eval_order(&capture.value)),
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
                && expr_requires_ordered_snapshot(&capture.value)
        }))
        || matches!(
            expr,
            HirExpr::ParamRef(_)
                | HirExpr::LocalRef(_)
                | HirExpr::UpvalueRef(_)
                | HirExpr::TempRef(_)
        )
}
