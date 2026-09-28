//! HIR 与 AST 共用的 Lua 原始值语义。
//!
//! 消费目标方言与字面量投影，统一数值、比较、结果域及表初始化查询；
//! 这些值事实不授权移动求值或删除物理根。

use crate::LuaString;
use crate::decompile::DecompileDialect;

pub(crate) mod results;
pub(crate) mod table;

#[derive(Clone, Copy, Debug)]
pub(crate) enum LuaLiteral<'a> {
    Nil,
    Boolean(bool),
    Integer(i64),
    Number(f64),
    String(&'a LuaString),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LuaComparison {
    Eq,
    Lt,
    Le,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MixedNumericMode {
    Unknown,
    ExactIntegerFloat,
    LuaJitBinary64,
    LuauBinary64,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct LuaValueSemantics {
    mixed_numeric_mode: MixedNumericMode,
    literal_string_order_is_binary: bool,
}

impl LuaValueSemantics {
    pub(crate) const fn for_dialect(dialect: DecompileDialect) -> Self {
        Self {
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
            literal_string_order_is_binary: dialect.literal_string_order_is_binary(),
        }
    }

    pub(crate) fn compare(
        self,
        op: LuaComparison,
        lhs: LuaLiteral<'_>,
        rhs: LuaLiteral<'_>,
    ) -> Option<bool> {
        primitive_literal_comparison_value(op, &lhs, &rhs, self)
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

    pub(crate) const fn distinguishes_integer_number_values(self) -> bool {
        matches!(self.mixed_numeric_mode, MixedNumericMode::ExactIntegerFloat)
    }
}

fn primitive_literal_comparison_value(
    op: LuaComparison,
    lhs: &LuaLiteral<'_>,
    rhs: &LuaLiteral<'_>,
    safety: LuaValueSemantics,
) -> Option<bool> {
    if op == LuaComparison::Eq {
        let value = match (lhs, rhs) {
            (LuaLiteral::Integer(lhs), LuaLiteral::Integer(rhs)) => Some(lhs == rhs),
            (LuaLiteral::Number(lhs), LuaLiteral::Number(rhs))
                if lhs.is_finite() && rhs.is_finite() =>
            {
                Some(lhs == rhs)
            }
            (LuaLiteral::String(lhs), LuaLiteral::String(rhs)) => Some(lhs == rhs),
            (LuaLiteral::Boolean(lhs), LuaLiteral::Boolean(rhs)) => Some(lhs == rhs),
            (LuaLiteral::Nil, LuaLiteral::Nil) => Some(true),
            (LuaLiteral::Integer(integer), LuaLiteral::Number(number))
            | (LuaLiteral::Number(number), LuaLiteral::Integer(integer)) => {
                safety.mixed_integer_number_equal(*integer, *number)
            }
            _ => None,
        };
        if value.is_some() {
            return value;
        }
        if matches!(
            (lhs, rhs),
            (LuaLiteral::Integer(_), LuaLiteral::Number(_))
                | (LuaLiteral::Number(_), LuaLiteral::Integer(_))
                | (LuaLiteral::Number(_), LuaLiteral::Number(_))
        ) || matches!(lhs, LuaLiteral::Number(value) if !value.is_finite())
            || matches!(rhs, LuaLiteral::Number(value) if !value.is_finite())
        {
            // 候选拒绝[TargetConstraint]：Integer/Number 的目标数值域或源码物化无法精确证明，不能按宿主表示直接判等。
            return None;
        }
        return Some(false);
    }
    let ordering = match (lhs, rhs) {
        (LuaLiteral::Integer(lhs), LuaLiteral::Integer(rhs)) => lhs.cmp(rhs),
        (LuaLiteral::Number(lhs), LuaLiteral::Number(rhs))
            if lhs.is_finite() && rhs.is_finite() =>
        {
            lhs.partial_cmp(rhs)?
        }
        (LuaLiteral::Integer(integer), LuaLiteral::Number(number)) => {
            safety.mixed_integer_number_ordering(*integer, *number)?
        }
        (LuaLiteral::Number(number), LuaLiteral::Integer(integer)) => safety
            .mixed_integer_number_ordering(*integer, *number)?
            .reverse(),
        (LuaLiteral::String(lhs), LuaLiteral::String(rhs)) => {
            // 候选拒绝[SemanticBarrier:Locale]：PUC Lua 的 `strcoll` 结果可被 `os.setlocale` 改写，regress_392 证明不能用宿主字节序替代。
            if !safety.literal_string_order_is_binary {
                return None;
            }
            lhs.cmp(rhs)
        }
        _ => return None,
    };
    match op {
        LuaComparison::Lt => Some(ordering == std::cmp::Ordering::Less),
        LuaComparison::Le => Some(ordering != std::cmp::Ordering::Greater),
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
