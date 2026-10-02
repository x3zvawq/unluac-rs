//! pinned Luau 数值循环展开使用的成本与单变量折扣。
//! HIR 和最终 AST 分别提供当前表达式，共享饱和、局部常量传播与阈值计算。

#[derive(Clone, Copy, Debug)]
pub(crate) struct Cost {
    base: usize,
    specialized: usize,
    constant: bool,
    specialized_constant: bool,
}

impl Cost {
    /// 参数折扣也不能删除的成本下界；超过最大收益阈值时无需估算其它表达式。
    pub fn blocks_unroll_at_max_profit(self, count: usize) -> bool {
        self.base.saturating_mul(count) > 75
    }
    /// 常量实参已经代入并重算完整函数后，使用 pinned 内联阈值；不套用循环展开折扣。
    pub fn permits_inline(self, baseline: Self) -> bool {
        let profit = (100 * (baseline.base + 3))
            .checked_div(self.base)
            .unwrap_or(300)
            .min(300);
        self.base <= 25 * profit / 100
    }

    /// 把所有输入都给予折扣时得到保守下界；仅用于最大收益阈值的拒绝证明。
    pub fn discounted_floor(self) -> Self {
        Self::fixed(self.specialized)
    }

    pub fn is_constant(self) -> bool {
        self.constant
    }
    pub fn fixed(value: usize) -> Self {
        Self {
            base: value.min(127),
            specialized: value.min(127),
            constant: false,
            specialized_constant: false,
        }
    }
    pub fn literal() -> Self {
        Self {
            base: 0,
            specialized: 0,
            constant: true,
            specialized_constant: true,
        }
    }
    pub fn variable(index: bool) -> Self {
        Self {
            base: 0,
            specialized: 0,
            constant: false,
            specialized_constant: index,
        }
    }
    pub fn local(self) -> Self {
        Self {
            base: 0,
            specialized: 0,
            ..self
        }
    }
    pub fn add(self, rhs: Self) -> Self {
        Self {
            base: (self.base + rhs.base).min(127),
            specialized: (self.specialized + rhs.specialized).min(127),
            constant: false,
            specialized_constant: false,
        }
    }
    pub fn multiply(self, factor: usize) -> Self {
        Self {
            base: self.base.saturating_mul(factor).min(127),
            specialized: self.specialized.saturating_mul(factor).min(127),
            constant: false,
            specialized_constant: false,
        }
    }
    pub fn fold(self, rhs: Self, logical: bool) -> Option<Self> {
        // 候选拒绝[ProofIncomplete]：原常量左臂可提前选择整支；没有其具体值时不估算该折叠。
        if logical && self.constant {
            return None;
        }
        let constant = self.constant && rhs.constant;
        let specialized_constant = self.specialized_constant && rhs.specialized_constant;
        Some(Self {
            base: (self.base + rhs.base + usize::from(!constant)).min(127),
            specialized: (self.specialized + rhs.specialized + usize::from(!specialized_constant))
                .min(127),
            constant,
            specialized_constant,
        })
    }
    pub fn argument(self) -> Self {
        // CostModel 在应用循环变量折扣前决定是否需要常量/local COPY。
        if self.base == 0 { Self::fixed(1) } else { self }
    }
    pub fn blocks_unroll(self, start: i64, limit: i64, step: i64) -> bool {
        let Some(trips) = trips(start, limit, step) else {
            return false;
        };
        if trips > 25 {
            return true;
        }
        // CostModel 的 baseline byte 已饱和时不再应用任何折扣。
        let specialized = if self.base == 127 {
            127
        } else {
            self.specialized
        };
        let unrolled = specialized * trips;
        let baseline = (self.base + 1) * trips;
        let profit = (100 * baseline)
            .checked_div(unrolled)
            .unwrap_or(300)
            .min(300);
        unrolled > 25 * profit / 100
    }
}

pub(crate) fn trips(start: i64, limit: i64, step: i64) -> Option<usize> {
    if step == 0
        || [start, limit, step]
            .iter()
            .any(|value| i32::try_from(*value).is_err())
    {
        return None;
    }
    let distance = if step > 0 {
        i128::from(limit) - i128::from(start)
    } else {
        i128::from(start) - i128::from(limit)
    };
    if distance < 0 {
        return None;
    }
    let count = distance / i128::from(step).abs() + 1;
    // 超出 pinned 编译器精确 tripCount 域时，不以不同的宿主整数宽度推算成本。
    (count <= i128::from(i32::MAX)).then_some(count as usize)
}

/// 常量内层循环的每次迭代至少收取一个固定控制成本；正文及其它操作只会增加成本。
/// 调用方只使用无条件执行的首个内层循环，不能从可能被常量分支裁掉的循环取下界。
pub(crate) fn mandatory_inner_loop_blocks_unroll(outer: usize, inner: usize) -> bool {
    inner.min(127).saturating_mul(outer) > 25 * 300 / 100
}
