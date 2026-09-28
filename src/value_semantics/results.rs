//! HIR/AST 共用的正常单值结果域与短路合流。
//!
//! 消费当前语法及已证明的常量锚点，提供真假与结果集合查询，不授权删除求值或物理根。

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LuaValueFacts(u8);

impl LuaValueFacts {
    pub(crate) const EMPTY: Self = Self(0);
    pub(crate) const NIL: Self = Self(1);
    const FALSE: Self = Self(2);
    const TRUE: Self = Self(4);
    pub(crate) const NUMERIC: Self = Self(8);
    pub(crate) const STRING: Self = Self(16);
    pub(crate) const ANCHORED: Self = Self(32);
    pub(crate) const RESOURCE: Self = Self(64);
    pub(crate) const BOOLEAN: Self = Self(Self::FALSE.0 | Self::TRUE.0);
    pub(crate) const UNKNOWN: Self = Self(127);

    pub(crate) fn truthiness(self) -> Option<bool> {
        match (
            !self.restrict(false).is_empty(),
            !self.restrict(true).is_empty(),
        ) {
            (true, false) => Some(false),
            (false, true) => Some(true),
            _ => None,
        }
    }

    pub(crate) fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub(crate) fn is_boolean(self) -> bool {
        !self.is_empty() && self.0 & !Self::BOOLEAN.0 == 0
    }

    pub(crate) fn is_non_nil(self) -> bool {
        !self.is_empty() && self.0 & Self::NIL.0 == 0
    }

    pub(crate) fn is_gc_inert(self) -> bool {
        !self.is_empty() && self.0 & Self::RESOURCE.0 == 0
    }

    pub(crate) fn boolean(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }

    pub(crate) fn assuming_truthiness(value: bool) -> Self {
        Self::UNKNOWN.restrict(value)
    }

    pub(crate) fn restrict(self, truthy: bool) -> Self {
        let falsy = Self::NIL.0 | Self::FALSE.0;
        Self(self.0 & if truthy { !falsy } else { falsy })
    }

    pub(crate) fn join(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    pub(crate) fn logical_not(self) -> Self {
        self.truthiness()
            .map_or(Self::BOOLEAN, |v| Self::boolean(!v))
    }

    pub(crate) fn logical(self, take_rhs_when: bool, rhs: impl FnOnce() -> Self) -> Self {
        let retained = self.restrict(!take_rhs_when);
        if self.restrict(take_rhs_when).is_empty() {
            retained
        } else {
            retained.join(rhs())
        }
    }

    pub(crate) fn negated(self) -> Self {
        if self == Self::NUMERIC {
            Self::NUMERIC
        } else {
            Self::UNKNOWN
        }
    }

    pub(crate) fn string_length(self) -> Self {
        if self == Self::STRING {
            Self::NUMERIC
        } else {
            Self::UNKNOWN
        }
    }

    /// 仅用于普通数值算术；bitwise 转换失败可调用 primitive metatable，concat 无常量锚点。
    pub(crate) fn arithmetic(self, rhs: impl FnOnce() -> Self) -> Self {
        if self == Self::NUMERIC && rhs() == Self::NUMERIC {
            Self::NUMERIC
        } else {
            Self::UNKNOWN
        }
    }
}
