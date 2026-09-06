//! HIR 与 AST 共用的正常单值结果域及短路合流。
//!
//! 两层只投影当前表达式的种类与已证明的常量锚点，Lua 的真假选择、布尔结果和
//! 结果集合查询由此处统一。例如 `unknown and false` 的结果包含 nil，不能当作
//! boolean；`unknown or true` 则恒真，但仍可能返回对象，不能据此删除物理根。
//! ANCHORED 需要消费者证明常量锚点，不能从生成源码的构造调用反推。正常结果事实
//! 不证明求值无事件、可移动或不会出错，也不携带任何跨改写的节点身份。

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
