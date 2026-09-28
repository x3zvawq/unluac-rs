//! 保存 PUC/Luau 表预分配事实，并查询候选源码所需容量。
//!
//! Transformer 提供原容量与计数规则，后层投影字段进行比较；批次写入协议由 SETLIST owner 证明。

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArraySizing {
    /// Lua 5.1–5.3 的浮点字节计数，容量可能因编码取整而扩大。
    FloatingByte,
    /// Lua 5.4–5.5 与 Luau 的精确数组计数。
    Exact,
}

/// 原预分配容量影响后续扩容及 #table，不能仅按最终字段值等价替换。
/// 例如逐项写入三个槽可能扩到四槽，与直接预分配三个槽的构造器不同。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TablePreallocation {
    pub array_capacity: u32,
    pub hash_capacity: u32,
    pub array_sizing: ArraySizing,
}

impl TablePreallocation {
    /// Luau 非空候选的官方编译器布局；空表的后续写入推断仍留给原构造区域。
    pub(crate) fn matches_luau<'a, E: super::TableExpression + 'a>(
        self,
        fields: impl Iterator<Item = super::TableFieldRef<'a, E>>,
        trailing_vararg: bool,
    ) -> bool {
        use super::TableFieldRef;
        let (mut arrays, mut records, mut named, mut indices) = (0, 0, 0, 0);
        for field in fields {
            match field {
                TableFieldRef::Array { .. } => arrays += 1,
                TableFieldRef::Named(_) => {
                    records += 1;
                    named += 1;
                }
                TableFieldRef::Record { key, .. } => {
                    records += 1;
                    if key.table_integer_key() == Some(indices + 1) {
                        indices += 1;
                    }
                }
            }
        }
        if arrays + records == 0 {
            return true;
        }
        if arrays == 0 && records == named {
            // 纯 hash NEWTABLE 保留 bracket 语法；有数组预分配时，全 named 也无法匹配。
            // DUPTABLE 使用独立的原键身份，不在此重建编译器模板去重规则。
            return false;
        }
        if arrays == 0 && records == named + indices as usize {
            arrays = indices as usize;
            records = named;
        }
        self.matches(arrays - usize::from(trailing_vararg), records)
    }

    pub(crate) fn floating_byte(array: u32, hash: u32) -> Option<Self> {
        Some(Self {
            array_capacity: decode_floating_byte(array)?,
            hash_capacity: hash_capacity(decode_floating_byte(hash)?)?,
            array_sizing: ArraySizing::FloatingByte,
        })
    }

    pub(crate) fn exact(array_capacity: u32, hash_log_plus_one: u8) -> Option<Self> {
        Some(Self {
            array_capacity,
            hash_capacity: if hash_log_plus_one == 0 {
                0
            } else {
                1_u32.checked_shl(u32::from(hash_log_plus_one - 1))?
            },
            array_sizing: ArraySizing::Exact,
        })
    }

    pub(crate) fn matches(self, array_fields: usize, record_fields: usize) -> bool {
        let (Ok(array), Ok(hash)) = (u32::try_from(array_fields), u32::try_from(record_fields))
        else {
            return false;
        };
        let array_capacity = match self.array_sizing {
            ArraySizing::Exact => Some(array),
            ArraySizing::FloatingByte => {
                let mut mantissa = u64::from(array);
                let mut shift = 0;
                while mantissa >= 16 {
                    mantissa = mantissa.div_ceil(2);
                    shift += 1;
                }
                u32::try_from(mantissa << shift).ok()
            }
        };
        array_capacity == Some(self.array_capacity)
            && hash_capacity(hash) == Some(self.hash_capacity)
    }
}

fn decode_floating_byte(value: u32) -> Option<u32> {
    let exponent = (value >> 3) & 31;
    if exponent == 0 {
        Some(value)
    } else {
        (value & 7).checked_add(8)?.checked_mul(1 << (exponent - 1))
    }
}

fn hash_capacity(entries: u32) -> Option<u32> {
    if entries == 0 {
        Some(0)
    } else {
        entries.checked_next_power_of_two()
    }
}
