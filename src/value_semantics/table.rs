//! HIR/AST 共用的表分配容量与模板初始化约束。
//!
//! 消费各层的字段语法投影和原分配事实，区分编译期常量与运行时值；不授权移动求值或根。

pub(crate) mod allocation;

#[derive(Clone, Copy)]
pub(crate) enum TableConstant {
    Nil,
    Boolean(bool),
    /// 常量语法已成立，但本查询不计算比较或条件选择的具体结果。
    Unknown,
    Number,
    String,
}

pub(crate) enum TableConstantExpr<'a, E> {
    Literal(TableConstant),
    Neg(&'a E),
    Not(&'a E),
    Numeric(&'a E, &'a E),
    Comparison(&'a E, &'a E),
    And(&'a E, &'a E),
    Or(&'a E, &'a E),
    Dynamic,
}

pub(crate) trait TableExpression: Sized {
    fn table_constant_expr(&self) -> TableConstantExpr<'_, Self>;

    fn table_integer_key(&self) -> Option<i64> {
        None
    }

    fn table_key(&self) -> Option<TableTemplateKey>;
}

/// 原模板中的稳定 key 身份。LuaJIT/Luau 数字使用 binary64 身份，字符串保留原始字节。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TableTemplateKey {
    Boolean(bool),
    Number(u64),
    String(crate::LuaString),
}

impl TableTemplateKey {
    pub(crate) fn number(value: f64) -> Self {
        Self::Number(if value == 0.0 {
            0.0_f64.to_bits()
        } else {
            value.to_bits()
        })
    }
}

/// 原分配对候选模板的约束，借用不可变原键集合，不依赖两层表达式表示。
#[derive(Clone, Copy)]
pub(crate) enum TableInitializationConstraint<'a> {
    Runtime,
    Template {
        /// 包含索引 0 的原槽数，不能把零索引模板与无数组模板视为同一容量。
        array_slots: u32,
        hash_keys: &'a std::collections::BTreeSet<TableTemplateKey>,
    },
}

pub(crate) enum TableFieldRef<'a, E> {
    Array { index: u32, value: &'a E },
    Record { key: &'a E, value: &'a E },
    Named(&'a str),
}

#[derive(Clone, Copy)]
pub(crate) enum TableRuntimeOperand {
    Key,
    Value,
}

/// 字段中的哪一个操作数必须保持运行时读取，才能保持原分配与扩容时点。
/// 原模板外的新静态键还会改变 hash 压力，不能根据源码数组字段数排除它。
/// 例如把 `{a, x, c}` 中的 x 替换为常量可能触发模板序列化，裁掉尾部 nil 槽。
pub(crate) fn runtime_table_operand<E: TableExpression>(
    constraint: TableInitializationConstraint<'_>,
    field: TableFieldRef<'_, E>,
) -> Option<TableRuntimeOperand> {
    use TableRuntimeOperand::{Key, Value};
    match constraint {
        TableInitializationConstraint::Runtime => match field {
            TableFieldRef::Array { value, .. } => table_constant_kind(value).map(|_| Value),
            TableFieldRef::Record { key, value } if initializes_template(key, value) => Some(
                if matches!(
                    table_constant_kind(key),
                    Some(TableConstant::String | TableConstant::Unknown)
                ) {
                    Key
                } else {
                    Value
                },
            ),
            TableFieldRef::Named(_) => Some(Key),
            _ => None,
        },
        TableInitializationConstraint::Template {
            array_slots,
            hash_keys,
        } => {
            let (index, value) = match field {
                TableFieldRef::Array { index, value } => (i64::from(index), value),
                TableFieldRef::Record { key, value } => {
                    if !initializes_template(key, value) {
                        return None;
                    }
                    let identity = key.table_key();
                    if identity.as_ref().is_some_and(|key| hash_keys.contains(key)) {
                        return None;
                    }
                    if let Some(index) = key.table_integer_key() {
                        // 新的稀疏整数也会增加 hash 压力，不能只检查候选数组范围。
                        if index < 0 {
                            return constant_can_be_non_nil(value).then_some(Value);
                        }
                        (index, value)
                    } else {
                        return Some(
                            if matches!(
                                table_constant_kind(key),
                                Some(TableConstant::String | TableConstant::Unknown)
                            ) {
                                Key
                            } else {
                                Value
                            },
                        );
                    }
                }
                TableFieldRef::Named(name) => {
                    return (!hash_keys.contains(&TableTemplateKey::String(name.into())))
                        .then_some(Key);
                }
            };
            (index >= i64::from(array_slots) && constant_can_be_non_nil(value)).then_some(Value)
        }
    }
}

pub(crate) fn constant_can_be_non_nil<E: TableExpression>(expr: &E) -> bool {
    table_constant_kind(expr).is_some_and(|value| !matches!(value, TableConstant::Nil))
}

pub(crate) fn integer_table_key(value: f64) -> Option<i64> {
    (value.is_finite()
        && value.fract() == 0.0
        && value.abs() <= ((1_u64 << f64::MANTISSA_DIGITS) as f64))
        .then_some(value as i64)
}

/// 候选模板序列化后保留的数组范围。动态写入不会清除模板初值；静态重复写最后生效。
/// Unknown 是可能折叠但无法确定是否为 nil 的值，不能据此签发精确容量。
pub(crate) fn template_array_capacity<'a, E: TableExpression + 'a>(
    fields: impl Iterator<Item = TableFieldRef<'a, E>>,
    array_fields: u32,
) -> Option<u32> {
    let mut values = std::collections::BTreeMap::new();
    for field in fields {
        let (key, value) = match field {
            TableFieldRef::Array { index, value } => (i64::from(index), value),
            TableFieldRef::Record { key, value } => {
                let Some(index) = key.table_integer_key() else {
                    if matches!(
                        table_constant_kind(key),
                        Some(TableConstant::Number | TableConstant::Unknown)
                    ) {
                        return None;
                    }
                    continue;
                };
                (index, value)
            }
            TableFieldRef::Named(_) => continue,
        };
        if key < 1 || key > i64::from(array_fields) {
            continue;
        }
        let non_nil = match table_constant_kind(value) {
            Some(TableConstant::Nil) => false,
            Some(TableConstant::Unknown) => return None,
            Some(_) => true,
            None => continue,
        };
        values.insert(key, non_nil);
    }
    Some(
        values
            .into_iter()
            .rev()
            .find_map(|(key, non_nil)| non_nil.then_some(key as u32))
            .unwrap_or(0),
    )
}

pub(crate) fn table_constant_kind<E: TableExpression>(expr: &E) -> Option<TableConstant> {
    use TableConstantExpr::*;
    match expr.table_constant_expr() {
        Literal(kind) => Some(kind),
        Neg(value) => matches!(table_constant_kind(value), Some(TableConstant::Number))
            .then_some(TableConstant::Number),
        Not(value) => Some(
            truthiness(table_constant_kind(value)?).map_or(TableConstant::Unknown, |truthy| {
                TableConstant::Boolean(!truthy)
            }),
        ),
        Numeric(lhs, rhs) => (matches!(table_constant_kind(lhs), Some(TableConstant::Number))
            && matches!(table_constant_kind(rhs), Some(TableConstant::Number)))
        .then_some(TableConstant::Number),
        Comparison(lhs, rhs) => {
            table_constant_kind(lhs)?;
            table_constant_kind(rhs)?;
            Some(TableConstant::Unknown)
        }
        And(lhs, rhs) => {
            let lhs = table_constant_kind(lhs)?;
            match truthiness(lhs) {
                Some(true) => table_constant_kind(rhs),
                Some(false) => Some(lhs),
                None => table_constant_kind(rhs).map(|_| TableConstant::Unknown),
            }
        }
        Or(lhs, rhs) => {
            let lhs = table_constant_kind(lhs)?;
            match truthiness(lhs) {
                Some(true) => Some(lhs),
                Some(false) => table_constant_kind(rhs),
                None => table_constant_kind(rhs).map(|_| TableConstant::Unknown),
            }
        }
        Dynamic => None,
    }
}

fn truthiness(value: TableConstant) -> Option<bool> {
    match value {
        TableConstant::Unknown => None,
        TableConstant::Nil | TableConstant::Boolean(false) => Some(false),
        _ => Some(true),
    }
}

pub(crate) fn initializes_template<E: TableExpression>(key: &E, value: &E) -> bool {
    match table_constant_kind(key) {
        Some(TableConstant::String | TableConstant::Unknown) => true,
        Some(TableConstant::Number | TableConstant::Boolean(_)) => {
            table_constant_kind(value).is_some()
        }
        _ => false,
    }
}
