//! 将当前 AST 字段投影到共享表初始化约束。
//!
//! 消费 HIR 的分配容量与原键身份，供 AST 改写检查候选布局。

use super::common::{
    AstBinaryOpKind, AstExpr, AstTableConstructor, AstTableField, AstTableKey, AstUnaryOpKind,
};
use crate::value_semantics::table::{
    TableConstant as Kind, TableConstantExpr as Expr, TableExpression, TableFieldRef,
    runtime_table_operand,
};

/// 新增字段与 HIR lowering 共用原分配对命名语法的许可，不能在 sugar 中改回裸键。
pub(crate) fn record_key(allocation: &crate::hir::HirTableAllocation, name: String) -> AstTableKey {
    if allocation.permits_named_record_keys() {
        AstTableKey::Name(name)
    } else {
        AstTableKey::Expr(AstExpr::String(name.into()))
    }
}

fn field_ref<'a>(field: &'a AstTableField, next_array: &mut u32) -> TableFieldRef<'a, AstExpr> {
    match field {
        AstTableField::Array(value) => {
            *next_array += 1;
            TableFieldRef::Array {
                index: *next_array,
                value,
            }
        }
        AstTableField::Record(record) => match &record.key {
            AstTableKey::Name(name) => TableFieldRef::Named(name),
            AstTableKey::Expr(key) => TableFieldRef::Record {
                key,
                value: &record.value,
            },
        },
    }
}

/// 字段扩展事务完成后统一投影候选大小，不在每次追加时重复扫描整个构造器。
pub(crate) fn matches_preallocation(table: &AstTableConstructor) -> bool {
    if let Some(constraint) = table.allocation.initialization_constraint() {
        let mut next_array = 0;
        if table.fields.iter().any(|field| {
            runtime_table_operand(constraint, field_ref(field, &mut next_array)).is_some()
        }) {
            // 候选拒绝[SemanticBarrier:TableInitialization]：字段扩展不能把原模板外的
            // 键放进编译期模板。AST 没有新增原运行时操作数的权限，消费 HIR 分配约束。
            return false;
        }
    }
    if let crate::hir::HirTableAllocation::Luau(allocation) = table.allocation {
        let mut next_array = 0;
        return allocation.matches_luau(
            table
                .fields
                .iter()
                .map(|field| field_ref(field, &mut next_array)),
            matches!(
                table.fields.last(),
                Some(AstTableField::Array(AstExpr::VarArg))
            ),
        );
    }
    let arrays = table
        .fields
        .iter()
        .filter(|field| matches!(field, AstTableField::Array(_)))
        .count();
    table
        .allocation
        .batched_capacity_matches(arrays, table.fields.len() - arrays)
        .unwrap_or(true)
}

pub(crate) fn introduces_runtime_table_operand(
    before: &AstTableConstructor,
    after: &AstTableConstructor,
) -> bool {
    let Some(constraint) = before.allocation.initialization_constraint() else {
        return false;
    };
    let (mut before_array, mut after_array) = (0, 0);
    before
        .fields
        .iter()
        .zip(&after.fields)
        .any(|(before, after)| {
            let before = runtime_table_operand(constraint, field_ref(before, &mut before_array));
            let after = runtime_table_operand(constraint, field_ref(after, &mut after_array));
            before.is_none() && after.is_some()
        })
}

impl TableExpression for AstExpr {
    fn table_key(&self) -> Option<crate::value_semantics::table::TableTemplateKey> {
        use crate::value_semantics::table::TableTemplateKey as Key;
        match self {
            Self::Boolean(value) => Some(Key::Boolean(*value)),
            Self::Integer(value) => Some(Key::number(*value as f64)),
            Self::Number(value) => Some(Key::number(*value)),
            Self::String(value) => Some(Key::String(value.clone())),
            Self::SingleValue(value) => value.table_key(),
            _ => None,
        }
    }

    fn table_integer_key(&self) -> Option<i64> {
        match self {
            Self::Integer(value) => Some(*value),
            Self::Number(value) => crate::value_semantics::table::integer_table_key(*value),
            Self::SingleValue(value) => value.table_integer_key(),
            _ => None,
        }
    }

    fn table_constant_expr(&self) -> Expr<'_, Self> {
        match self {
            Self::Nil => Expr::Literal(Kind::Nil),
            Self::Boolean(value) => Expr::Literal(Kind::Boolean(*value)),
            Self::Integer(_) | Self::Number(_) => Expr::Literal(Kind::Number),
            Self::String(_) => Expr::Literal(Kind::String),
            Self::SingleValue(value) => value.table_constant_expr(),
            Self::Unary(unary) => match unary.op {
                AstUnaryOpKind::Neg => Expr::Neg(&unary.expr),
                AstUnaryOpKind::Not => Expr::Not(&unary.expr),
                _ => Expr::Dynamic,
            },
            Self::Binary(binary)
                if matches!(
                    binary.op,
                    AstBinaryOpKind::Add
                        | AstBinaryOpKind::Sub
                        | AstBinaryOpKind::Mul
                        | AstBinaryOpKind::Div
                        | AstBinaryOpKind::Mod
                        | AstBinaryOpKind::Pow
                ) =>
            {
                Expr::Numeric(&binary.lhs, &binary.rhs)
            }
            Self::LogicalAnd(logical) => Expr::And(&logical.lhs, &logical.rhs),
            Self::Binary(binary)
                if matches!(
                    binary.op,
                    AstBinaryOpKind::Eq
                        | AstBinaryOpKind::Lt
                        | AstBinaryOpKind::Le
                        | AstBinaryOpKind::Gt
                        | AstBinaryOpKind::Ge
                ) =>
            {
                Expr::Comparison(&binary.lhs, &binary.rhs)
            }
            Self::LogicalOr(logical) => Expr::Or(&logical.lhs, &logical.rhs),
            _ => Expr::Dynamic,
        }
    }
}
