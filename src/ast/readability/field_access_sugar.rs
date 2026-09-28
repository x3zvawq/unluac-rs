//! 将合法字符串索引和构造器键整理为字段语法。
//!
//! 消费目标标识符规则与 HIR 分配许可，为后续 Readability 提供统一访问形状。

use crate::ast::DecompileDialect;

use super::super::common::{
    AstExpr, AstFieldAccess, AstIndexAccess, AstLValue, AstModule, AstTableField, AstTableKey,
};
use super::ReadabilityContext;
use super::walk::{self, AstRewritePass};

pub(super) fn apply(module: &mut AstModule, context: ReadabilityContext) -> bool {
    walk::rewrite_module(
        module,
        &mut FieldAccessSugarPass {
            dialect: context.target.version,
        },
    )
}

struct FieldAccessSugarPass {
    dialect: DecompileDialect,
}

impl AstRewritePass for FieldAccessSugarPass {
    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        match expr {
            AstExpr::IndexAccess(access) => {
                let Some(field_access) = field_access_from_index(access, self.dialect) else {
                    return false;
                };
                *expr = AstExpr::FieldAccess(Box::new(field_access));
                true
            }
            AstExpr::TableConstructor(table) => {
                if !table.allocation.permits_named_record_keys() {
                    return false;
                }
                let mut changed = false;
                for field in &mut table.fields {
                    let AstTableField::Record(record) = field else {
                        continue;
                    };
                    let AstTableKey::Expr(key) = &record.key else {
                        continue;
                    };
                    let Some(field_name) = field_name_from_key_expr(key, self.dialect) else {
                        continue;
                    };
                    record.key = AstTableKey::Name(field_name);
                    changed = true;
                }
                changed
            }
            _ => false,
        }
    }

    fn rewrite_lvalue(&mut self, lvalue: &mut AstLValue) -> bool {
        let AstLValue::IndexAccess(access) = lvalue else {
            return false;
        };
        let Some(field_access) = field_access_from_index(access, self.dialect) else {
            return false;
        };
        *lvalue = AstLValue::FieldAccess(Box::new(field_access));
        true
    }
}

fn field_access_from_index(
    access: &AstIndexAccess,
    dialect: DecompileDialect,
) -> Option<AstFieldAccess> {
    let field = field_name_from_key_expr(&access.index, dialect)?;
    Some(AstFieldAccess {
        base: access.base.clone(),
        field,
    })
}

fn field_name_from_key_expr(expr: &AstExpr, dialect: DecompileDialect) -> Option<String> {
    let AstExpr::String(field_value) = expr else {
        return None;
    };
    // 候选拒绝[TargetConstraint]：Lua 裸字段名必须是目标方言可表示的 UTF-8 标识符；原始字节键只能保留 `obj["..."]`。
    let field = field_value.as_utf8()?;
    if !dialect.is_identifier_name(field) {
        // 候选拒绝[TargetConstraint]：关键字或非法标识符不能生成 `obj.field`，否则目标方言源码无法解析。
        return None;
    }
    Some(field.to_owned())
}
