//! 把等价的字符串索引与 constructor key 收敛成字段形式。
//!
//! `obj["name"]` 和 `obj.name` 在 `name` 是合法标识符时语义等价。
//! 这里尽早把它规整成字段访问，是为了让后续的 alias inline / method sugar
//! 都能直接面对更稳定的 AST 形状，而不是各自重复理解字符串索引。

use crate::ast::DecompileDialect;

use super::super::common::{
    AstExpr, AstFieldAccess, AstIndexAccess, AstLValue, AstModule, AstTableField, AstTableKey,
    is_lua_identifier_name,
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
    if !is_lua_identifier_name(field, dialect) {
        // 候选拒绝[TargetConstraint]：关键字或非法标识符不能生成 `obj.field`，否则目标方言源码无法解析。
        return None;
    }
    Some(field.to_owned())
}
