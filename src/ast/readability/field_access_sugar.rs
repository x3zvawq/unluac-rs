//! 把等价的字符串索引收敛成字段访问。
//!
//! `obj["name"]` 和 `obj.name` 在 `name` 是合法标识符时语义等价。
//! 这里尽早把它规整成字段访问，是为了让后续的 alias inline / method sugar
//! 都能直接面对更稳定的 AST 形状，而不是各自重复理解字符串索引。

use super::super::common::{
    AstDialectVersion, AstExpr, AstFieldAccess, AstIndexAccess, AstLValue, AstModule,
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
    dialect: AstDialectVersion,
}

impl AstRewritePass for FieldAccessSugarPass {
    fn rewrite_expr(&mut self, expr: &mut AstExpr) -> bool {
        let AstExpr::IndexAccess(access) = expr else {
            return false;
        };
        let Some(field_access) = field_access_from_index(access, self.dialect) else {
            return false;
        };
        *expr = AstExpr::FieldAccess(Box::new(field_access));
        true
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
    dialect: AstDialectVersion,
) -> Option<AstFieldAccess> {
    let AstExpr::String(field) = &access.index else {
        return None;
    };
    if !is_lua_identifier(field, dialect) {
        return None;
    }
    Some(AstFieldAccess {
        base: access.base.clone(),
        field: field.clone(),
    })
}

fn is_lua_identifier(name: &str, dialect: AstDialectVersion) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    if !chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric()) {
        return false;
    }
    !dialect.is_keyword(name)
}

#[cfg(test)]
mod tests;
