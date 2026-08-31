//! 把等价的字符串索引收敛成字段访问。
//!
//! `obj["name"]` 和 `obj.name` 在 `name` 是合法标识符时语义等价。
//! 这里尽早把它规整成字段访问，是为了让后续的 alias inline / method sugar
//! 都能直接面对更稳定的 AST 形状，而不是各自重复理解字符串索引。

use crate::ast::DecompileDialect;

use super::super::common::{
    AstExpr, AstFieldAccess, AstIndexAccess, AstLValue, AstModule, is_lua_identifier_name,
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
    dialect: DecompileDialect,
) -> Option<AstFieldAccess> {
    let AstExpr::String(field_value) = &access.index else {
        return None;
    };
    // 候选拒绝[TargetConstraint]：Lua 裸字段名必须是目标方言可表示的 UTF-8 标识符；原始字节键只能保留 `obj["..."]`。
    let field = field_value.as_utf8()?;
    if !is_lua_identifier_name(field, dialect) {
        // 候选拒绝[TargetConstraint]：关键字或非法标识符不能生成 `obj.field`，否则目标方言源码无法解析。
        return None;
    }
    Some(AstFieldAccess {
        base: access.base.clone(),
        field: field.to_owned(),
    })
}
