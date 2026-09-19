//! 从最终表达式提取形状和调用候选名；这些只是阅读提示，不作为类型或改写证明。

use crate::ast::naming::{NameSource, support::normalize_identifier};
use crate::ast::{AstBinaryOpKind, AstExpr, AstLValue, AstNameRef, AstTableField, AstUnaryOpKind};

/// 仅真正开放的尾调用/vararg 可以为后续多个 binding 提供初始化提示。
pub(super) fn initializer_for_slot(values: &[AstExpr], index: usize) -> Option<&AstExpr> {
    values.get(index).or_else(|| {
        values.last().filter(|expr| {
            matches!(
                expr,
                AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
            )
        })
    })
}

pub(super) fn field_name(target: &AstLValue) -> Option<&str> {
    match target {
        AstLValue::FieldAccess(access) => Some(&access.field),
        AstLValue::IndexAccess(access) => match &access.index {
            AstExpr::String(key) => key.as_utf8(),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn candidate_from_expr(expr: &AstExpr) -> Option<(String, NameSource)> {
    let (name, source) = match expr {
        AstExpr::Boolean(_) => ("ok".to_owned(), NameSource::BoolShape),
        AstExpr::LogicalAnd(_) | AstExpr::LogicalOr(_) => {
            // and/or 返回操作数，只有值域已证明为 boolean 时才给布尔名字。
            return crate::ast::readability::expr_is_boolean_valued(expr)
                .then(|| ("ok".to_owned(), NameSource::BoolShape));
        }
        AstExpr::FieldAccess(access) => {
            (normalize_identifier(&access.field)?, NameSource::FieldName)
        }
        AstExpr::IndexAccess(access) => {
            let name = if let AstExpr::String(key) = &access.index {
                normalize_identifier(key.as_utf8()?)?
            } else {
                index_base_name(&access.base)?
            };
            (name, NameSource::FieldName)
        }
        AstExpr::TableConstructor(table) => (
            if !table.fields.is_empty()
                && table
                    .fields
                    .iter()
                    .all(|field| matches!(field, AstTableField::Array(_)))
            {
                "arr"
            } else {
                "tbl"
            }
            .to_owned(),
            NameSource::TableShape,
        ),
        AstExpr::FunctionExpr(_) => ("fn".to_owned(), NameSource::FunctionShape),
        AstExpr::Call(call) => {
            if matches!(&call.callee, AstExpr::Var(AstNameRef::Global(global)) if global.text == "require")
                && let [AstExpr::String(path)] = call.args.as_slice()
                && let Some(path) = path.as_utf8()
                && let Some(leaf) = path.rsplit(['.', '/', '\\']).find(|part| !part.is_empty())
                && let Some(name) = normalize_identifier(leaf)
            {
                return Some((name, NameSource::ModulePath));
            }
            call_result_name(&call.callee)
                .map(|name| (name, NameSource::CallResult))
                .unwrap_or_else(|| ("result".to_owned(), NameSource::ResultShape))
        }
        AstExpr::MethodCall(call) => (
            result_from_verb(&call.method).unwrap_or_else(|| "result".to_owned()),
            NameSource::CallResult,
        ),
        AstExpr::SingleValue(inner) => return candidate_from_expr(inner),
        AstExpr::VarArg => ("value".to_owned(), NameSource::ResultShape),
        AstExpr::Integer(_) | AstExpr::Number(_) | AstExpr::Int64(_) | AstExpr::UInt64(_) => {
            ("num".to_owned(), NameSource::NumberShape)
        }
        AstExpr::String(_) => ("str".to_owned(), NameSource::StringShape),
        AstExpr::Unary(unary) => match unary.op {
            AstUnaryOpKind::Length => ("length".to_owned(), NameSource::NumberShape),
            AstUnaryOpKind::Neg | AstUnaryOpKind::BitNot => {
                ("num".to_owned(), NameSource::NumberShape)
            }
            AstUnaryOpKind::Not => ("ok".to_owned(), NameSource::BoolShape),
        },
        AstExpr::Binary(binary) => match binary.op {
            AstBinaryOpKind::Concat => ("str".to_owned(), NameSource::StringShape),
            AstBinaryOpKind::Eq
            | AstBinaryOpKind::Lt
            | AstBinaryOpKind::Le
            | AstBinaryOpKind::Gt
            | AstBinaryOpKind::Ge => ("ok".to_owned(), NameSource::BoolShape),
            _ => ("num".to_owned(), NameSource::NumberShape),
        },
        AstExpr::Var(AstNameRef::Global(global)) => {
            (normalize_identifier(&global.text)?, NameSource::FieldName)
        }
        _ => return None,
    };
    Some((name, source))
}

fn call_result_name(callee: &AstExpr) -> Option<String> {
    match callee {
        AstExpr::FieldAccess(access) => {
            result_from_verb(&access.field).or_else(|| normalize_identifier(&access.field))
        }
        AstExpr::Var(AstNameRef::Global(global)) => result_from_verb(&global.text),
        _ => None,
    }
}

// 只裁掉明确的词边界；getaway 不能被解释成 get + away。标准库 getenv 是明确的例外。
fn result_from_verb(name: &str) -> Option<String> {
    if name == "getenv" {
        return Some("env".to_owned());
    }
    for prefix in [
        "get", "find", "load", "create", "fetch", "read", "make", "build", "parse", "new",
    ] {
        let Some(rest) = name.strip_prefix(prefix) else {
            continue;
        };
        let rest = if let Some(rest) = rest.strip_prefix('_') {
            rest
        } else if rest.starts_with(|c: char| c.is_ascii_uppercase()) {
            rest
        } else {
            continue;
        };
        let mut chars = rest.chars();
        let first = chars.next()?;
        let candidate = format!("{}{}", first.to_ascii_lowercase(), chars.as_str());
        return normalize_identifier(&candidate);
    }
    None
}

fn index_base_name(base: &AstExpr) -> Option<String> {
    match base {
        AstExpr::FieldAccess(access) => Some(singularize(&access.field)),
        AstExpr::IndexAccess(access) => index_base_name(&access.base),
        AstExpr::Var(AstNameRef::Global(global)) => normalize_identifier(&global.text),
        AstExpr::Var(_) => Some("item".to_owned()),
        _ => None,
    }
}

fn singularize(field: &str) -> String {
    let singular = if let Some(stem) = field.strip_suffix("ies") {
        format!("{stem}y")
    } else if let Some(stem) = field.strip_suffix("ches") {
        format!("{stem}ch")
    } else if let Some(stem) = field.strip_suffix("shes") {
        format!("{stem}sh")
    } else if let Some(stem) = field.strip_suffix("sses") {
        format!("{stem}ss")
    } else if let Some(stem) = field.strip_suffix("xes") {
        format!("{stem}x")
    } else {
        field
            .strip_suffix('s')
            .filter(|stem| !stem.is_empty())
            .unwrap_or(field)
            .to_owned()
    };
    normalize_identifier(&singular).unwrap_or_else(|| "item".to_owned())
}
