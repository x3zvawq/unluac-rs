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
            return expr
                .is_boolean_valued()
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

// 只裁掉明确的词边界（lowercase / PascalCase / SCREAMING_SNAKE_CASE）；
// `getaway`、`Getaway`、`Builder`、`GETS` 等不能被误拆。标准库 `getenv` 是明确的例外。
fn result_from_verb(name: &str) -> Option<String> {
    if name == "getenv" {
        return Some("env".to_owned());
    }
    for prefix in [
        "get", "find", "load", "create", "fetch", "read", "make", "build", "parse", "new",
    ] {
        let Some(rest) = strip_verb_prefix(name, prefix) else {
            continue;
        };
        if rest.is_empty() || rest.starts_with(|c: char| c.is_ascii_digit()) {
            return None;
        }
        let candidate = lowercase_leading_word(rest);
        return normalize_identifier(&candidate);
    }
    None
}

fn strip_verb_prefix<'a>(name: &'a str, prefix: &str) -> Option<&'a str> {
    if name.len() <= prefix.len() || !name.is_char_boundary(prefix.len()) {
        return None;
    }
    let (head, tail) = name.split_at(prefix.len());
    let head_bytes = head.as_bytes();
    let prefix_bytes = prefix.as_bytes();
    let is_lower = head == prefix;
    let is_pascal = head_bytes[0].is_ascii_uppercase()
        && head_bytes[0].to_ascii_lowercase() == prefix_bytes[0]
        && head[1..] == prefix[1..];
    let is_upper = head_bytes
        .iter()
        .zip(prefix_bytes)
        .all(|(h, p)| h.is_ascii_uppercase() && h.to_ascii_lowercase() == *p);

    if is_lower || is_pascal {
        if let Some(rest) = tail.strip_prefix('_') {
            return Some(rest);
        }
        if tail.starts_with(|c: char| c.is_ascii_uppercase()) {
            return Some(tail);
        }
    } else if is_upper && let Some(rest) = tail.strip_prefix('_') {
        return Some(rest);
    }
    None
}

/// 将动词后缀规范为自然的小驼峰/小写标识符：
/// - `Player` → `player`，`Buff` → `buff`
/// - `ID` / `NPC` / `NPC_INFO` → `id` / `npc` / `npc_info`
/// - `NPCName` / `HTTPClient` → `npcName` / `httpClient`
fn lowercase_leading_word(rest: &str) -> String {
    if !rest.bytes().any(|b| b.is_ascii_lowercase()) {
        return rest.to_ascii_lowercase();
    }
    let upper_run = rest
        .bytes()
        .take_while(|b| b.is_ascii_uppercase())
        .count();
    if upper_run == 0 {
        return rest.to_owned();
    }
    let lower_count = if upper_run == 1 {
        1
    } else if rest.as_bytes().get(upper_run).is_some_and(|b| b.is_ascii_lowercase()) {
        upper_run - 1
    } else {
        upper_run
    };
    let mut out = String::with_capacity(rest.len());
    out.push_str(&rest[..lower_count].to_ascii_lowercase());
    out.push_str(&rest[lower_count..]);
    out
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

#[cfg(test)]
mod tests {
    use super::result_from_verb;

    #[test]
    fn extracts_noun_from_camel_pascal_and_screaming_snake_verbs() {
        for (input, expected) in [
            ("getenv", Some("env")),
            ("getPlayer", Some("player")),
            ("get_player", Some("player")),
            ("GetPlayer", Some("player")),
            ("GetBuff", Some("buff")),
            ("Get_Player", Some("player")),
            ("GET_PLAYER", Some("player")),
            ("GET_NPC_INFO", Some("npc_info")),
            ("FindFirstChild", Some("firstChild")),
            ("CreateItem", Some("item")),
            ("LoadConfig", Some("config")),
            ("GetID", Some("id")),
            ("GetNPC", Some("npc")),
            ("GetNPCName", Some("npcName")),
            ("GetHTTPClient", Some("httpClient")),
            ("GetUI2Layer", Some("ui2Layer")),
            ("GetX", Some("x")),
        ] {
            assert_eq!(
                result_from_verb(input).as_deref(),
                expected,
                "input={input:?}"
            );
        }
    }

    #[test]
    fn rejects_false_word_boundaries_and_non_getter_verbs() {
        for input in [
            "get",
            "Get",
            "Get_",
            "Get_1",
            "getaway",
            "Getaway",
            "Builder",
            "Newbie",
            "Readonly",
            "GETS",
            "IsPlayer",
            "HasBuff",
            "SetPlayer",
        ] {
            assert_eq!(result_from_verb(input), None, "input={input:?}");
        }
    }
}
