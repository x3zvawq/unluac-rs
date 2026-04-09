//! 这个文件集中放 Naming 层共享的轻量工具函数。
//!
//! 它们本身不参与主流程决策，但 evidence、hint、allocation、strategy
//! 都会复用。把这些辅助函数独立出来，可以避免“公共小工具”继续把主流程文件撑大。

use std::collections::BTreeSet;

/// 取简单参数名候选。
pub(super) fn alphabetical_name(index: usize) -> Option<String> {
    const NAMES: &[&str] = &[
        "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "m", "n", "p", "q", "r", "s", "t",
        "u", "v", "w", "x", "y", "z",
    ];
    NAMES.get(index).map(|name| (*name).to_owned())
}

/// 把 parser/debug 给出的名字清洗成合法标识符。
pub(super) fn as_valid_name(value: &Option<String>) -> Option<String> {
    value.as_deref().and_then(normalize_identifier)
}

/// 规范化任意候选标识符。
pub(super) fn normalize_identifier(candidate: &str) -> Option<String> {
    if candidate.is_empty() {
        return None;
    }
    if is_valid_identifier(candidate) {
        return Some(candidate.to_owned());
    }

    let mut normalized = String::with_capacity(candidate.len());
    for ch in candidate.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            normalized.push(ch);
        } else if !normalized.ends_with('_') {
            normalized.push('_');
        }
    }

    let normalized = normalized.trim_matches('_');
    if normalized.is_empty() {
        return None;
    }

    let mut result = normalized.to_owned();
    if result
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_digit())
    {
        result.insert(0, '_');
    }
    if is_valid_identifier(&result) {
        Some(result)
    } else {
        None
    }
}

/// 判断是否为合法 Lua 标识符。
pub(super) fn is_valid_identifier(candidate: &str) -> bool {
    let mut chars = candidate.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

/// Lua 关键字列表（包含 `global` 作为保留标识符）。
const LUA_KEYWORDS: &[&str] = &[
    "and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if", "in",
    "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while", "global",
];

/// 判断是否为 Lua 关键字。
pub(super) fn is_lua_keyword(candidate: &str) -> bool {
    LUA_KEYWORDS.contains(&candidate)
}

/// 预置 Lua 关键字表。
pub(super) fn lua_keywords() -> BTreeSet<String> {
    LUA_KEYWORDS.iter().map(|s| (*s).to_owned()).collect()
}
