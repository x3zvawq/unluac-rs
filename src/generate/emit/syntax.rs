//! 这个子模块负责 Generate 层共享的语法细节格式化。
//!
//! 它依赖 AST 运算符、目标方言和引号策略，只回答括号、字面量和标签这些稳定语法细节，
//! 不会在这里改变表达式语义。
//! 例如：当子表达式优先级不足时，这里会决定是否补上一层括号。

use crate::ast::{AstBinaryOpKind, AstGlobalAttr, AstGlobalBinding, AstLabelId};
use crate::generate::common::QuoteStyle;
use crate::generate::doc::Doc;

use super::{
    Assoc, ExprSide, PREC_ADD, PREC_BIT_AND, PREC_BIT_OR, PREC_BIT_XOR, PREC_COMPARE, PREC_CONCAT,
    PREC_MUL, PREC_POW, PREC_SHIFT,
};

pub(super) fn maybe_parenthesize(
    doc: Doc,
    expr_prec: u8,
    parent_prec: u8,
    side: ExprSide,
    assoc: Assoc,
) -> Doc {
    let needs_parens = if expr_prec < parent_prec {
        true
    } else if expr_prec > parent_prec {
        false
    } else {
        match assoc {
            Assoc::Left => matches!(side, ExprSide::Right),
            Assoc::Right => matches!(side, ExprSide::Left),
            Assoc::Non => !matches!(side, ExprSide::Standalone),
        }
    };
    if needs_parens {
        Doc::concat([Doc::text("("), doc, Doc::text(")")])
    } else {
        doc
    }
}

pub(super) fn binary_meta(op: AstBinaryOpKind) -> (u8, Assoc, &'static str) {
    match op {
        AstBinaryOpKind::Add => (PREC_ADD, Assoc::Left, "+"),
        AstBinaryOpKind::Sub => (PREC_ADD, Assoc::Left, "-"),
        AstBinaryOpKind::Mul => (PREC_MUL, Assoc::Left, "*"),
        AstBinaryOpKind::Div => (PREC_MUL, Assoc::Left, "/"),
        AstBinaryOpKind::FloorDiv => (PREC_MUL, Assoc::Left, "//"),
        AstBinaryOpKind::Mod => (PREC_MUL, Assoc::Left, "%"),
        AstBinaryOpKind::Pow => (PREC_POW, Assoc::Right, "^"),
        AstBinaryOpKind::BitAnd => (PREC_BIT_AND, Assoc::Left, "&"),
        AstBinaryOpKind::BitOr => (PREC_BIT_OR, Assoc::Left, "|"),
        AstBinaryOpKind::BitXor => (PREC_BIT_XOR, Assoc::Left, "~"),
        AstBinaryOpKind::Shl => (PREC_SHIFT, Assoc::Left, "<<"),
        AstBinaryOpKind::Shr => (PREC_SHIFT, Assoc::Left, ">>"),
        AstBinaryOpKind::Concat => (PREC_CONCAT, Assoc::Right, ".."),
        AstBinaryOpKind::Eq => (PREC_COMPARE, Assoc::Non, "=="),
        AstBinaryOpKind::Lt => (PREC_COMPARE, Assoc::Non, "<"),
        AstBinaryOpKind::Le => (PREC_COMPARE, Assoc::Non, "<="),
    }
}

pub(super) fn common_global_attr(bindings: &[AstGlobalBinding]) -> Option<AstGlobalAttr> {
    let first = bindings
        .first()
        .map(|binding| binding.attr)
        .unwrap_or(AstGlobalAttr::None);
    bindings
        .iter()
        .all(|binding| binding.attr == first)
        .then_some(first)
}

pub(super) fn format_label_name(label: AstLabelId) -> String {
    format!("L{}", label.index())
}

pub(super) fn format_number(value: f64) -> String {
    if value.is_nan() {
        return "(0/0)".to_owned();
    }
    if value.is_infinite() {
        return if value.is_sign_negative() {
            "(-1/0)".to_owned()
        } else {
            "(1/0)".to_owned()
        };
    }
    value.to_string()
}

pub(super) fn format_complex_literal(real: f64, imag: f64) -> String {
    if real == 0.0 {
        return format!("{}i", format_number(imag));
    }
    let imag_abs = format_number(imag.abs());
    let imag_sign = if imag.is_sign_negative() { "-" } else { "+" };
    format!("({} {} {}i)", format_number(real), imag_sign, imag_abs)
}

pub(super) fn format_string_literal(value: &str, quote_style: QuoteStyle) -> String {
    if value.contains(['\n', '\r']) {
        return format_long_bracket_string(value);
    }

    let candidates = match quote_style {
        QuoteStyle::PreferDouble => ['"', '\''],
        QuoteStyle::PreferSingle => ['\'', '"'],
        QuoteStyle::MinEscape => ['"', '\''],
    };
    let preferred = if matches!(quote_style, QuoteStyle::MinEscape) {
        if escape_cost(value, '"') <= escape_cost(value, '\'') {
            '"'
        } else {
            '\''
        }
    } else {
        candidates[0]
    };
    let mut rendered = String::new();
    rendered.push(preferred);
    for ch in value.chars() {
        match ch {
            '\n' => rendered.push_str("\\n"),
            '\r' => rendered.push_str("\\r"),
            '\t' => rendered.push_str("\\t"),
            '\\' => rendered.push_str("\\\\"),
            c if c == preferred => {
                rendered.push('\\');
                rendered.push(c);
            }
            c if c.is_control() => {
                rendered.push_str(&format!("\\{:03}", c as u32));
            }
            c => rendered.push(c),
        }
    }
    rendered.push(preferred);
    rendered
}

fn format_long_bracket_string(value: &str) -> String {
    let eqs = long_bracket_eqs(value);
    format!("[{eqs}[{value}]{eqs}]")
}

fn long_bracket_eqs(value: &str) -> String {
    for count in 0.. {
        let eqs = "=".repeat(count);
        let closing = format!("]{eqs}]");
        if !value.contains(&closing) {
            return eqs;
        }
    }

    unreachable!("unbounded search over bracket delimiters should always terminate")
}

fn escape_cost(value: &str, quote: char) -> usize {
    value
        .chars()
        .map(|ch| match ch {
            '\n' | '\r' | '\t' | '\\' => 2,
            c if c == quote => 2,
            c if c.is_control() => 4,
            _ => 1,
        })
        .sum()
}

#[cfg(test)]
mod tests;
