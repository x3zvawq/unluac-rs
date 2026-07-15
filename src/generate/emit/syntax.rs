//! 这个子模块负责 Generate 层共享的语法细节格式化。
//!
//! 它依赖 AST 运算符、目标方言和引号策略，只回答括号、字面量和标签这些稳定语法细节，
//! 不会在这里改变表达式语义。
//! 例如：当子表达式优先级不足时，这里会决定是否补上一层括号。

use crate::LuaString;
use crate::ast::{AstBinaryOpKind, AstGlobalAttr, AstGlobalBinding, AstLabelId};
use crate::generate::common::{NumberFormat, QuoteStyle};
use crate::generate::doc::Doc;
use crate::generate::error::GenerateError;

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
            Assoc::Full => false,
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

pub(super) fn format_number(value: f64, preserve_integral_float: bool) -> String {
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
    if value == 0.0 && value.is_sign_negative() {
        return "-0.0".to_owned();
    }
    let rendered = value.to_string();
    if !preserve_integral_float || rendered.contains(['.', 'e', 'E']) {
        rendered
    } else {
        format!("{rendered}.0")
    }
}

pub(super) fn format_vector_component(bits: u32) -> String {
    let value = f32::from_bits(bits);
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
    if value == 0.0 && value.is_sign_negative() {
        return "-0.0".to_owned();
    }
    value.to_string()
}

pub(super) fn format_integer(value: i64, number_format: NumberFormat) -> String {
    match number_format {
        NumberFormat::Decimal if value == i64::MIN => format_signed_hex(value),
        NumberFormat::Decimal => value.to_string(),
        NumberFormat::Hex => format_signed_hex(value),
    }
}

pub(super) fn format_unsigned_integer(value: u64, number_format: NumberFormat) -> String {
    match number_format {
        NumberFormat::Decimal => value.to_string(),
        NumberFormat::Hex => format!("0x{value:x}"),
    }
}

fn format_signed_hex(value: i64) -> String {
    if value.is_negative() {
        format!("-0x{:x}", value.unsigned_abs())
    } else {
        format!("0x{:x}", value)
    }
}

pub(super) fn format_complex_literal(real: f64, imag: f64) -> Result<String, GenerateError> {
    if real.to_bits() != 0.0f64.to_bits() || imag.is_nan() {
        return Err(GenerateError::UnrepresentableLuajitComplex { real, imag });
    }
    let coefficient = match (imag.is_infinite(), imag.is_sign_negative()) {
        (true, true) => "-1e999".to_owned(),
        (true, false) => "1e999".to_owned(),
        (false, _) => format_number(imag, false),
    };
    Ok(format!("{coefficient}i"))
}

pub(super) fn format_string_literal(value: &LuaString, quote_style: QuoteStyle) -> String {
    if let Some(text) = value.preferred_text().or_else(|| value.as_utf8())
        && can_use_long_bracket_string(text)
    {
        return format_long_bracket_string(text);
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
    push_quoted_string_body(&mut rendered, value, preferred);
    rendered.push(preferred);
    rendered
}

fn push_quoted_string_body(rendered: &mut String, value: &LuaString, quote: char) {
    if let Some(text) = value.preferred_text().or_else(|| value.as_utf8()) {
        push_utf8_string_body(rendered, text, quote);
    } else {
        push_byte_string_body(rendered, value.as_bytes(), quote);
    }
}

fn push_utf8_string_body(rendered: &mut String, text: &str, quote: char) {
    for ch in text.chars() {
        match ch {
            '\n' => rendered.push_str("\\n"),
            '\r' => rendered.push_str("\\r"),
            '\t' => rendered.push_str("\\t"),
            '\\' => rendered.push_str("\\\\"),
            c if c == quote => {
                rendered.push('\\');
                rendered.push(c);
            }
            c if c.is_control() => {
                push_escaped_utf8_bytes(rendered, c);
            }
            c => rendered.push(c),
        }
    }
}

fn push_byte_string_body(rendered: &mut String, bytes: &[u8], quote: char) {
    for byte in bytes {
        match *byte {
            b'\n' => rendered.push_str("\\n"),
            b'\r' => rendered.push_str("\\r"),
            b'\t' => rendered.push_str("\\t"),
            b'\\' => rendered.push_str("\\\\"),
            b if char::from(b) == quote => {
                rendered.push('\\');
                rendered.push(char::from(b));
            }
            0x20..=0x7e => rendered.push(char::from(*byte)),
            byte => push_decimal_escape(rendered, byte),
        }
    }
}

fn push_escaped_utf8_bytes(rendered: &mut String, ch: char) {
    let mut bytes = [0; 4];
    for byte in ch.encode_utf8(&mut bytes).as_bytes() {
        push_decimal_escape(rendered, *byte);
    }
}

fn push_decimal_escape(rendered: &mut String, byte: u8) {
    rendered.push('\\');
    rendered.push(char::from(b'0' + byte / 100));
    rendered.push(char::from(b'0' + byte / 10 % 10));
    rendered.push(char::from(b'0' + byte % 10));
}

fn can_use_long_bracket_string(value: &str) -> bool {
    value.contains('\n') && !value.starts_with('\n') && !value.contains('\r')
}

fn format_long_bracket_string(value: &str) -> String {
    let eqs = long_bracket_eqs(value);
    format!("[{eqs}[{value}]{eqs}]")
}

fn long_bracket_eqs(value: &str) -> String {
    for count in 0.. {
        let eqs = "=".repeat(count);
        let mut closing = format!("]{eqs}");
        let overlaps_suffix = value.ends_with(&closing);
        closing.push(']');
        if !overlaps_suffix && !value.contains(&closing) {
            return eqs;
        }
    }

    unreachable!("unbounded search over bracket delimiters should always terminate")
}

fn escape_cost(value: &LuaString, quote: char) -> usize {
    if let Some(text) = value.preferred_text().or_else(|| value.as_utf8()) {
        return text
            .chars()
            .map(|ch| match ch {
                '\n' | '\r' | '\t' | '\\' => 2,
                c if c == quote => 2,
                c if c.is_control() => c.len_utf8() * 4,
                _ => ch.len_utf8(),
            })
            .sum();
    }
    value
        .as_bytes()
        .iter()
        .map(|byte| match *byte {
            b'\n' | b'\r' | b'\t' | b'\\' => 2,
            b if char::from(b) == quote => 2,
            0x20..=0x7e => 1,
            _ => 4,
        })
        .sum()
}
