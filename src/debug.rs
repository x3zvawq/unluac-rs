//! 这个模块定义各层调试能力共享的公共契约。
//!
//! 之所以把 `detail / filters` 这类类型单独提出来，是为了让 parser、
//! 后续 transformer/cfg 和主 pipeline 共享同一套调试开关，同时避免低层反向
//! 依赖 `decompile` 模块。

use std::{fmt, str::FromStr};
use std::io::IsTerminal;

use owo_colors::{OwoColorize, Style};

/// 调试输出详细程度。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugDetail {
    Summary,
    #[default]
    Normal,
    Verbose,
}

impl DebugDetail {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Summary => "summary",
            Self::Normal => "normal",
            Self::Verbose => "verbose",
        }
    }
}

impl fmt::Display for DebugDetail {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for DebugDetail {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "summary" => Ok(Self::Summary),
            "normal" => Ok(Self::Normal),
            "verbose" => Ok(Self::Verbose),
            _ => Err(()),
        }
    }
}

/// 调试输出颜色策略。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub enum DebugColorMode {
    #[default]
    Auto,
    Always,
    Never,
}

impl DebugColorMode {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Always => "always",
            Self::Never => "never",
        }
    }

    fn enabled(self) -> bool {
        match self {
            Self::Auto => std::io::stdout().is_terminal(),
            Self::Always => true,
            Self::Never => false,
        }
    }
}

impl fmt::Display for DebugColorMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for DebugColorMode {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "auto" => Ok(Self::Auto),
            "always" => Ok(Self::Always),
            "never" => Ok(Self::Never),
            _ => Err(()),
        }
    }
}

/// 统一过滤器先从 proto 维度开始，后续再按同样模式扩展到 block、instr、reg。
#[derive(Debug, Clone, Default, Eq, PartialEq)]
pub struct DebugFilters {
    pub proto: Option<usize>,
}

#[derive(Debug, Clone, Copy)]
struct DebugPalette {
    enabled: bool,
}

impl DebugPalette {
    fn new(mode: DebugColorMode) -> Self {
        Self {
            enabled: mode.enabled(),
        }
    }

    fn title(self, text: &str) -> String {
        self.paint(text, Style::new().blue().bold())
    }

    fn section(self, text: &str) -> String {
        self.paint(text, Style::new().yellow().bold())
    }

    fn field(self, text: &str) -> String {
        self.paint(text, Style::new().green().bold())
    }

    fn dim(self, text: &str) -> String {
        self.paint(text, Style::new().bright_black())
    }

    fn keyword(self, text: &str) -> String {
        self.paint(text, Style::new().magenta().bold())
    }

    fn entity(self, text: &str) -> String {
        self.paint(text, Style::new().cyan())
    }

    fn opcode(self, text: &str) -> String {
        self.paint(text, Style::new().yellow().bold())
    }

    fn operator(self, text: &str) -> String {
        self.paint(text, Style::new().yellow())
    }

    fn punct(self, text: &str) -> String {
        self.paint(text, Style::new().bright_black())
    }

    fn literal(self, text: &str) -> String {
        self.paint(text, Style::new().bright_green())
    }

    fn warning(self, text: &str) -> String {
        self.paint(text, Style::new().red().bold())
    }

    fn paint(self, text: &str, style: Style) -> String {
        if self.enabled {
            format!("{}", text.style(style))
        } else {
            text.to_owned()
        }
    }
}

pub(crate) fn colorize_debug_text(text: &str, mode: DebugColorMode) -> String {
    let palette = DebugPalette::new(mode);
    if !palette.enabled {
        return text.to_owned();
    }

    let mut output = String::new();
    for (index, line) in text.lines().enumerate() {
        if index > 0 {
            output.push('\n');
        }
        output.push_str(&colorize_line(line, palette));
    }
    if text.ends_with('\n') {
        output.push('\n');
    }
    output
}

fn colorize_line(line: &str, palette: DebugPalette) -> String {
    if line.contains('\u{1b}') {
        return line.to_owned();
    }

    let indent_len = line.len() - line.trim_start_matches(' ').len();
    let indent = &line[..indent_len];
    let trimmed = &line[indent_len..];

    if trimmed.is_empty() {
        return line.to_owned();
    }

    if trimmed.starts_with("===== ") {
        return format!("{indent}{}", palette.title(trimmed));
    }

    if is_section_heading(trimmed) {
        return format!("{indent}{}", palette.section(trimmed));
    }

    if trimmed.starts_with("pc=") {
        return format!(
            "{indent}{}",
            colorize_parser_instruction_line(trimmed, palette)
        );
    }

    if trimmed.starts_with('@') {
        return format!(
            "{indent}{}",
            colorize_indexed_instruction_line(trimmed, palette)
        );
    }

    if let Some((key, rest)) = trimmed.split_once(": ")
        && !key.contains(' ')
    {
        return format!(
            "{indent}{}: {}",
            palette.field(key),
            colorize_inline(rest, palette)
        );
    }

    if trimmed.starts_with("::L") && trimmed.ends_with("::") {
        return format!("{indent}{}", palette.entity(trimmed));
    }

    format!("{indent}{}", colorize_inline(trimmed, palette))
}

fn colorize_parser_instruction_line(line: &str, palette: DebugPalette) -> String {
    let Some((pc_part, rest)) = line.split_once(" opcode=") else {
        return colorize_inline(line, palette);
    };
    let Some((opcode_part, rest)) = rest.split_once(" operands=") else {
        return colorize_inline(line, palette);
    };
    let Some((operands_part, origin_part)) = rest.split_once(" origin=") else {
        return colorize_inline(line, palette);
    };

    format!(
        "{} {} {} {}",
        colorize_key_value_token("pc", pc_part.trim_start_matches("pc="), palette),
        colorize_key_value_token("opcode", opcode_part.trim(), palette),
        colorize_operands_value(operands_part, palette),
        colorize_key_value_token("origin", origin_part, palette),
    )
}

fn colorize_indexed_instruction_line(line: &str, palette: DebugPalette) -> String {
    let Some((index_token, rest)) = line.split_once(' ') else {
        return colorize_inline(line, palette);
    };
    let rest = rest.trim_start();
    if let Some(rest) = rest.strip_prefix("block=") {
        let Some((block_token, rest)) = rest.split_once(' ') else {
            return format!(
                "{} {}",
                palette.entity(index_token),
                colorize_key_value_token("block", rest, palette),
            );
        };
        let rest = rest.trim_start();
        let Some((head_token, tail)) = rest.split_once(' ') else {
            return format!(
                "{} {} {}",
                palette.entity(index_token),
                colorize_key_value_token("block", block_token, palette),
                palette.opcode(rest),
            );
        };
        return format!(
            "{} {} {} {}",
            palette.entity(index_token),
            colorize_key_value_token("block", block_token, palette),
            palette.opcode(head_token),
            colorize_inline(tail, palette),
        );
    }

    let Some((head_token, tail)) = rest.split_once(' ') else {
        return format!("{} {}", palette.entity(index_token), palette.opcode(rest));
    };

    format!(
        "{} {} {}",
        palette.entity(index_token),
        palette.opcode(head_token),
        colorize_inline(tail, palette),
    )
}

fn colorize_inline(line: &str, palette: DebugPalette) -> String {
    let mut output = String::new();
    let mut index = 0;
    let mut previous = PrevTokenContext::Boundary;

    while index < line.len() {
        let ch = next_char(line, index);
        if ch.is_whitespace() {
            output.push(ch);
            index += ch.len_utf8();
            previous = PrevTokenContext::Boundary;
            continue;
        }

        if ch == '"' {
            let end = consume_string_literal(line, index);
            output.push_str(&palette.literal(&line[index..end]));
            index = end;
            previous = PrevTokenContext::Value;
            continue;
        }

        if ch.is_ascii_digit() {
            let end = consume_number_token(line, index);
            output.push_str(&palette.dim(&line[index..end]));
            index = end;
            previous = PrevTokenContext::Value;
            continue;
        }

        if is_word_start(ch) {
            let end = consume_word_token(line, index);
            let token = &line[index..end];
            let is_inline_field = line[end..].starts_with('=');
            output.push_str(&colorize_word_token(
                token,
                is_inline_field,
                previous,
                palette,
            ));
            index = end;
            previous = if matches!(token, "." | ":") {
                PrevTokenContext::MemberAccess
            } else {
                PrevTokenContext::Value
            };
            continue;
        }

        if let Some(symbol_len) = match_symbol_token(line, index) {
            let token = &line[index..index + symbol_len];
            output.push_str(&colorize_symbol_token(token, palette));
            index += symbol_len;
            previous = if matches!(token, "." | ":") {
                PrevTokenContext::MemberAccess
            } else {
                PrevTokenContext::Boundary
            };
            continue;
        }

        output.push_str(&palette.punct(&line[index..index + ch.len_utf8()]));
        index += ch.len_utf8();
        previous = PrevTokenContext::Boundary;
    }

    output
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum PrevTokenContext {
    Boundary,
    MemberAccess,
    Value,
}

fn next_char(line: &str, index: usize) -> char {
    line[index..]
        .chars()
        .next()
        .expect("index should always point to a char boundary")
}

fn is_word_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || matches!(ch, '_' | '#' | '@')
}

fn consume_string_literal(line: &str, start: usize) -> usize {
    let mut escaped = false;
    let mut index = start + '"'.len_utf8();

    while index < line.len() {
        let ch = next_char(line, index);
        index += ch.len_utf8();

        if escaped {
            escaped = false;
            continue;
        }

        if ch == '\\' {
            escaped = true;
            continue;
        }

        if ch == '"' {
            break;
        }
    }

    index
}

fn consume_number_token(line: &str, start: usize) -> usize {
    let mut index = start;
    if line[start..].starts_with("0x") || line[start..].starts_with("0X") {
        index += 2;
        while index < line.len() {
            let ch = next_char(line, index);
            if ch.is_ascii_hexdigit() || ch == '_' {
                index += ch.len_utf8();
            } else {
                break;
            }
        }
        return index;
    }

    let mut seen_dot = false;
    let mut seen_exponent = false;
    while index < line.len() {
        let ch = next_char(line, index);
        if ch.is_ascii_digit() || ch == '_' {
            index += ch.len_utf8();
            continue;
        }
        if !seen_dot && ch == '.' {
            let next_index = index + ch.len_utf8();
            if next_index < line.len() && next_char(line, next_index).is_ascii_digit() {
                seen_dot = true;
                index = next_index;
                continue;
            }
        }
        if !seen_exponent && matches!(ch, 'e' | 'E') {
            let next_index = index + ch.len_utf8();
            if next_index < line.len() {
                let next = next_char(line, next_index);
                if next.is_ascii_digit() || matches!(next, '+' | '-') {
                    seen_exponent = true;
                    index = next_index;
                    continue;
                }
            }
        }
        if seen_exponent && matches!(ch, '+' | '-') {
            let prev = line[..index].chars().next_back();
            if matches!(prev, Some('e' | 'E')) {
                index += ch.len_utf8();
                continue;
            }
        }
        break;
    }
    index
}

fn consume_word_token(line: &str, start: usize) -> usize {
    let mut index = start;
    while index < line.len() {
        let ch = next_char(line, index);
        if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '#' | '@' | '-') {
            index += ch.len_utf8();
        } else {
            break;
        }
    }
    index
}

fn match_symbol_token(line: &str, start: usize) -> Option<usize> {
    const MULTI_CHAR_SYMBOLS: [&str; 8] = ["::", "...", "..", "->", "<-", "<=", ">=", "=="];
    for symbol in MULTI_CHAR_SYMBOLS {
        if line[start..].starts_with(symbol) {
            return Some(symbol.len());
        }
    }
    if line[start..].starts_with("~=") {
        return Some(2);
    }

    matches!(
        next_char(line, start),
        '=' | '.'
            | ':'
            | ','
            | '('
            | ')'
            | '['
            | ']'
            | '{'
            | '}'
            | '<'
            | '>'
            | '+'
            | '-'
            | '*'
            | '/'
            | '%'
            | '^'
            | '#'
    )
    .then_some(1)
}

fn colorize_word_token(
    token: &str,
    is_inline_field: bool,
    previous: PrevTokenContext,
    palette: DebugPalette,
) -> String {
    if token.is_empty() {
        return String::new();
    }

    if is_inline_field {
        return if is_operand_field_key(token) {
            palette.opcode(token)
        } else {
            palette.field(token)
        };
    }

    if is_literal_token(token) {
        return palette.literal(token);
    }

    if is_keyword_token(token) {
        return palette.keyword(token);
    }

    if is_warning_token(token) {
        return palette.warning(token);
    }

    if is_opcode_token(token) {
        return palette.opcode(token);
    }

    if matches!(previous, PrevTokenContext::MemberAccess) {
        return palette.entity(token);
    }

    if is_anchor_token(token) {
        return palette.entity(token);
    }

    token.to_owned()
}

fn colorize_symbol_token(token: &str, palette: DebugPalette) -> String {
    if is_operator_symbol(token) {
        return palette.operator(token);
    }
    palette.punct(token)
}

fn is_operator_symbol(token: &str) -> bool {
    matches!(
        token,
        "=" | "->"
            | "<-"
            | "<"
            | ">"
            | "<="
            | ">="
            | "=="
            | "~="
            | "+"
            | "-"
            | "*"
            | "/"
            | "%"
            | "^"
            | "#"
            | ".."
            | "..."
    )
}

fn is_literal_token(token: &str) -> bool {
    matches!(token, "nil" | "true" | "false")
}

fn colorize_key_value_token(key: &str, value: &str, palette: DebugPalette) -> String {
    if key.is_empty() {
        return colorize_inline(value, palette);
    }

    let styled_key = if is_operand_field_key(key) {
        palette.opcode(key)
    } else {
        palette.field(key)
    };

    let styled_value = match key {
        "opcode" => palette.opcode(value),
        "pc" | "raw" | "line" => palette.dim(value),
        "operands" => colorize_operands_value(value, palette),
        "origin" => palette.dim(value),
        "effects" => colorize_inline(value, palette),
        "kind" if is_opcode_token(value) => palette.opcode(value),
        _ => colorize_inline(value, palette),
    };

    format!("{styled_key}={styled_value}")
}

fn colorize_operands_value(value: &str, palette: DebugPalette) -> String {
    let styled_key = palette.field("operands");
    let Some((shape, args)) = value.split_once('(') else {
        return format!("{styled_key}={}", palette.opcode(value));
    };
    let args = args.strip_suffix(')').unwrap_or(args);
    let styled_args = args
        .split(", ")
        .map(|part| {
            if let Some((key, value)) = part.split_once('=') {
                format!("{}={}", palette.opcode(key), palette.dim(value))
            } else {
                palette.opcode(part)
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{styled_key}={}({styled_args})", palette.opcode(shape),)
}

fn is_operand_field_key(key: &str) -> bool {
    matches!(key, "A" | "B" | "C" | "Bx" | "sBx" | "Ax" | "sJ" | "k")
}

fn is_section_heading(line: &str) -> bool {
    matches!(
        line,
        "header"
            | "proto tree"
            | "constants"
            | "raw instructions"
            | "low-ir listing"
            | "block listing"
            | "edge listing"
            | "dominator tree"
            | "post-dominator tree"
            | "dominance frontier"
            | "natural loops"
            | "instr effects"
            | "liveness"
            | "phi candidates"
            | "reaching defs"
            | "reaching values"
            | "branch candidates"
            | "branch value merges"
            | "loop candidates"
            | "short-circuit candidates"
            | "goto requirements"
            | "region facts"
            | "scope candidates"
            | "body"
            | "debug locals"
            | "debug upvalue names"
    )
}

fn is_keyword_token(token: &str) -> bool {
    matches!(
        token,
        "local"
            | "global"
            | "function"
            | "assign"
            | "call"
            | "return"
            | "if"
            | "then"
            | "else"
            | "elseif"
            | "end"
            | "while"
            | "repeat"
            | "until"
            | "and"
            | "or"
            | "not"
            | "in"
            | "numeric-for"
            | "generic-for"
            | "break"
            | "continue"
            | "goto"
            | "label"
            | "block"
            | "edge"
            | "table-set-list"
            | "err-nnil"
            | "to-be-closed"
            | "close"
            | "unstructured"
            | "do"
    )
}

fn is_anchor_token(token: &str) -> bool {
    token == "parser"
        || token == "lir"
        || token == "cfg"
        || token == "graph-facts"
        || token == "dataflow"
        || token == "structure"
        || token == "hir"
        || token == "ast"
        || token == "readability"
        || token == "pipeline"
        || token == "filters"
        || token.starts_with("proto#")
        || token.starts_with('@')
        || token.starts_with("pc=")
        || token.starts_with('#') && token[1..].chars().all(|ch| ch.is_ascii_digit())
        || is_named_index_token(token, "def")
        || is_named_index_token(token, "phi")
        || is_named_index_token(token, "open")
        || is_prefixed_index_token(token, 'k')
        || is_prefixed_index_token(token, 'u')
        || is_prefixed_index_token(token, 'r')
        || is_prefixed_index_token(token, 'l')
        || is_prefixed_index_token(token, 't')
        || is_prefixed_index_token(token, 'p')
        || is_prefixed_index_token(token, 'L')
}

fn is_prefixed_index_token(token: &str, prefix: char) -> bool {
    let mut chars = token.chars();
    matches!(chars.next(), Some(found) if found == prefix) && chars.all(|ch| ch.is_ascii_digit())
}

fn is_named_index_token(token: &str, prefix: &str) -> bool {
    token
        .strip_prefix(prefix)
        .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|ch| ch.is_ascii_digit()))
}

fn is_warning_token(token: &str) -> bool {
    matches!(
        token,
        "decision" | "unresolved" | "unstructured" | "fallback"
    ) || token.starts_with("decision(")
        || token.starts_with("unresolved(")
}

fn is_opcode_token(token: &str) -> bool {
    token.chars().all(|ch| ch.is_ascii_uppercase() || ch == '_')
        || matches!(
            token,
            "move"
                | "load-nil"
                | "load-bool"
                | "load-const"
                | "load-int"
                | "load-num"
                | "concat"
                | "get-upvalue"
                | "set-upvalue"
                | "get-table"
                | "set-table"
                | "err-nnil"
                | "new-table"
                | "set-list"
                | "call"
                | "tail-call"
                | "return"
                | "jump"
                | "branch"
                | "branch-true"
                | "branch-false"
                | "fallthrough"
                | "alloc"
                | "read-table"
                | "write-table"
                | "read-env"
                | "write-env"
                | "read-upvalue"
                | "write-upvalue"
                | "closure"
                | "numeric-for-init"
                | "numeric-for-loop"
                | "generic-for-call"
                | "generic-for-loop"
                | "tbc"
                | "close"
                | "getvarg"
        )
}

#[cfg(test)]
mod tests;
