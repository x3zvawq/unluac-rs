//! 这个文件承载 `generate::emit::syntax` 的局部输出测试。
//!
//! 这里只锁共享语法 helper 的文本规则，避免把生成层的小约定全都挤进更高层回归里。

use crate::generate::common::QuoteStyle;

use super::format_string_literal;

#[test]
fn formats_multiline_strings_with_long_brackets() {
    assert_eq!(
        format_string_literal("first\nsecond\n", QuoteStyle::PreferDouble),
        "[[first\nsecond\n]]"
    );
}

#[test]
fn widens_long_bracket_delimiter_when_content_contains_closer() {
    assert_eq!(
        format_string_literal("head\n]]\ntail", QuoteStyle::PreferDouble),
        "[=[head\n]]\ntail]=]"
    );
}

#[test]
fn keeps_single_line_strings_on_quoted_literal_path() {
    assert_eq!(
        format_string_literal("ffi", QuoteStyle::PreferDouble),
        "\"ffi\""
    );
}
