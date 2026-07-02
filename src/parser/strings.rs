//! 这个文件承载 parser 层共享的 RawString 构造逻辑。
//!
//! 字符串长度前缀、是否有结尾 NUL、是否来自字符串表都由各 dialect 自己决定；一旦拿到
//! 原始字节、offset 和 raw size，文本解码与 `Origin` 组装应统一走这里。

use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{DecodedText, Origin, RawString, Span};

/// 用共享的 origin/text 组装逻辑创建 `RawString`，避免版本文件重复样板。
pub(crate) fn build_raw_string(
    options: ParseOptions,
    offset: usize,
    bytes: Vec<u8>,
    raw_size: usize,
) -> Result<RawString, ParseError> {
    let (encoding, value) =
        options
            .string_encoding
            .decode(offset, &bytes, options.string_decode_mode)?;
    Ok(RawString {
        bytes,
        text: Some(DecodedText { encoding, value }),
        origin: Origin {
            span: Span {
                offset,
                size: raw_size,
            },
            raw_word: None,
        },
    })
}
