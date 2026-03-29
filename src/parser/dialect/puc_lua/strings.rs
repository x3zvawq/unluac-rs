use crate::parser::error::ParseError;
use crate::parser::options::ParseOptions;
use crate::parser::raw::{DecodedText, Origin, RawString, Span};

/// 复用 parser 共享的字符串编码选项，为原始字节补上可选文本视图。
pub(crate) fn decode_string_text(
    options: ParseOptions,
    offset: usize,
    bytes: &[u8],
) -> Result<Option<DecodedText>, ParseError> {
    let encoding = options.string_encoding;
    let value = encoding.decode(offset, bytes, options.string_decode_mode)?;
    Ok(Some(DecodedText { encoding, value }))
}

/// 用共享的 origin/text 组装逻辑创建 `RawString`，避免版本文件重复样板。
pub(crate) fn build_raw_string(
    options: ParseOptions,
    offset: usize,
    bytes: Vec<u8>,
    raw_size: usize,
) -> Result<RawString, ParseError> {
    let text = decode_string_text(options, offset, &bytes)?;
    Ok(RawString {
        bytes,
        text,
        origin: Origin {
            span: Span {
                offset,
                size: raw_size,
            },
            raw_word: None,
        },
    })
}
