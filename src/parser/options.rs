//! 这个文件定义 parser 层的公共选项。
//!
//! 这些选项放在共享层，是为了让不同 dialect 的 parser 在严格度和字符串
//! 解码策略上遵循同一套调用约定，而不是把策略散落到各个实现里。

use chardetng::{EncodingDetector, Iso2022JpDetection, Utf8Detection};
use encoding_rs::Encoding;
use std::str::FromStr;
use strum_macros::{Display, EnumString, IntoStaticStr};

use super::error::ParseError;

/// 控制 parser 遇到异常时是立即报错，还是尽量继续解析。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum ParseMode {
    #[default]
    Strict,
    Permissive,
}

impl ParseMode {
    pub(crate) const fn is_permissive(self) -> bool {
        matches!(self, Self::Permissive)
    }
}

/// 控制 parser 生成字符串文本视图时使用的编码。
///
/// `auto` 会先用 chardetng 对原始字节做启发式检测；UTF-8 单独处理以使用
/// Rust 标准库的原生 UTF-8 校验和转换路径，
/// 其余编码统一走 encoding_rs 路径，支持 Encoding Standard 定义的所有编码。
/// `from_str()` 接受 encoding_rs 支持的任意编码标签（大小写不敏感），
/// 如 "auto"、"gbk"、"shift_jis"、"euc-kr"、"big5" 等。
#[derive(Debug, Clone, Copy, Default)]
pub enum StringEncoding {
    #[default]
    Auto,
    Utf8,
    /// encoding_rs 支持的非 UTF-8 编码
    EncodingRs(&'static Encoding),
}

// encoding_rs::Encoding 只实现了 PartialEq（基于指针比较），未实现 Eq，
// 因此这里手动实现以保证 StringEncoding 可用于 assert_eq! 等场景。
impl PartialEq for StringEncoding {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Auto, Self::Auto) => true,
            (Self::Utf8, Self::Utf8) => true,
            (Self::EncodingRs(a), Self::EncodingRs(b)) => std::ptr::eq(*a, *b),
            _ => false,
        }
    }
}

impl Eq for StringEncoding {}

impl StringEncoding {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Auto => "auto",
            Self::Utf8 => "utf-8",
            Self::EncodingRs(enc) => enc.name(),
        }
    }

    pub(crate) fn decode(
        self,
        offset: usize,
        bytes: &[u8],
        mode: StringDecodeMode,
    ) -> Result<(Self, String), ParseError> {
        let encoding = self.resolve(bytes);
        let value =
            match encoding {
                Self::Auto => unreachable!("auto encoding must resolve before decoding"),
                Self::Utf8 => match mode {
                    StringDecodeMode::Strict => std::str::from_utf8(bytes)
                        .map(str::to_owned)
                        .map_err(|_| ParseError::StringDecode {
                            offset,
                            encoding: encoding.as_str(),
                        }),
                    StringDecodeMode::Lossy => Ok(String::from_utf8_lossy(bytes).into_owned()),
                },
                Self::EncodingRs(enc) => {
                    let (value, _, had_errors) = enc.decode(bytes);
                    if had_errors && matches!(mode, StringDecodeMode::Strict) {
                        return Err(ParseError::StringDecode {
                            offset,
                            encoding: encoding.as_str(),
                        });
                    }
                    Ok(value.into_owned())
                }
            }?;
        Ok((encoding, value))
    }

    fn resolve(self, bytes: &[u8]) -> Self {
        if !matches!(self, Self::Auto) {
            return self;
        }
        let mut detector = EncodingDetector::new(Iso2022JpDetection::Allow);
        detector.feed(bytes, true);
        let enc = detector.guess(None, Utf8Detection::Allow);
        if std::ptr::eq(enc, encoding_rs::UTF_8) {
            Self::Utf8
        } else {
            Self::EncodingRs(enc)
        }
    }
}

impl FromStr for StringEncoding {
    type Err = ();

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        if value.eq_ignore_ascii_case("auto") {
            return Ok(Self::Auto);
        }
        // encoding_rs::Encoding::for_label 大小写不敏感，且接受 WHATWG 标准的所有别名
        let enc = Encoding::for_label(value.as_bytes()).ok_or(())?;
        // UTF-8 走 Rust 原生路径，不走 encoding_rs
        if std::ptr::eq(enc, encoding_rs::UTF_8) {
            Ok(Self::Utf8)
        } else {
            Ok(Self::EncodingRs(enc))
        }
    }
}

/// 控制字符串解码失败时是报错还是退化成宽松解码。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq, Display, EnumString, IntoStaticStr)]
#[strum(serialize_all = "kebab-case")]
pub enum StringDecodeMode {
    #[default]
    Strict,
    Lossy,
}

/// 传给各 dialect parser 的共享选项。
#[derive(Debug, Clone, Copy, Default, Eq, PartialEq)]
pub struct ParseOptions {
    pub mode: ParseMode,
    pub string_encoding: StringEncoding,
    pub string_decode_mode: StringDecodeMode,
}
