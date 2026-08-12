//! Lua 字符串字面量的字节值。
//!
//! Lua string 是任意字节序列，不等同于 Rust `String`。HIR 之后的表达式层必须保留
//! 原始字节；只有在需要生成字段名、全局名或调试名这类文本身份时，才临时尝试 UTF-8
//! 视图。字节与已解码文本使用 `Arc` 共享，RawString -> HIR -> AST 的机械 Clone
//! 不应随 pipeline 阶段重复深拷贝字面量。

use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::parser::{RawString, StringEncoding};

#[derive(Debug, Clone, Default)]
pub struct LuaString {
    bytes: Arc<[u8]>,
    text: Option<Arc<str>>,
    encoding: Option<StringEncoding>,
}

impl PartialEq for LuaString {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for LuaString {}

impl PartialOrd for LuaString {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LuaString {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bytes.cmp(&other.bytes)
    }
}

impl Hash for LuaString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl LuaString {
    pub fn from_raw(raw: &RawString) -> Self {
        Self {
            bytes: raw.bytes.clone(),
            text: raw.text.as_ref().map(|text| text.value.clone()),
            encoding: raw.text.as_ref().map(|text| text.encoding),
        }
    }

    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        Self {
            bytes: bytes.into(),
            text: None,
            encoding: None,
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub fn decoded_text(&self) -> Option<&str> {
        self.text.as_deref()
    }

    pub fn preferred_text(&self) -> Option<&str> {
        match self.encoding {
            // auto 检测到 windows-1252 时常只是给任意单字节高位数据一个展示视图；
            // 这里保留 byte escape，避免把二进制字符串改成 UTF-8 文本。
            Some(StringEncoding::EncodingRs(enc))
                if std::ptr::eq(enc, encoding_rs::WINDOWS_1252) =>
            {
                None
            }
            _ => self.decoded_text(),
        }
    }

    pub fn as_utf8(&self) -> Option<&str> {
        std::str::from_utf8(&self.bytes).ok()
    }

    pub fn debug_literal(&self) -> String {
        self.preferred_text()
            .or_else(|| self.as_utf8())
            .map_or_else(
                || {
                    const HEX: &[u8; 16] = b"0123456789abcdef";
                    let mut literal = format!("<{} bytes: ", self.bytes.len()).into_bytes();
                    literal.reserve(self.bytes.len().saturating_mul(3));
                    if let Some((&first, rest)) = self.bytes.split_first() {
                        literal.push(HEX[usize::from(first >> 4)]);
                        literal.push(HEX[usize::from(first & 0x0f)]);
                        for byte in rest.iter().copied() {
                            literal.push(b' ');
                            literal.push(HEX[usize::from(byte >> 4)]);
                            literal.push(HEX[usize::from(byte & 0x0f)]);
                        }
                    }
                    literal.push(b'>');
                    String::from_utf8(literal).expect("hex debug literal must be ASCII")
                },
                |text| format!("{text:?}"),
            )
    }
}

impl From<&str> for LuaString {
    fn from(value: &str) -> Self {
        Self {
            bytes: value.as_bytes().into(),
            text: Some(value.into()),
            encoding: Some(StringEncoding::Utf8),
        }
    }
}

impl From<String> for LuaString {
    fn from(value: String) -> Self {
        let bytes = Arc::from(value.as_bytes());
        Self {
            bytes,
            text: Some(value.into()),
            encoding: Some(StringEncoding::Utf8),
        }
    }
}
