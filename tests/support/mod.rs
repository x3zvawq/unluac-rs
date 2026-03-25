//! 这个模块承载 tests 目录下共享的轻量辅助函数。
//!
//! 这些 helper 只负责测试夹具解码这类稳定、无业务语义的重复逻辑，避免 unit
//! 和 regression 两套入口各自复制同一份样板代码。

#[allow(dead_code)]
pub(crate) mod case_manifest;

/// 把嵌入测试文件里的十六进制 fixture 解码成原始字节。
pub(crate) fn decode_hex(hex: &str) -> Vec<u8> {
    let compact = hex
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    assert_eq!(compact.len() % 2, 0, "fixture hex should have even length");

    compact
        .as_bytes()
        .chunks(2)
        .map(|pair| {
            let digits = std::str::from_utf8(pair).expect("fixture hex should stay ascii");
            u8::from_str_radix(digits, 16).expect("fixture hex should decode")
        })
        .collect()
}
