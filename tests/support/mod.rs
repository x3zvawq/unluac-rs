//! 这个模块承载 tests 目录下共享的轻量辅助函数。
//!
//! 这些 helper 只负责测试夹具解码这类稳定、无业务语义的重复逻辑，避免 unit
//! 和 regression 两套入口各自复制同一份样板代码。

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

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

/// 使用 vendored 的 `luac` 把某个仓库内 Lua case 编译成测试 chunk。
#[allow(dead_code)]
pub(crate) fn compile_lua_case(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, true)
}

#[allow(dead_code)]
pub(crate) fn compile_lua_case_with_debug(dialect_label: &str, source_relative: &str) -> Vec<u8> {
    compile_lua_case_inner(dialect_label, source_relative, false)
}

static TEST_CHUNK_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn compile_lua_case_inner(
    dialect_label: &str,
    source_relative: &str,
    strip_debug: bool,
) -> Vec<u8> {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let source = repo_root.join(source_relative);
    let luac = repo_root
        .join("lua")
        .join("build")
        .join(dialect_label)
        .join("luac");
    assert!(
        luac.exists(),
        "missing bundled luac for {dialect_label}: {}",
        luac.display()
    );

    let output = test_chunk_output_path(&repo_root, dialect_label, &source, strip_debug);
    fs::create_dir_all(
        output
            .parent()
            .expect("test chunk output path should always have a parent"),
    )
    .expect("should create test chunk output directory");

    let status = Command::new(&luac)
        .args(strip_debug.then_some("-s"))
        .arg("-o")
        .arg(&output)
        .arg(&source)
        .status()
        .expect("should spawn bundled luac for test case");
    assert!(
        status.success(),
        "bundled luac failed for {} with status {status}",
        source.display()
    );

    fs::read(&output).unwrap_or_else(|error| {
        panic!(
            "should read compiled test chunk {}: {error}",
            output.display()
        )
    })
}

#[allow(dead_code)]
fn test_chunk_output_path(
    repo_root: &Path,
    dialect_label: &str,
    source: &Path,
    strip_debug: bool,
) -> PathBuf {
    let unique = TEST_CHUNK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let relative = source
        .strip_prefix(repo_root)
        .expect("test source should stay inside repo root");
    repo_root
        .join("target")
        .join("unluac-tests")
        .join(dialect_label)
        .join(if strip_debug { "stripped" } else { "debug" })
        .join(relative)
        .with_extension(format!("{}.out", unique))
}
