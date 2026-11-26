//! `unluac` 库基础调用示例：读取任意受支持方言的 Lua 字节码并输出反编译源码。
//!
//! 用法：`cargo run --example basic -- <path/to/chunk.luac>`

use std::env;
use std::fs;
use std::process::ExitCode;

use unluac::decompile::{DecompileOptions, decompile};
use unluac::generate::GenerateMode;

fn main() -> ExitCode {
    let Some(path) = env::args().nth(1) else {
        eprintln!("Usage: cargo run --example basic -- <path/to/chunk.luac>");
        return ExitCode::FAILURE;
    };

    let bytes = match fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("failed to read {path}: {error}");
            return ExitCode::FAILURE;
        }
    };

    let mut options = DecompileOptions::default();
    options.generate.mode = GenerateMode::Permissive;

    match decompile(&bytes, options) {
        Ok(result) => {
            if let Some(generated) = result.state.generated.as_ref() {
                print!("{}", generated.source);
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("failed to decompile {path}: {error}");
            ExitCode::FAILURE
        }
    }
}
