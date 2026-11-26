//! 这个二进制只负责承接命令行参数和本地调试流程。
//!
//! 实际反编译逻辑都放在库层，避免 CLI 行为和 library / wasm 绑定逐渐分叉。

mod cli;

fn main() {
    match cli::run(std::env::args_os()) {
        Ok(cli::CliExit::Ok) => {}
        Ok(cli::CliExit::PartialDiagnostic) => std::process::exit(2),
        Err(cli::CliError::HelpShown) => {}
        Err(error) => {
            eprintln!("error: {error}");
            std::process::exit(1);
        }
    }
}
