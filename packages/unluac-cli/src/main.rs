//! 这个二进制只负责承接命令行参数和本地调试流程。
//!
//! 实际反编译逻辑都放在库层，避免 CLI 行为和 library / wasm 绑定逐渐分叉。

mod cli;

fn main() {
    if let Err(error) = cli::run(std::env::args_os()) {
        if matches!(error, cli::CliError::HelpShown) {
            return;
        }
        eprintln!("error: {error}");
        std::process::exit(1);
    }
}
