//! 按统一 manifest 的实例 ID 执行源码合同；列表提供主题索引，展示字段不参与重建配置。

#![forbid(unsafe_code)]

use std::io::Read;
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::{env, io, process, thread};
use unluac_test_support::{
    LuaCaseId, case_entries, find_case_entry, format_case_failure, inspect_case_readability,
    run_case, validate_case_catalog,
};

enum CommandLine {
    List,
    Run {
        machine: bool,
        watch_parent_stdin: bool,
        id: LuaCaseId,
    },
}

fn main() {
    match run() {
        Ok(true) => {}
        Ok(false) => process::exit(1),
        Err(error) => {
            eprintln!("{error}");
            process::exit(2);
        }
    }
}

struct NormalExitGuard(Option<Arc<AtomicBool>>);

impl Drop for NormalExitGuard {
    fn drop(&mut self) {
        if let Some(flag) = &self.0 {
            flag.store(true, Ordering::Release);
        }
    }
}

/// 监听父进程（xtask）持有的 stdin 管道；一旦父进程被 Ctrl-C / SIGTERM / SIGKILL 终止，
/// 内核会立即向本进程投递 stdin EOF，此处立刻终止本进程组（含正在运行的 lua/luac 孙进程）。
fn spawn_parent_stdin_watchdog() -> NormalExitGuard {
    let finished = Arc::new(AtomicBool::new(false));
    let flag = Arc::clone(&finished);
    let _ = thread::Builder::new()
        .name("parent-stdin-watchdog".to_owned())
        .spawn(move || {
            let mut stdin = io::stdin();
            let mut buf = [0u8; 16];
            loop {
                match stdin.read(&mut buf) {
                    Ok(0) | Err(_) => {
                        if !flag.load(Ordering::Acquire) {
                            terminate_self_process_tree();
                            process::exit(130);
                        }
                        break;
                    }
                    Ok(_) => {}
                }
            }
        });
    NormalExitGuard(Some(finished))
}

fn terminate_self_process_tree() {
    #[cfg(unix)]
    {
        // xtask 通过 `process_group(0)` 将本 runner 设为独立进程组组长，
        // 向 `-pid` 发送 SIGKILL 可原子级清除所有派生中的 lua/luac/luajit/luau 进程。
        let pgid_target = format!("-{}", process::id());
        let _ = process::Command::new("kill")
            .args(["-s", "KILL", "--", &pgid_target])
            .status();
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;

        let _ = process::Command::new("taskkill.exe")
            .args(["/PID", &process::id().to_string(), "/T", "/F"])
            .creation_flags(0x0800_0000) // CREATE_NO_WINDOW
            .status();
    }
}

fn run() -> Result<bool, String> {
    match parse_args(env::args().skip(1))? {
        CommandLine::List => {
            validate_case_catalog()?;
            let entries = case_entries();
            let readability = inspect_case_readability(&entries)?;
            for entry in entries {
                let summary = readability[entry.path];
                println!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                    entry.id.0,
                    entry.category(),
                    <&'static str>::from(entry.dialect),
                    entry.path,
                    entry.variant_label(),
                    entry.tags.join(","),
                    entry.purpose,
                    entry.configuration_description(),
                    summary.total,
                    summary.ast,
                );
            }
            Ok(true)
        }
        CommandLine::Run {
            machine,
            watch_parent_stdin,
            id,
        } => {
            let _watchdog = watch_parent_stdin.then(spawn_parent_stdin_watchdog);
            let entry =
                find_case_entry(id).ok_or_else(|| format!("unknown case instance id: {}", id.0))?;
            match run_case(entry) {
                Ok(success) => {
                    if machine {
                        println!("proto-count\t{}", success.proto_count);
                    }
                    Ok(true)
                }
                Err(failure) => {
                    let rendered = format_case_failure(entry.path, &failure);
                    if machine {
                        println!("kind\t{}", failure.kind().label());
                        println!("proto-count\t{}", failure.proto_count());
                        if !failure.failed_proto_tags().is_empty() {
                            println!("failed-protos\t{}", failure.failed_proto_tags().join(","));
                        }
                        print!("{rendered}");
                        if !rendered.ends_with('\n') {
                            println!();
                        }
                    } else {
                        eprintln!("{rendered}");
                    }
                    Ok(false)
                }
            }
        }
    }
}

fn parse_args(args: impl Iterator<Item = String>) -> Result<CommandLine, String> {
    let mut args = args.peekable();
    if args.peek().is_some_and(|arg| arg == "--list") {
        args.next();
        return if args.next().is_none() {
            Ok(CommandLine::List)
        } else {
            Err("--list takes no additional arguments".to_owned())
        };
    }
    let mut machine = false;
    let mut watch_parent_stdin = false;
    let mut id = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--report" => {
                machine = match args.next().as_deref() {
                    Some("human") => false,
                    Some("machine") => true,
                    _ => return Err("--report requires human or machine".to_owned()),
                };
            }
            "--watch-parent-stdin" => {
                watch_parent_stdin = true;
            }
            "--id" => {
                let value = args.next().ok_or("missing value for --id")?;
                id = Some(LuaCaseId(
                    value
                        .parse()
                        .map_err(|_| format!("invalid case id: {value}"))?,
                ));
            }
            _ => return Err(format!("unsupported case_runner option: {arg}")),
        }
    }
    id.map(|id| CommandLine::Run {
        machine,
        watch_parent_stdin,
        id,
    })
    .ok_or_else(|| {
        "usage: case_runner --list | case_runner [--report human|machine] [--watch-parent-stdin] --id <id>".to_owned()
    })
}
