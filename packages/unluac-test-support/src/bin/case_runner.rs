//! 按统一 manifest 的实例 ID 执行源码合同；列表提供主题索引，展示字段不参与重建配置。

#![forbid(unsafe_code)]

use std::{env, process};
use unluac_test_support::{
    LuaCaseId, case_entries, find_case_entry, format_case_failure, inspect_case_readability,
    run_case, validate_case_catalog,
};

enum CommandLine {
    List,
    Run { machine: bool, id: LuaCaseId },
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
        CommandLine::Run { machine, id } => {
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
    id.map(|id| CommandLine::Run { machine, id })
        .ok_or_else(|| {
            "usage: case_runner --list | case_runner [--report human|machine] --id <id>".to_owned()
        })
}
