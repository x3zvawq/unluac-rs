#![forbid(unsafe_code)]

use std::env;
use std::process;

#[path = "mod.rs"]
mod support;

use support::{
    UnitSuite, find_unit_case_spec, format_case_failure, run_unit_case, unit_case_specs,
};

enum CommandLine {
    List,
    Run {
        report: ReportFormat,
        suite: String,
        dialect: String,
        case_path: String,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReportFormat {
    Human,
    Machine,
}

impl ReportFormat {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "human" => Ok(Self::Human),
            "machine" => Ok(Self::Machine),
            _ => Err(format!(
                "unknown report format: {raw} (expected `human` or `machine`)"
            )),
        }
    }
}

enum ExitKind {
    Success,
    Failure,
}

fn main() {
    match run() {
        Ok(ExitKind::Success) => {}
        Ok(ExitKind::Failure) => process::exit(1),
        Err(error) => {
            eprintln!("{error}");
            process::exit(2);
        }
    }
}

fn run() -> Result<ExitKind, String> {
    match parse_args(env::args().skip(1))? {
        CommandLine::List => {
            for spec in unit_case_specs() {
                println!(
                    "{}\t{}\t{}",
                    spec.suite.label(),
                    spec.entry.dialect.label(),
                    spec.entry.path
                );
            }
            Ok(ExitKind::Success)
        }
        CommandLine::Run {
            report,
            suite,
            dialect,
            case_path,
        } => {
            let suite = UnitSuite::parse(&suite)?;
            let spec = find_unit_case_spec(suite, &dialect, &case_path).ok_or_else(|| {
                format!(
                    "unknown unit case spec: suite={}, dialect={}, case={}",
                    suite.label(),
                    dialect,
                    case_path
                )
            })?;

            match run_unit_case(spec) {
                Ok(()) => Ok(ExitKind::Success),
                Err(failure) => {
                    let rendered = format_case_failure(spec.entry.path, &failure);
                    match report {
                        ReportFormat::Human => eprintln!("{rendered}"),
                        ReportFormat::Machine => {
                            println!("kind\t{}", failure.kind().label());
                            print!("{rendered}");
                            if !rendered.ends_with('\n') {
                                println!();
                            }
                        }
                    }
                    Ok(ExitKind::Failure)
                }
            }
        }
    }
}

fn parse_args<I>(args: I) -> Result<CommandLine, String>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();

    if matches!(args.as_slice(), [flag] if flag == "--list") {
        return Ok(CommandLine::List);
    }

    let mut report = ReportFormat::Human;
    let mut suite = None;
    let mut dialect = None;
    let mut case_path = None;
    let mut cursor = 0;

    while cursor < args.len() {
        match args[cursor].as_str() {
            "--report" => {
                cursor += 1;
                let value = args
                    .get(cursor)
                    .ok_or_else(|| "missing value for `--report`".to_owned())?;
                report = ReportFormat::parse(value)?;
            }
            "--suite" => {
                cursor += 1;
                suite = Some(
                    args.get(cursor)
                        .ok_or_else(|| "missing value for `--suite`".to_owned())?
                        .clone(),
                );
            }
            "--dialect" => {
                cursor += 1;
                dialect = Some(
                    args.get(cursor)
                        .ok_or_else(|| "missing value for `--dialect`".to_owned())?
                        .clone(),
                );
            }
            "--case" => {
                cursor += 1;
                case_path = Some(
                    args.get(cursor)
                        .ok_or_else(|| "missing value for `--case`".to_owned())?
                        .clone(),
                );
            }
            other => {
                return Err(format!("unsupported unit_case_runner option: {other}"));
            }
        }
        cursor += 1;
    }

    match (suite, dialect, case_path) {
        (Some(suite), Some(dialect), Some(case_path)) => Ok(CommandLine::Run {
            report,
            suite,
            dialect,
            case_path,
        }),
        _ => Err(
            "usage: unit_case_runner --list | unit_case_runner [--report <human|machine>] --suite <suite> --dialect <dialect> --case <path>"
                .to_owned(),
        ),
    }
}
