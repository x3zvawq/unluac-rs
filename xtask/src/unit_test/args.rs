//! 解析 unit-test CLI/环境选项并执行过滤与显示辅助；依赖 Options，不负责运行进程；例如校验 jobs/timeout 非零及 progress/color 模式。

use super::*;

pub(super) fn parse_args<I>(args: I) -> Result<Options>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    let mut options = Options {
        suite: "all".to_owned(),
        dialect: "all".to_owned(),
        case_filters: Vec::new(),
        output: parse_env_or_default(OUTPUT_ENV, "simple", FailureOutputMode::parse)?,
        timeout_seconds: 25,
        progress: parse_env_or_default(PROGRESS_ENV, "auto", ProgressMode::parse)?,
        color: parse_env_or_default(COLOR_ENV, "auto", ColorMode::parse)?,
        plain_progress_detail: PlainProgressDetail::Sparse,
        jobs: 1,
        recompile_rounds: 1,
    };

    let mut cursor = 0;
    while cursor < args.len() {
        match args[cursor].as_str() {
            "--suite" => {
                cursor += 1;
                options.suite = args
                    .get(cursor)
                    .context("missing value for `--suite`")?
                    .clone();
            }
            "--dialect" => {
                cursor += 1;
                options.dialect = args
                    .get(cursor)
                    .context("missing value for `--dialect`")?
                    .clone();
            }
            "--case-filter" => {
                cursor += 1;
                options.case_filters.push(
                    args.get(cursor)
                        .context("missing value for `--case-filter`")?
                        .clone(),
                );
            }
            "--output" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--output`")?;
                options.output = FailureOutputMode::parse(value)?;
            }
            "--timeout-seconds" => {
                cursor += 1;
                let value = args
                    .get(cursor)
                    .context("missing value for `--timeout-seconds`")?;
                options.timeout_seconds = value
                    .parse::<u64>()
                    .with_context(|| format!("invalid timeout seconds: {value}"))?;
                if options.timeout_seconds == 0 {
                    bail!("timeout seconds must be greater than zero");
                }
            }
            "--progress" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--progress`")?;
                options.progress = ProgressMode::parse(value)?;
            }
            "--color" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--color`")?;
                options.color = ColorMode::parse(value)?;
            }
            "--jobs" => {
                cursor += 1;
                let value = args.get(cursor).context("missing value for `--jobs`")?;
                options.jobs = value
                    .parse::<usize>()
                    .with_context(|| format!("invalid jobs value: {value}"))?;
                if options.jobs == 0 {
                    bail!("jobs must be greater than zero");
                }
            }
            "--recompile-rounds" => {
                cursor += 1;
                let value = args
                    .get(cursor)
                    .context("missing value for `--recompile-rounds`")?;
                options.recompile_rounds = value
                    .parse::<u32>()
                    .with_context(|| format!("invalid recompile rounds: {value}"))?;
            }
            "--verbose" => {
                options.plain_progress_detail = PlainProgressDetail::Verbose;
            }
            other => bail!("unsupported `test-unit` option: {other}"),
        }
        cursor += 1;
    }

    Ok(options)
}

pub(super) fn is_help_request(args: &[String]) -> bool {
    matches!(args, [flag] if matches!(flag.as_str(), "help" | "--help" | "-h"))
}

pub(super) fn parse_env_or_default<T>(
    key: &str,
    default: &str,
    parse: impl Fn(&str) -> Result<T>,
) -> Result<T> {
    match env::var(key) {
        Ok(value) => parse(value.trim()).with_context(|| format!("invalid {key} value")),
        Err(env::VarError::NotPresent) => parse(default),
        Err(error) => bail!("failed to read {key}: {error}"),
    }
}

pub(super) fn progress_is_enabled(mode: ProgressMode) -> bool {
    match mode {
        ProgressMode::On => true,
        ProgressMode::Off => false,
        ProgressMode::Auto => stderr_supports_live_updates(),
    }
}

pub(super) fn color_is_enabled(mode: ColorMode) -> bool {
    match mode {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => env::var_os("NO_COLOR").is_none() && stderr_supports_live_updates(),
    }
}

pub(super) fn stderr_supports_live_updates() -> bool {
    io::stderr().is_terminal() && env::var("TERM").map_or(true, |term| term != "dumb")
}

pub(super) fn matches_case_filters(case: &UnitCaseDescriptor, case_filters: &[String]) -> bool {
    case_filters.is_empty()
        || case_filters.iter().any(|case_filter| {
            case.path.contains(case_filter)
                || case
                    .variant
                    .as_ref()
                    .is_some_and(|variant| variant.contains(case_filter))
        })
}

pub(super) fn sorted_failure_counts(
    failure_counts: &BTreeMap<String, usize>,
) -> Vec<(&str, usize)> {
    let mut entries = failure_counts
        .iter()
        .map(|(label, count)| (label.as_str(), *count))
        .collect::<Vec<_>>();
    entries.sort_by(|left, right| right.1.cmp(&left.1).then_with(|| left.0.cmp(right.0)));
    entries
}

pub(super) fn describe_suite_counts(cases: &[UnitCaseDescriptor]) -> String {
    let mut counts = BTreeMap::new();
    for case in cases {
        *counts.entry(case.suite.as_str()).or_insert(0usize) += 1;
    }
    counts
        .into_iter()
        .map(|(suite, count)| format!("{suite}={count}"))
        .collect::<Vec<_>>()
        .join(", ")
}
