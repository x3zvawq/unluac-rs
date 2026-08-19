//! 构建 case runner、枚举 case、调度 worker、处理超时并解析机器输出；依赖子进程与 channel，不负责终端渲染；例如杀死超时 case 并归一化失败详情。

use super::*;

pub(super) fn workspace_root() -> Result<PathBuf> {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf)
        .context("failed to resolve workspace root")
}

pub(super) fn build_unit_case_runner(root: &Path) -> Result<()> {
    run_command(
        "cargo",
        [
            "build",
            "--quiet",
            "-p",
            "unluac-test-support",
            "--bin",
            "unit_case_runner",
        ],
        root,
    )
}

pub(super) fn unit_case_runner_path(root: &Path) -> PathBuf {
    root.join("target")
        .join("debug")
        .join(format!("unit_case_runner{}", std::env::consts::EXE_SUFFIX))
}

pub(super) fn list_unit_cases(root: &Path, runner: &Path) -> Result<Vec<UnitCaseDescriptor>> {
    let output = Command::new(runner)
        .arg("--list")
        .current_dir(root)
        .output()
        .with_context(|| format!("failed to spawn `{}`", runner.display()))?;

    if !output.status.success() {
        bail!(
            "`{}` --list failed with status {}",
            runner.display(),
            output.status
        );
    }

    let stdout = String::from_utf8(output.stdout).context("unit case list is not valid UTF-8")?;
    stdout
        .lines()
        .map(|line| {
            let mut parts = line.splitn(4, '\t');
            let suite = parts
                .next()
                .context("missing suite column in unit case list")?;
            let dialect = parts
                .next()
                .context("missing dialect column in unit case list")?;
            let path = parts
                .next()
                .context("missing path column in unit case list")?;
            let variant = parts
                .next()
                .filter(|variant| !variant.is_empty())
                .map(str::to_owned);
            Ok(UnitCaseDescriptor {
                suite: suite.to_owned(),
                dialect: dialect.to_owned(),
                path: path.to_owned(),
                variant,
            })
        })
        .collect()
}

type WorkerHandles = Vec<thread::JoinHandle<Result<()>>>;
type SpawnedWorkers = (mpsc::Receiver<WorkerEvent>, WorkerHandles);

pub(super) fn spawn_workers(
    root: PathBuf,
    runner: PathBuf,
    cases: Vec<UnitCaseDescriptor>,
    output_mode: String,
    recompile_rounds: u32,
    timeout: Duration,
    jobs: usize,
) -> Result<SpawnedWorkers> {
    let (task_tx, task_rx) = mpsc::channel::<ScheduledCase>();
    let (event_tx, event_rx) = mpsc::channel::<WorkerEvent>();
    let task_rx = Arc::new(Mutex::new(task_rx));
    let mut handles = Vec::with_capacity(jobs);

    for _ in 0..jobs {
        let root = root.clone();
        let runner = runner.clone();
        let output_mode = output_mode.clone();
        let task_rx = Arc::clone(&task_rx);
        let event_tx = event_tx.clone();
        handles.push(thread::spawn(move || {
            loop {
                let scheduled = {
                    let receiver = task_rx
                        .lock()
                        .map_err(|_| anyhow::anyhow!("task receiver mutex poisoned"))?;
                    match receiver.recv() {
                        Ok(scheduled) => scheduled,
                        Err(_) => break,
                    }
                };

                event_tx
                    .send(WorkerEvent::Started {
                        case: scheduled.case.clone(),
                    })
                    .map_err(|_| anyhow::anyhow!("worker event channel closed"))?;

                match run_unit_case_with_timeout(
                    &root,
                    &runner,
                    &scheduled.case,
                    &output_mode,
                    recompile_rounds,
                    timeout,
                ) {
                    Ok(execution) => event_tx
                        .send(WorkerEvent::Finished {
                            case: scheduled.case,
                            execution,
                        })
                        .map_err(|_| anyhow::anyhow!("worker event channel closed"))?,
                    Err(error) => {
                        let error = error.to_string();
                        let _ = event_tx.send(WorkerEvent::WorkerError {
                            case: scheduled.case,
                            error,
                        });
                        break;
                    }
                }
            }

            Ok(())
        }));
    }

    drop(event_tx);

    for case in cases {
        task_tx.send(ScheduledCase { case }).map_err(|_| {
            anyhow::anyhow!("worker task channel closed before scheduling all cases")
        })?;
    }
    drop(task_tx);

    Ok((event_rx, handles))
}

pub(super) fn run_unit_case_with_timeout(
    root: &Path,
    runner: &Path,
    case: &UnitCaseDescriptor,
    output_mode: &str,
    recompile_rounds: u32,
    timeout: Duration,
) -> Result<UnitCaseExecution> {
    let mut command = Command::new(runner);
    command.args([
        "--report",
        "machine",
        "--suite",
        case.suite.as_str(),
        "--dialect",
        case.dialect.as_str(),
        "--case",
        case.path.as_str(),
    ]);
    if let Some(variant) = &case.variant {
        command.args(["--variant", variant]);
    }
    let mut child = command
        .env(OUTPUT_ENV, output_mode)
        .env(RECOMPILE_ROUNDS_ENV, recompile_rounds.to_string())
        .current_dir(root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("failed to spawn `{}`", runner.display()))?;

    let start = Instant::now();
    loop {
        if let Some(status) = child
            .try_wait()
            .with_context(|| format!("failed to poll `{}`", runner.display()))?
        {
            let output = child
                .wait_with_output()
                .with_context(|| format!("failed to read `{}` output", runner.display()))?;
            return match status.code() {
                Some(0) => {
                    let proto_count = parse_machine_success(&output);
                    Ok(UnitCaseExecution {
                        outcome: UnitCaseOutcome::Passed,
                        classification: None,
                        rendered_failure: None,
                        proto_count,
                        failed_proto_tags: Vec::new(),
                    })
                }
                Some(1) => {
                    let failure = parse_machine_failure(&output)?;
                    Ok(UnitCaseExecution {
                        outcome: UnitCaseOutcome::Failed,
                        classification: Some(failure.classification),
                        rendered_failure: Some(failure.rendered),
                        proto_count: failure.proto_count,
                        failed_proto_tags: failure.failed_proto_tags,
                    })
                }
                _ => bail!(
                    "unit case runner exited unexpectedly for {} {} {} with status {}",
                    case.suite,
                    case.dialect,
                    case.display_path(),
                    status
                ),
            };
        }

        if start.elapsed() >= timeout {
            child
                .kill()
                .with_context(|| format!("failed to kill timed out `{}`", runner.display()))?;
            let output = child.wait_with_output().with_context(|| {
                format!("failed to read timed out `{}` output", runner.display())
            })?;
            let rendered_failure = preferred_child_output(&output);
            return Ok(UnitCaseExecution {
                outcome: UnitCaseOutcome::TimedOut,
                classification: Some("timed-out".to_owned()),
                rendered_failure: (!rendered_failure.trim().is_empty()).then_some(rendered_failure),
                proto_count: 0,
                failed_proto_tags: Vec::new(),
            });
        }

        thread::sleep(Duration::from_millis(50));
    }
}

/// 解析 machine 模式成功输出中的 `proto-count` 行。
pub(super) fn parse_machine_success(output: &std::process::Output) -> usize {
    let stdout = String::from_utf8_lossy(&output.stdout);
    for line in stdout.lines() {
        if let Some(v) = line.strip_prefix("proto-count\t") {
            return v.trim().parse().unwrap_or(0);
        }
    }
    0
}

/// 解析 machine 模式失败输出：支持 `kind`、`proto-count`、`failed-protos` 三种头部行，
/// 余下内容作为渲染后的失败详情。
pub(super) fn parse_machine_failure(output: &std::process::Output) -> Result<MachineFailure> {
    let stdout = String::from_utf8(output.stdout.clone())
        .context("unit case runner machine output is not valid UTF-8")?;
    let trimmed = stdout.trim_end_matches('\n');

    let mut classification = None;
    let mut proto_count = 0usize;
    let mut failed_proto_tags = Vec::new();
    let mut body_start = 0usize;

    for (i, line) in trimmed.lines().enumerate() {
        if let Some(v) = line.strip_prefix("kind\t") {
            classification = Some(v.trim().to_owned());
            body_start = i + 1;
        } else if let Some(v) = line.strip_prefix("proto-count\t") {
            proto_count = v.trim().parse().unwrap_or(0);
            body_start = i + 1;
        } else if let Some(v) = line.strip_prefix("failed-protos\t") {
            failed_proto_tags = v
                .split(',')
                .map(|s| s.trim().to_owned())
                .filter(|s| !s.is_empty())
                .collect();
            body_start = i + 1;
        } else {
            break;
        }
    }

    let classification =
        classification.context("unit case runner machine output is missing kind header")?;
    let rendered: String = trimmed
        .lines()
        .skip(body_start)
        .collect::<Vec<_>>()
        .join("\n");
    let rendered = rendered.trim().to_owned();
    if classification.is_empty() || rendered.is_empty() {
        bail!("unit case runner machine output contained an empty failure payload");
    }

    Ok(MachineFailure {
        classification,
        rendered,
        proto_count,
        failed_proto_tags,
    })
}

pub(super) fn preferred_child_output(output: &std::process::Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr).trim().to_owned();
    let stdout = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if !stderr.is_empty() { stderr } else { stdout }
}

pub(super) fn progress_message(
    palette: Palette,
    completed: usize,
    total: usize,
    active: usize,
    case: &UnitCaseDescriptor,
) -> String {
    format!(
        "[{completed}/{total}]\tactive: {active}\tdialect: {}\tcase: {}",
        palette.cyan(&case.dialect),
        case.display_path()
    )
}

pub(super) fn sparse_progress_message(
    palette: Palette,
    completed: usize,
    total: usize,
    active: usize,
) -> String {
    format!(
        "[{completed}/{total}]\tactive: {active}\t{}",
        palette.cyan("progress")
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ProgressEventKind {
    Started,
    Finished,
}

pub(super) fn should_emit_sparse_plain_progress(
    event: ProgressEventKind,
    completed: usize,
    total: usize,
) -> bool {
    matches!(event, ProgressEventKind::Finished)
        && completed > 0
        && (completed == total || completed.is_multiple_of(100))
}

pub(super) fn normalize_runner_failure(
    raw: &str,
    case: &UnitCaseDescriptor,
    output_mode: FailureOutputMode,
) -> String {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return "runner exited with failure but did not report details".to_owned();
    }

    match output_mode {
        FailureOutputMode::Simple => trimmed
            .strip_prefix(&format!("{} :: ", case.path))
            .unwrap_or(trimmed)
            .to_owned(),
        FailureOutputMode::Verbose => trimmed
            .strip_prefix(&format!("case: {}\n", case.path))
            .unwrap_or(trimmed)
            .to_owned(),
    }
}

pub(super) fn run_command<I, S>(program: &str, args: I, cwd: &Path) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let status = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .status()
        .with_context(|| format!("failed to spawn `{program}` in {}", cwd.display()))?;

    if status.success() {
        Ok(())
    } else {
        bail!("`{program}` failed with status {status}")
    }
}
