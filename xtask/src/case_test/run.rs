//! 编排 case-test 命令、筛选 case、启动 worker 并汇总结果；依赖 reporter/worker，不负责参数解析细节。

use super::*;

pub(crate) fn run<I>(args: I) -> Result<()>
where
    I: IntoIterator,
    I::Item: Into<String>,
{
    let args = args.into_iter().map(Into::into).collect::<Vec<_>>();
    if is_help_request(&args) {
        print_help();
        return Ok(());
    }

    let options = parse_args(args)?;
    let root = workspace_root()?;

    let build_started = Instant::now();
    let runner = build_case_runner(&root, &options.profile)?;
    let build_elapsed = build_started.elapsed();
    let catalog_started = Instant::now();
    let cases = list_cases(&root, &runner)?;
    let cases = cases
        .into_iter()
        .filter(|case| options.category == "all" || case.category == options.category)
        .filter(|case| options.tags.iter().all(|tag| case.tags.contains(tag)))
        .filter(|case| options.dialect == "all" || case.dialect == options.dialect)
        .filter(|case| matches_case_filters(case, &options.case_filters))
        .collect::<Vec<_>>();
    let catalog_elapsed = catalog_started.elapsed();

    if cases.is_empty() {
        let filter_text = if options.case_filters.is_empty() {
            "none".to_owned()
        } else {
            options.case_filters.join(", ")
        };
        bail!(
            "no cases matched filters: type={}, dialect={}, case-filter={filter_text}, tags={:?}",
            options.category,
            options.dialect,
            options.tags,
        );
    }

    if options.list || options.list_json {
        return print_catalog(&cases, options.list_json);
    }

    let started = Instant::now();
    let mut report_entries = Vec::new();
    let timeout = Duration::from_secs(options.timeout_seconds);
    let category_counts = describe_category_counts(&cases);
    let total = cases.len();
    let jobs = options.jobs.min(total).max(1);
    let reporter = Reporter::new(total, &options)?;
    reporter.announce_start(total, &options, jobs, &category_counts);

    let (event_rx, handles) = spawn_workers(
        root,
        runner,
        cases,
        options.output.label().to_owned(),
        options.recompile_rounds,
        timeout,
        jobs,
    )?;

    let mut active = 0usize;
    let mut completed = 0usize;
    let mut failed = 0usize;
    let mut timed_out = 0usize;
    let mut failure_counts = BTreeMap::new();
    let mut worker_error = None;
    let mut total_protos = 0usize;
    let mut failed_protos = 0usize;
    let mut last_persistent_progress = Instant::now();

    while completed < total && worker_error.is_none() {
        let heartbeat_wait = progress_heartbeat_wait(last_persistent_progress, Instant::now());
        match event_rx.recv_timeout(heartbeat_wait) {
            Ok(WorkerEvent::Started { case }) => {
                active += 1;
                if reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Started,
                ) {
                    last_persistent_progress = Instant::now();
                }
            }
            Ok(WorkerEvent::Finished { case, execution }) => {
                if options.report_json.is_some() {
                    let mut record = case.catalog_json();
                    record["elapsed_ms"] = serde_json::json!(execution.elapsed.as_millis());
                    record["outcome"] = serde_json::json!(match execution.outcome {
                        CaseOutcome::Passed => "passed",
                        CaseOutcome::Failed => "failed",
                        CaseOutcome::TimedOut => "timed-out",
                    });
                    record["classification"] = serde_json::json!(execution.classification);
                    record["detail"] = serde_json::json!(execution.rendered_failure);
                    report_entries.push(record);
                }
                active = active.saturating_sub(1);
                completed += 1;
                if reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Finished,
                ) {
                    last_persistent_progress = Instant::now();
                }

                match execution.outcome {
                    CaseOutcome::Passed => {
                        total_protos += execution.proto_count;
                    }
                    CaseOutcome::Failed => {
                        failed += 1;
                        total_protos += execution.proto_count;
                        failed_protos += execution.failed_proto_tags.len();
                        if let Some(classification) = execution.classification {
                            *failure_counts.entry(classification).or_insert(0) += 1;
                        }
                        reporter.emit_failure(
                            ProgressCounts { completed, total },
                            &case,
                            execution.outcome,
                            execution.rendered_failure.as_deref(),
                            &execution.failed_proto_tags,
                            options.timeout_seconds,
                            options.output,
                        );
                    }
                    CaseOutcome::TimedOut => {
                        failed += 1;
                        timed_out += 1;
                        *failure_counts.entry("timed-out".to_owned()).or_insert(0) += 1;
                        reporter.emit_failure(
                            ProgressCounts { completed, total },
                            &case,
                            execution.outcome,
                            execution.rendered_failure.as_deref(),
                            &execution.failed_proto_tags,
                            options.timeout_seconds,
                            options.output,
                        );
                    }
                }
            }
            Ok(WorkerEvent::WorkerError { case, error }) => {
                worker_error = Some(format!(
                    "worker failed while running {} {} {}: {error}",
                    case.category,
                    case.dialect,
                    case.display_path()
                ));
            }
            Err(mpsc::RecvTimeoutError::Timeout) => {}
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                worker_error =
                    Some("worker event channel closed before all cases finished".to_owned());
            }
        }
        if completed < total
            && worker_error.is_none()
            && progress_heartbeat_is_due(last_persistent_progress, Instant::now())
        {
            reporter.emit_heartbeat(completed, total, active);
            last_persistent_progress = Instant::now();
        }
    }

    for handle in handles {
        match handle.join() {
            Ok(Ok(())) => {}
            Ok(Err(error)) => {
                if worker_error.is_none() {
                    worker_error = Some(error.to_string());
                }
            }
            Err(_) => {
                if worker_error.is_none() {
                    worker_error = Some("case test worker panicked".to_owned());
                }
            }
        }
    }

    if let Some(path) = &options.report_json {
        report_entries.sort_by(|left, right| {
            left["path"]
                .as_str()
                .cmp(&right["path"].as_str())
                .then_with(|| left["id"].as_str().cmp(&right["id"].as_str()))
        });
        let report = serde_json::json!({
            "total": total, "completed": completed, "failed": failed, "timed_out": timed_out,
            "elapsed_ms": started.elapsed().as_millis(), "worker_error": worker_error,
            "profile": options.profile, "jobs": jobs,
            "build_elapsed_ms": build_elapsed.as_millis(),
            "catalog_elapsed_ms": catalog_elapsed.as_millis(),
            "entries": report_entries,
        });
        let file = std::fs::File::create(path)
            .with_context(|| format!("create report {}", path.display()))?;
        serde_json::to_writer_pretty(file, &report)?;
    }

    if let Some(error) = worker_error {
        bail!("{error}");
    }

    reporter.finish(
        total,
        failed,
        timed_out,
        &failure_counts,
        total_protos,
        failed_protos,
    );

    if failed == 0 {
        Ok(())
    } else {
        bail!("case runner failed with {failed} failing case(s)")
    }
}

pub(super) fn progress_heartbeat_wait(last_persistent: Instant, now: Instant) -> Duration {
    PROGRESS_HEARTBEAT_INTERVAL.saturating_sub(now.saturating_duration_since(last_persistent))
}

pub(super) fn progress_heartbeat_is_due(last_persistent: Instant, now: Instant) -> bool {
    now.saturating_duration_since(last_persistent) >= PROGRESS_HEARTBEAT_INTERVAL
}

pub(crate) fn print_help() {
    println!("usage:");
    println!("  cargo case-test");
    println!("  cargo case-test <help|--help|-h>");
    println!("                  [--type <category>] [--tag <tag>]...");
    println!("                  [--dialect <all|lua5.1|lua5.2|lua5.3|lua5.4|lua5.5|luajit|luau>]");
    println!("                  [--list | --list-json] [--report-json <path>]");
    println!("                  [--case-filter <substring>]...");
    println!("                  [--output <simple|verbose>] [--timeout-seconds <n>]");
    println!("                  [--progress <auto|on|off>] [--color <auto|always|never>]");
    println!("                  [--verbose]");
    println!("                  [--jobs <n>] (default: available parallelism, up to 8)");
    println!(
        "                  [--profile <cargo-profile>] (default: case-test; dev for fast rebuilds)"
    );
    println!("                  [--recompile-rounds <n>]");
}
