//! 编排 unit-test 命令、筛选 case、启动 worker 并汇总结果；依赖 reporter/worker，不负责参数解析细节；例如并行运行 regression 并统计失败分类。

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

    build_unit_case_runner(&root)?;
    let runner = unit_case_runner_path(&root);
    let cases = list_unit_cases(&root, &runner)?;
    let cases = cases
        .into_iter()
        .filter(|case| options.suite == "all" || case.suite == options.suite)
        .filter(|case| options.dialect == "all" || case.dialect == options.dialect)
        .filter(|case| matches_case_filters(case, &options.case_filters))
        .collect::<Vec<_>>();

    if cases.is_empty() {
        let filter_text = if options.case_filters.is_empty() {
            "none".to_owned()
        } else {
            options.case_filters.join(", ")
        };
        bail!(
            "no unit cases matched filters: suite={}, dialect={}, case-filter={filter_text}",
            options.suite,
            options.dialect
        );
    }

    let timeout = Duration::from_secs(options.timeout_seconds);
    let suite_counts = describe_suite_counts(&cases);
    let total = cases.len();
    let jobs = options.jobs.min(total).max(1);
    let reporter = Reporter::new(total, &options)?;
    reporter.announce_start(total, &options, jobs, &suite_counts);

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

    while completed < total && worker_error.is_none() {
        match event_rx.recv() {
            Ok(WorkerEvent::Started { case }) => {
                active += 1;
                reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Started,
                );
            }
            Ok(WorkerEvent::Finished { case, execution }) => {
                active = active.saturating_sub(1);
                completed += 1;
                reporter.update_progress(
                    completed,
                    total,
                    active,
                    &case,
                    ProgressEventKind::Finished,
                );

                match execution.outcome {
                    UnitCaseOutcome::Passed => {
                        total_protos += execution.proto_count;
                    }
                    UnitCaseOutcome::Failed => {
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
                    UnitCaseOutcome::TimedOut => {
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
                    case.suite,
                    case.dialect,
                    case.display_path()
                ));
            }
            Err(_) => {
                worker_error =
                    Some("worker event channel closed before all cases finished".to_owned());
            }
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
                    worker_error = Some("unit test worker panicked".to_owned());
                }
            }
        }
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
        bail!("unit runner failed with {failed} failing case(s)")
    }
}

pub(crate) fn print_help() {
    println!("usage:");
    println!("  cargo unit-test");
    println!("  cargo unit-test <help|--help|-h>");
    println!("                  [--suite <all|unit|regression>]");
    println!("                  [--dialect <all|lua5.1|lua5.2|lua5.3|lua5.4|lua5.5>]");
    println!("                  [--case-filter <substring>]...");
    println!("                  [--output <simple|verbose>] [--timeout-seconds <n>]");
    println!("                  [--progress <auto|on|off>] [--color <auto|always|never>]");
    println!("                  [--verbose]");
    println!("                  [--jobs <n>]");
    println!("                  [--recompile-rounds <n>]");
}
