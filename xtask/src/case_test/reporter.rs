//! 渲染进度、失败详情、超时与最终汇总；依赖终端能力和 Options，不负责调度 case。

use super::*;

/// 用户索引按源码聚合，完整实例仍嵌入 JSON；不按 variant 展示标签合并配置。
pub(super) fn print_catalog(cases: &[CaseDescriptor], json: bool) -> Result<()> {
    let mut grouped: BTreeMap<&str, Vec<&CaseDescriptor>> = BTreeMap::new();
    for case in cases {
        grouped.entry(&case.path).or_default().push(case);
    }
    if json {
        let catalog = grouped
            .values()
            .map(|entries| {
                let case = entries[0];
                let instances = entries
                    .iter()
                    .map(|entry| {
                        serde_json::json!({
                            "id": entry.id, "dialect": entry.dialect, "variant": entry.variant,
                            "configuration": entry.configuration,
                        })
                    })
                    .collect::<Vec<_>>();
                serde_json::json!({
                    "path": case.path, "type": case.category, "tags": case.tags,
                    "purpose": case.purpose, "readability_assertions": case.readability_assertions,
                    "ast_assertions": case.ast_assertions, "instances": instances,
                })
            })
            .collect::<Vec<_>>();
        serde_json::to_writer_pretty(io::stdout().lock(), &catalog)?;
        println!();
    } else {
        println!("type\tpath\tinstances\tassertions\tast\ttags\tpurpose");
        for entries in grouped.values() {
            let case = entries[0];
            println!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                case.category,
                case.path,
                entries.len(),
                case.readability_assertions,
                case.ast_assertions,
                case.tags.join(","),
                case.purpose
            );
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Palette {
    enabled: bool,
}

impl Palette {
    pub(super) fn red(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.red().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    pub(super) fn green(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.green().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    pub(super) fn yellow(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.yellow().bold().to_string()
        } else {
            text.to_owned()
        }
    }

    pub(super) fn cyan(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.cyan().to_string()
        } else {
            text.to_owned()
        }
    }

    pub(super) fn magenta(self, text: impl AsRef<str>) -> String {
        let text = text.as_ref();
        if self.enabled {
            text.magenta().to_string()
        } else {
            text.to_owned()
        }
    }
}

pub(super) enum ReporterMode {
    Interactive(ProgressBar),
    Plain,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ProgressCounts {
    pub(super) completed: usize,
    pub(super) total: usize,
}

pub(super) struct Reporter {
    mode: ReporterMode,
    palette: Palette,
    plain_progress_detail: PlainProgressDetail,
    progress_enabled: bool,
}

impl Reporter {
    pub(super) fn new(total: usize, options: &Options) -> Result<Self> {
        let palette = Palette {
            enabled: color_is_enabled(options.color),
        };
        let progress_enabled = !matches!(options.progress, ProgressMode::Off);
        let mode = if progress_enabled && stderr_supports_live_updates() {
            let progress =
                ProgressBar::with_draw_target(Some(total as u64), ProgressDrawTarget::stderr());
            progress.set_style(
                ProgressStyle::with_template("{spinner} {msg}")
                    .context("failed to build case test progress style")?,
            );
            ReporterMode::Interactive(progress)
        } else {
            ReporterMode::Plain
        };
        Ok(Self {
            mode,
            palette,
            plain_progress_detail: options.plain_progress_detail,
            progress_enabled,
        })
    }

    pub(super) fn announce_start(
        &self,
        total: usize,
        options: &Options,
        jobs: usize,
        category_counts: &str,
    ) {
        let filters = if options.case_filters.is_empty() {
            "none".to_owned()
        } else {
            options.case_filters.join(", ")
        };
        eprintln!(
            "running {total} test entry(s) ({category_counts}) with output={} timeout={}s progress={} color={} jobs={} recompile-rounds={} case-filter={}",
            options.output.label(),
            options.timeout_seconds,
            match options.progress {
                ProgressMode::Auto => "auto",
                ProgressMode::On => "on",
                ProgressMode::Off => "off",
            },
            match options.color {
                ColorMode::Auto => "auto",
                ColorMode::Always => "always",
                ColorMode::Never => "never",
            },
            jobs,
            options.recompile_rounds,
            filters,
        );
    }

    pub(super) fn update_progress(
        &self,
        completed: usize,
        total: usize,
        active: usize,
        case: &CaseDescriptor,
        event: ProgressEventKind,
    ) -> bool {
        if !self.progress_enabled {
            return false;
        }
        match &self.mode {
            ReporterMode::Interactive(progress) => {
                let message = progress_message(self.palette, completed, total, active, case);
                progress.set_position(completed as u64);
                progress.set_message(message);
                if should_emit_progress_milestone(event, completed, total) {
                    progress.println(sparse_progress_message(
                        self.palette,
                        completed,
                        total,
                        active,
                    ));
                    true
                } else {
                    false
                }
            }
            ReporterMode::Plain => match self.plain_progress_detail {
                PlainProgressDetail::Verbose => {
                    let message = progress_message(self.palette, completed, total, active, case);
                    eprintln!("{message}");
                    true
                }
                PlainProgressDetail::Sparse => {
                    if should_emit_progress_milestone(event, completed, total) {
                        eprintln!(
                            "{}",
                            sparse_progress_message(self.palette, completed, total, active)
                        );
                        true
                    } else {
                        false
                    }
                }
            },
        }
    }

    pub(super) fn emit_heartbeat(&self, completed: usize, total: usize, active: usize) {
        if !self.progress_enabled {
            return;
        }
        let text = heartbeat_progress_message(self.palette, completed, total, active);
        match &self.mode {
            ReporterMode::Interactive(progress) => progress.println(text),
            ReporterMode::Plain => eprintln!("{text}"),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn emit_failure(
        &self,
        counts: ProgressCounts,
        case: &CaseDescriptor,
        outcome: CaseOutcome,
        rendered_failure: Option<&str>,
        failed_proto_tags: &[String],
        timeout_seconds: u64,
        output_mode: FailureOutputMode,
    ) {
        let text = match outcome {
            CaseOutcome::TimedOut => self.render_timeout(counts, case, timeout_seconds),
            CaseOutcome::Failed => self.render_failure(
                counts,
                case,
                rendered_failure.unwrap_or("runner exited with failure but did not report details"),
                failed_proto_tags,
                output_mode,
            ),
            CaseOutcome::Passed => return,
        };

        match &self.mode {
            ReporterMode::Interactive(progress) => progress.println(text),
            ReporterMode::Plain => eprintln!("{text}"),
        }
    }

    pub(super) fn finish(
        &self,
        total: usize,
        failed: usize,
        timed_out: usize,
        failure_counts: &BTreeMap<String, usize>,
        total_protos: usize,
        failed_protos: usize,
    ) {
        if let ReporterMode::Interactive(progress) = &self.mode {
            progress.finish_and_clear();
        }

        let passed = total - failed;
        let passed_protos = total_protos.saturating_sub(failed_protos);
        eprintln!(
            "case runner finished: entries: total={}, passed={}, failed={}, timed_out={}",
            total,
            self.palette.green(passed.to_string()),
            if failed == 0 {
                self.palette.green(failed.to_string())
            } else {
                self.palette.red(failed.to_string())
            },
            if timed_out == 0 {
                self.palette.green(timed_out.to_string())
            } else {
                self.palette.yellow(timed_out.to_string())
            },
        );
        if total_protos > 0 {
            eprintln!(
                "                     protos: total={}, passed={}, failed={}",
                total_protos,
                self.palette.green(passed_protos.to_string()),
                if failed_protos == 0 {
                    self.palette.green(failed_protos.to_string())
                } else {
                    self.palette.red(failed_protos.to_string())
                },
            );
        }

        if failure_counts.is_empty() {
            return;
        }

        eprintln!("failure summary:");
        for (label, count) in sorted_failure_counts(failure_counts) {
            let is_timeout = label == "timed-out";
            let label = if is_timeout {
                self.palette.yellow(label)
            } else {
                self.palette.red(label)
            };
            let count = if is_timeout {
                self.palette.yellow(count.to_string())
            } else {
                self.palette.red(count.to_string())
            };
            eprintln!("  {count}\t{label}");
        }
    }

    pub(super) fn render_timeout(
        &self,
        counts: ProgressCounts,
        case: &CaseDescriptor,
        timeout_seconds: u64,
    ) -> String {
        format!(
            "{} [{}/{}]\tdialect: {}\tcase: {}\t{}",
            self.palette.red("FAIL"),
            counts.completed,
            counts.total,
            self.palette.cyan(&case.dialect),
            case.display_path(),
            self.palette
                .yellow(format!("timed out after {}s", timeout_seconds))
        )
    }

    pub(super) fn render_failure(
        &self,
        counts: ProgressCounts,
        case: &CaseDescriptor,
        raw: &str,
        failed_proto_tags: &[String],
        output_mode: FailureOutputMode,
    ) -> String {
        let normalized = normalize_runner_failure(raw, case, output_mode);
        let tag_suffix = if failed_proto_tags.is_empty() {
            String::new()
        } else {
            format!("\t[{}]", failed_proto_tags.join(", "))
        };
        match output_mode {
            FailureOutputMode::Simple => format!(
                "{} [{}/{}]\tdialect: {}\tcase: {}\t{}{}",
                self.palette.red("FAIL"),
                counts.completed,
                counts.total,
                self.palette.cyan(&case.dialect),
                case.display_path(),
                self.palette.red(&normalized),
                self.palette.yellow(&tag_suffix),
            ),
            FailureOutputMode::Verbose => {
                let mut lines = Vec::new();
                lines.push(format!(
                    "{} [{}/{}]\tdialect: {}\tcase: {}{}",
                    self.palette.red("FAIL"),
                    counts.completed,
                    counts.total,
                    self.palette.cyan(&case.dialect),
                    case.display_path(),
                    self.palette.yellow(&tag_suffix),
                ));
                lines.extend(
                    normalized
                        .lines()
                        .map(|line| format!("  {}", self.color_detail_line(line))),
                );
                lines.join("\n")
            }
        }
    }

    pub(super) fn color_detail_line(&self, line: &str) -> String {
        if line.starts_with("status:") {
            self.palette.yellow(line)
        } else if line.starts_with("stdout:") {
            self.palette.cyan(line)
        } else if line.starts_with("stderr:") {
            self.palette.red(line)
        } else if line.starts_with("source artifact:") || line.starts_with("chunk artifact:") {
            self.palette.cyan(line)
        } else if line.starts_with("generated source:") {
            self.palette.magenta(line)
        } else if line.contains("failed") || line.contains("mismatch") {
            self.palette.red(line)
        } else {
            line.to_owned()
        }
    }
}
