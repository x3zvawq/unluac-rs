//! 这个模块承载跨层共享的轻量运行时计时基础设施。
//!
//! 默认构建会保留完整 timing 树收集与渲染，方便仓库内排查性能问题；
//! 当关闭 `timing-report` feature 时，这里退化成只保留公共数据结构和 no-op 收集器，
//! 这样发布用 wasm 就不会再把计时相关实现一起打进去。

use std::time::Duration;

use crate::debug::{DebugColorMode, DebugDetail};

/// 一次 pipeline 运行产出的 timing 树。
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TimingReport {
    pub total: Duration,
    pub nodes: Vec<TimingNode>,
}

/// timing 树上的单个节点。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimingNode {
    pub label: String,
    pub total: Duration,
    pub calls: usize,
    pub children: Vec<TimingNode>,
}

#[cfg(feature = "timing-report")]
mod enabled {
    use std::cell::RefCell;
    use std::collections::BTreeMap;
    use std::fmt::Write;
    use std::time::Instant;

    use crate::debug::colorize_debug_text;

    use super::{DebugColorMode, DebugDetail, Duration, TimingNode, TimingReport};

    /// 把层级 timing 渲染成终端友好的稳定文本。
    pub fn render_timing_report(
        report: &TimingReport,
        detail: DebugDetail,
        color: DebugColorMode,
    ) -> String {
        let mut output = String::new();
        let _ = writeln!(output, "===== Timing =====");
        let _ = writeln!(output, "pipeline total={}", format_duration(report.total));

        if report.nodes.is_empty() {
            let _ = writeln!(output, "no timing spans recorded");
            return colorize_debug_text(&output, color);
        }

        let max_depth = match detail {
            DebugDetail::Summary => 1,
            DebugDetail::Normal | DebugDetail::Verbose => usize::MAX,
        };

        for node in &report.nodes {
            render_node(&mut output, node, 0, max_depth, detail);
        }

        colorize_debug_text(&output, color)
    }

    #[derive(Debug)]
    pub(crate) struct TimingCollector {
        enabled: bool,
        inner: RefCell<TimingCollectorInner>,
    }

    #[derive(Debug, Default)]
    struct TimingCollectorInner {
        stack: Vec<String>,
        entry_order: Vec<TimingFlatEntry>,
        index_by_path: BTreeMap<Vec<String>, usize>,
    }

    #[derive(Debug)]
    struct TimingFlatEntry {
        path: Vec<String>,
        total: Duration,
        calls: usize,
    }

    #[derive(Debug)]
    struct ActiveTimingSpan<'a> {
        collector: &'a TimingCollector,
        start: Option<Instant>,
    }

    #[derive(Debug)]
    struct TimingNodeBuilder {
        label: String,
        total: Duration,
        calls: usize,
        children: Vec<TimingNodeBuilder>,
    }

    impl TimingCollector {
        pub(crate) fn new(enabled: bool) -> Self {
            Self {
                enabled,
                inner: RefCell::new(TimingCollectorInner::default()),
            }
        }

        pub(crate) fn disabled() -> Self {
            Self::new(false)
        }

        pub(crate) fn record<T, F>(&self, label: impl Into<String>, f: F) -> T
        where
            F: FnOnce() -> T,
        {
            if !self.enabled {
                return f();
            }

            let _span = self.enter(label);
            f()
        }

        pub(crate) fn finish(&self) -> Option<TimingReport> {
            if !self.enabled {
                return None;
            }

            let inner = self.inner.borrow();
            let mut roots = Vec::new();
            for entry in &inner.entry_order {
                insert_timing_path(&mut roots, &entry.path, entry.total, entry.calls);
            }

            let nodes = roots
                .into_iter()
                .map(TimingNodeBuilder::build)
                .collect::<Vec<_>>();
            let total = nodes
                .iter()
                .fold(Duration::ZERO, |acc, node| acc + node.total);
            Some(TimingReport { total, nodes })
        }

        fn enter(&self, label: impl Into<String>) -> ActiveTimingSpan<'_> {
            let label = label.into();
            self.inner.borrow_mut().stack.push(label);
            ActiveTimingSpan {
                collector: self,
                start: Some(Instant::now()),
            }
        }
    }

    impl TimingCollectorInner {
        fn record_path(&mut self, path: Vec<String>, elapsed: Duration) {
            if let Some(index) = self.index_by_path.get(&path).copied() {
                let entry = &mut self.entry_order[index];
                entry.total += elapsed;
                entry.calls += 1;
                return;
            }

            let index = self.entry_order.len();
            self.index_by_path.insert(path.clone(), index);
            self.entry_order.push(TimingFlatEntry {
                path,
                total: elapsed,
                calls: 1,
            });
        }
    }

    impl Drop for ActiveTimingSpan<'_> {
        fn drop(&mut self) {
            let Some(start) = self.start.take() else {
                return;
            };

            let elapsed = start.elapsed();
            let mut inner = self.collector.inner.borrow_mut();
            let path = inner.stack.clone();
            let popped = inner.stack.pop();
            debug_assert!(popped.is_some(), "timing stack must stay balanced");
            inner.record_path(path, elapsed);
        }
    }

    impl TimingNodeBuilder {
        fn new(label: String) -> Self {
            Self {
                label,
                total: Duration::ZERO,
                calls: 0,
                children: Vec::new(),
            }
        }

        fn build(self) -> TimingNode {
            TimingNode {
                label: self.label,
                total: self.total,
                calls: self.calls,
                children: self
                    .children
                    .into_iter()
                    .map(TimingNodeBuilder::build)
                    .collect(),
            }
        }
    }

    fn insert_timing_path(
        nodes: &mut Vec<TimingNodeBuilder>,
        path: &[String],
        total: Duration,
        calls: usize,
    ) {
        let Some(label) = path.first() else {
            return;
        };

        let index = nodes
            .iter()
            .position(|node| node.label == *label)
            .unwrap_or_else(|| {
                nodes.push(TimingNodeBuilder::new(label.clone()));
                nodes.len() - 1
            });

        if path.len() == 1 {
            let node = &mut nodes[index];
            node.total += total;
            node.calls += calls;
            return;
        }

        insert_timing_path(&mut nodes[index].children, &path[1..], total, calls);
    }

    fn render_node(
        output: &mut String,
        node: &TimingNode,
        depth: usize,
        max_depth: usize,
        detail: DebugDetail,
    ) {
        if depth >= max_depth {
            return;
        }

        let indent = "  ".repeat(depth);
        let _ = write!(
            output,
            "{indent}{} total={} calls={}",
            node.label,
            format_duration(node.total),
            node.calls
        );
        if detail == DebugDetail::Verbose {
            let average = if node.calls == 0 {
                Duration::ZERO
            } else {
                node.total.div_f64(node.calls as f64)
            };
            let _ = write!(output, " avg={}", format_duration(average));
        }
        let _ = writeln!(output);

        for child in &node.children {
            render_node(output, child, depth + 1, max_depth, detail);
        }
    }

    fn format_duration(duration: Duration) -> String {
        let seconds = duration.as_secs_f64();
        if seconds >= 1.0 {
            return format!("{seconds:.2}s");
        }

        let millis = duration.as_secs_f64() * 1_000.0;
        if millis >= 1.0 {
            return format!("{millis:.2}ms");
        }

        let micros = duration.as_secs_f64() * 1_000_000.0;
        if micros >= 1.0 {
            return format!("{micros:.2}us");
        }

        format!("{}ns", duration.as_nanos())
    }

    pub(crate) use TimingCollector as Collector;
}

#[cfg(not(feature = "timing-report"))]
mod enabled {
    use super::{DebugColorMode, DebugDetail, TimingReport};

    pub fn render_timing_report(
        _report: &TimingReport,
        _detail: DebugDetail,
        _color: DebugColorMode,
    ) -> String {
        "timing support is unavailable in this build".to_owned()
    }

    #[derive(Debug, Default)]
    pub(crate) struct TimingCollector;

    impl TimingCollector {
        pub(crate) fn new(_enabled: bool) -> Self {
            Self
        }

        pub(crate) fn disabled() -> Self {
            Self
        }

        pub(crate) fn record<T, F>(&self, _label: impl Into<String>, f: F) -> T
        where
            F: FnOnce() -> T,
        {
            f()
        }

        pub(crate) fn finish(&self) -> Option<TimingReport> {
            None
        }
    }

    pub(crate) use TimingCollector as Collector;
}

pub(crate) use enabled::Collector as TimingCollector;
pub use enabled::render_timing_report;
