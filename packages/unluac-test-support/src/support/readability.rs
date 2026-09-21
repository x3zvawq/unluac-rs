//! 解析并校验源码中的可读性与结构合同指令；依赖 manifest/StructureFacts，不负责执行 Lua；例如检查生成源码包含、顺序及 loop protocol。

use std::collections::BTreeMap;

use unluac::ast::AstModule;

use super::*;

#[path = "readability/ast_metrics.rs"]
mod ast_metrics;

use ast_metrics::AstMetricSummary;

pub(super) fn read_readability_assertions(
    source_relative: &str,
) -> Result<Vec<ReadabilityAssertion>, TestFailure> {
    let source = repo_root().join(source_relative);
    let text = fs::read_to_string(&source).map_err(|error| {
        TestFailure::new(
            FailureKind::ReadabilityAssertionFailed,
            "read readability assertions failed",
            format!(
                "read readability assertions from {} failed: {error}",
                repo_relative_display(&source)
            ),
        )
    })?;

    let mut assertions = Vec::new();
    for (line_index, line) in text.lines().enumerate() {
        let line_no = line_index + 1;
        let Some(raw) = line
            .trim_start()
            .strip_prefix("--")
            .map(str::trim_start)
            .and_then(|line| line.strip_prefix("unluac:"))
            .map(str::trim)
        else {
            continue;
        };

        let (directive, args) = split_directive(raw).ok_or_else(|| {
            readability_parse_failure(source_relative, line_no, "missing readability directive")
        })?;
        let args = parse_long_bracket_args(args)
            .map_err(|error| readability_parse_failure(source_relative, line_no, error))?;
        let required_data_args = match directive {
            "expect-contains"
            | "expect-not-contains"
            | "expect-not-line"
            | "expect-max-line-length" => 1,
            "expect-order"
            | "expect-count"
            | "expect-min-count"
            | "expect-max-count"
            | "expect-ast-count"
            | "expect-ast-min"
            | "expect-ast-max"
            | "expect-name"
            | "expect-instruction-count" => 2,
            other => {
                return Err(readability_parse_failure(
                    source_relative,
                    line_no,
                    format!("unknown readability directive: {other}"),
                ));
            }
        };
        let (args, selector) = split_assertion_args(args, required_data_args)
            .map_err(|error| readability_parse_failure(source_relative, line_no, error))?;
        if selector.proto.is_some()
            && !directive.starts_with("expect-ast-")
            && directive != "expect-name"
        {
            return Err(readability_parse_failure(
                source_relative,
                line_no,
                format!(
                    "{directive} cannot use @proto; proto scopes require expect-ast-* or expect-name"
                ),
            ));
        }

        match directive {
            "expect-instruction-count" => {
                let operation = match args[0].as_str() {
                    "not" => InstructionOperation::Not,
                    "call" => InstructionOperation::Call,
                    _ => {
                        return Err(readability_parse_failure(
                            source_relative,
                            line_no,
                            "expect-instruction-count supports not and call operations",
                        ));
                    }
                };
                let expected = args[1].parse::<usize>().map_err(|_| {
                    readability_parse_failure(
                        source_relative,
                        line_no,
                        "instruction count must be a non-negative integer",
                    )
                })?;
                assertions.push(ReadabilityAssertion::InstructionCount {
                    line: line_no,
                    operation,
                    expected,
                    selector,
                });
            }
            "expect-name" => {
                let binding = parse_naming_binding(&args[0])
                    .map_err(|error| readability_parse_failure(source_relative, line_no, error))?;
                assertions.push(ReadabilityAssertion::Name {
                    line: line_no,
                    binding,
                    expected: args[1].clone(),
                    selector,
                });
            }
            "expect-contains" => {
                let [needle] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-contains requires exactly one [[...]] argument",
                    ));
                };
                assertions.push(ReadabilityAssertion::Contains {
                    line: line_no,
                    needle: needle.clone(),
                    selector,
                });
            }
            "expect-not-contains" | "expect-not-line" => {
                let [needle] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        format!("{directive} requires exactly one [[...]] argument"),
                    ));
                };
                assertions.push(if directive == "expect-not-line" {
                    ReadabilityAssertion::NotLine {
                        line: line_no,
                        needle: needle.clone(),
                        selector,
                    }
                } else {
                    ReadabilityAssertion::NotContains {
                        line: line_no,
                        needle: needle.clone(),
                        selector,
                    }
                });
            }
            "expect-order" => {
                let [before, after] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-order requires exactly two [[...]] arguments",
                    ));
                };
                assertions.push(ReadabilityAssertion::Order {
                    line: line_no,
                    before: before.clone(),
                    after: after.clone(),
                    selector,
                });
            }
            "expect-max-line-length" => {
                let [max] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-max-line-length requires exactly one [[...]] argument",
                    ));
                };
                let max = max.parse::<usize>().map_err(|_| {
                    readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-max-line-length requires a non-negative integer",
                    )
                })?;
                assertions.push(ReadabilityAssertion::MaxLineLength {
                    line: line_no,
                    max,
                    selector,
                });
            }
            "expect-count" | "expect-min-count" | "expect-max-count" => {
                let [needle, expected] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        format!("{directive} requires [[needle]] and [[count]] arguments"),
                    ));
                };
                if needle.is_empty() {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        format!("{directive} requires a non-empty needle"),
                    ));
                }
                let bound = parse_count_bound(source_relative, line_no, directive, expected)?;
                assertions.push(ReadabilityAssertion::SourceCount {
                    line: line_no,
                    needle: needle.clone(),
                    bound,
                    selector,
                });
            }
            "expect-ast-count" | "expect-ast-min" | "expect-ast-max" => {
                let [metric, expected] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        format!("{directive} requires [[metric]] and [[count]] arguments"),
                    ));
                };
                let metric = parse_ast_metric(source_relative, line_no, metric)?;
                let bound = parse_count_bound(source_relative, line_no, directive, expected)?;
                assertions.push(ReadabilityAssertion::AstCount {
                    line: line_no,
                    metric,
                    bound,
                    selector,
                });
            }
            other => {
                return Err(readability_parse_failure(
                    source_relative,
                    line_no,
                    format!("unknown readability directive: {other}"),
                ));
            }
        }
    }

    Ok(assertions)
}

/// `--list` 只在启动整批测试前执行一次该校验；按路径分组可避免同一源码在方言/variant
/// 矩阵中重复读盘。普通 child runner 仍只读取自己正在执行的单个 case。
pub(super) fn readability_summaries(
    entries: &[LuaCaseManifestEntry],
) -> Result<BTreeMap<&'static str, CaseReadabilitySummary>, String> {
    let mut entries_by_path: BTreeMap<&'static str, Vec<&LuaCaseManifestEntry>> = BTreeMap::new();
    for entry in entries {
        entries_by_path.entry(entry.path).or_default().push(entry);
    }

    let mut summaries = BTreeMap::new();
    for (path, entries) in entries_by_path {
        let assertions =
            read_readability_assertions(path).map_err(|failure| failure.detail().to_owned())?;
        summaries.insert(
            path,
            CaseReadabilitySummary {
                total: assertions.len(),
                ast: assertions
                    .iter()
                    .filter(|assertion| matches!(assertion, ReadabilityAssertion::AstCount { .. }))
                    .count(),
            },
        );
        for assertion in &assertions {
            let selector = assertion_selector(assertion);
            if !selector.is_configured() {
                continue;
            }
            if entries
                .iter()
                .any(|entry| selector_matches_entry(selector, entry))
            {
                continue;
            }
            return Err(format!(
                "readability selector matched no manifest entry at {}:{} ({})",
                path,
                assertion_line(assertion),
                selector.describe(),
            ));
        }
    }

    Ok(summaries)
}

fn split_assertion_args(
    args: Vec<String>,
    data_count: usize,
) -> Result<(Vec<String>, ReadabilitySelector), String> {
    if args.len() < data_count {
        return Err(format!(
            "directive requires {data_count} [[...]] argument(s) before selectors"
        ));
    }
    let mut selector = ReadabilitySelector::default();

    for argument in &args[data_count..] {
        let Some(raw_selector) = argument.strip_prefix('@') else {
            return Err("selector arguments must follow all directive arguments".to_owned());
        };
        let Some((key, value)) = raw_selector.split_once('=') else {
            return Err(format!("selector {argument:?} must use @key=value"));
        };
        if value.is_empty() {
            return Err(format!("selector {argument:?} has an empty value"));
        }
        match key {
            "naming-mode" => {
                if selector.naming_mode.is_some() {
                    return Err("selector @naming-mode may appear at most once".to_owned());
                }
                selector.naming_mode = Some(
                    value
                        .parse()
                        .map_err(|_| format!("unknown @naming-mode value {value:?}"))?,
                );
            }
            "dialect" => {
                if selector.dialect.is_some() {
                    return Err("selector @dialect may appear at most once".to_owned());
                }
                selector.dialect = Some(parse_selector_dialect(value)?);
            }
            "debug" => {
                if selector.debug.is_some() {
                    return Err("selector @debug may appear at most once".to_owned());
                }
                selector.debug = Some(match value {
                    "retained" => ReadabilityDebugSelector::Retained,
                    "stripped" => ReadabilityDebugSelector::Stripped,
                    "ignored" => ReadabilityDebugSelector::Ignored,
                    _ => {
                        return Err(format!(
                            "selector @debug must be retained, stripped, or ignored, got {value:?}"
                        ));
                    }
                });
            }
            "variant" => {
                if selector.variant.is_some() {
                    return Err("selector @variant may appear at most once".to_owned());
                }
                selector.variant = Some(value.to_owned());
            }
            "proto" => {
                if selector.proto.is_some() {
                    return Err("selector @proto may appear at most once".to_owned());
                }
                selector.proto = Some(value.parse::<usize>().map_err(|_| {
                    format!("selector @proto requires a non-negative integer, got {value:?}")
                })?);
            }
            _ => return Err(format!("unknown readability selector @{key}")),
        }
    }

    Ok((args[..data_count].to_vec(), selector))
}

fn parse_selector_dialect(value: &str) -> Result<LuaCaseDialect, String> {
    match value {
        "lua5.1" => Ok(LuaCaseDialect::Lua51),
        "lua5.2" => Ok(LuaCaseDialect::Lua52),
        "lua5.3" => Ok(LuaCaseDialect::Lua53),
        "lua5.4" => Ok(LuaCaseDialect::Lua54),
        "lua5.5" => Ok(LuaCaseDialect::Lua55),
        "luajit" => Ok(LuaCaseDialect::Luajit),
        "luau" => Ok(LuaCaseDialect::Luau),
        _ => Err(format!("unknown @dialect value {value:?}")),
    }
}

fn parse_naming_binding(value: &str) -> Result<NamingBindingSelector, String> {
    let (kind, index) = value
        .split_once(':')
        .ok_or_else(|| "expect-name requires param:N, local:N, or upvalue:N".to_owned())?;
    let index = index
        .parse::<usize>()
        .map_err(|_| "expect-name requires a non-negative binding index".to_owned())?;
    match kind {
        "param" => Ok(NamingBindingSelector::Param(index)),
        "local" => Ok(NamingBindingSelector::Local(index)),
        "upvalue" => Ok(NamingBindingSelector::Upvalue(index)),
        _ => Err(format!("unknown naming binding kind {kind:?}")),
    }
}

fn parse_count_bound(
    source_relative: &str,
    line: usize,
    directive: &str,
    value: &str,
) -> Result<ReadabilityCountBound, TestFailure> {
    let count = value.parse::<usize>().map_err(|_| {
        readability_parse_failure(
            source_relative,
            line,
            format!("{directive} requires a non-negative integer count"),
        )
    })?;
    match directive {
        "expect-count" | "expect-ast-count" => Ok(ReadabilityCountBound::Exact(count)),
        "expect-min-count" | "expect-ast-min" => Ok(ReadabilityCountBound::Min(count)),
        "expect-max-count" | "expect-ast-max" => Ok(ReadabilityCountBound::Max(count)),
        _ => Err(readability_parse_failure(
            source_relative,
            line,
            format!("unsupported count directive: {directive}"),
        )),
    }
}

fn parse_ast_metric(
    source_relative: &str,
    line: usize,
    value: &str,
) -> Result<ReadabilityAstMetric, TestFailure> {
    let metric = match value {
        "empty-local" => ReadabilityAstMetric::EmptyLocal,
        "empty-function" => ReadabilityAstMetric::EmptyFunction,
        "if" => ReadabilityAstMetric::If,
        "while" => ReadabilityAstMetric::While,
        "repeat" => ReadabilityAstMetric::Repeat,
        "numeric-for" => ReadabilityAstMetric::NumericFor,
        "generic-for" => ReadabilityAstMetric::GenericFor,
        "goto" => ReadabilityAstMetric::Goto,
        "label" => ReadabilityAstMetric::Label,
        "break" => ReadabilityAstMetric::Break,
        "continue" => ReadabilityAstMetric::Continue,
        "do-block" => ReadabilityAstMetric::DoBlock,
        "function" => ReadabilityAstMetric::Function,
        "local-function" => ReadabilityAstMetric::LocalFunction,
        "local-decl" => ReadabilityAstMetric::LocalDecl,
        "local-binding" => ReadabilityAstMetric::LocalBinding,
        "assign" => ReadabilityAstMetric::Assign,
        "call" => ReadabilityAstMetric::Call,
        "method-call" => ReadabilityAstMetric::MethodCall,
        "error" => ReadabilityAstMetric::Error,
        "close-binding" => ReadabilityAstMetric::CloseBinding,
        "global-decl" => ReadabilityAstMetric::GlobalDecl,
        "named-vararg-function" => ReadabilityAstMetric::NamedVarargFunction,
        "table-constructor" => ReadabilityAstMetric::TableConstructor,
        "table-list-field" => ReadabilityAstMetric::TableListField,
        "table-record-field" => ReadabilityAstMetric::TableRecordField,
        "repeat-condition-local" => ReadabilityAstMetric::RepeatConditionLocal,
        _ => {
            return Err(readability_parse_failure(
                source_relative,
                line,
                format!("unknown AST readability metric: {value}"),
            ));
        }
    };
    Ok(metric)
}

pub(super) fn split_directive(raw: &str) -> Option<(&str, &str)> {
    let raw = raw.trim();
    if raw.is_empty() {
        return None;
    }
    match raw.find(char::is_whitespace) {
        Some(index) => Some((&raw[..index], raw[index..].trim_start())),
        None => Some((raw, "")),
    }
}

pub(super) fn parse_long_bracket_args(mut raw: &str) -> Result<Vec<String>, &'static str> {
    let mut args = Vec::new();
    loop {
        raw = raw.trim_start();
        if raw.is_empty() {
            return Ok(args);
        }
        let Some(after_open) = raw.strip_prefix('[') else {
            return Err("arguments must use Lua long-bracket form [[...]] or [=[...]=]");
        };
        let level = after_open.bytes().take_while(|&ch| ch == b'=').count();
        let Some(rest) = after_open[level..].strip_prefix('[') else {
            return Err("invalid opening delimiter in readability assertion argument");
        };
        // 与 Lua 的长括号定界相同，允许模式本身包含 ]] 或以 ] 结尾。
        let closing = format!("]{}]", &after_open[..level]);
        let Some(end) = rest.find(&closing) else {
            return Err(
                "missing matching long-bracket closing delimiter in readability assertion argument",
            );
        };
        args.push(rest[..end].to_owned());
        raw = &rest[end + closing.len()..];
    }
}

pub(super) fn readability_parse_failure(
    source_relative: &str,
    line: usize,
    reason: impl Into<String>,
) -> TestFailure {
    let reason = reason.into();
    TestFailure::new(
        FailureKind::ReadabilityAssertionFailed,
        format!("readability assertion parse failed at {source_relative}:{line}: {reason}"),
        format!("readability assertion parse failed at {source_relative}:{line}: {reason}"),
    )
}

pub(super) fn assert_readability(
    stage_label: &str,
    generated_source: &str,
    readability: Option<&AstModule>,
    naming: Option<&unluac::ast::NameMap>,
    entry: &LuaCaseManifestEntry,
    assertions: &[ReadabilityAssertion],
    check_positive_shape: bool,
) -> Result<(), TestFailure> {
    let mut source_counts = BTreeMap::new();
    let ast_metrics = if check_positive_shape
        && assertions.iter().any(|assertion| {
            matches!(
                assertion,
                ReadabilityAssertion::AstCount { .. } | ReadabilityAssertion::Name { .. }
            ) && assertion_selector_matches(assertion, entry)
        }) {
        let module = readability.ok_or_else(|| {
            readability_assertion_failure(
                stage_label,
                0,
                "expected final readability AST for AST/name assertion".to_owned(),
                generated_source,
            )
        })?;
        Some(AstMetricSummary::collect(module))
    } else {
        None
    };

    for assertion in assertions {
        if !assertion_selector_matches(assertion, entry) {
            continue;
        }
        match assertion {
            ReadabilityAssertion::Name {
                line,
                binding,
                expected,
                selector,
            } if check_positive_shape => {
                let proto = selector
                    .proto
                    .unwrap_or_else(|| naming.map_or(0, |names| names.entry_function.index()));
                let actual = ast_metrics
                    .as_ref()
                    .filter(|metrics| metrics.count(Some(proto)).is_some())
                    .and(naming)
                    .and_then(|names| names.functions.get(proto))
                    .and_then(|names| match binding {
                        NamingBindingSelector::Param(index) => names.params.get(*index),
                        NamingBindingSelector::Local(index) => match ast_metrics
                            .as_ref()?
                            .local_binding(proto, *index)?
                        {
                            unluac::ast::AstBindingRef::Local(id) => names.locals.get(id.index()),
                            unluac::ast::AstBindingRef::SyntheticLocal(id) => {
                                names.synthetic_locals.get(&id)
                            }
                            unluac::ast::AstBindingRef::Temp(_) => None,
                        },
                        NamingBindingSelector::Upvalue(index) => names.upvalues.get(*index),
                    });
                if actual.is_none_or(|name| name.text != *expected) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!(
                            "expected name {binding:?} in proto#{proto} to be {expected:?}; actual {:?}",
                            actual.map(|name| &name.text)
                        ),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::Contains { line, needle, .. } if check_positive_shape => {
                if !generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::NotContains { line, needle, .. } => {
                if generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source not to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::NotLine { line, needle, .. } => {
                if generated_source
                    .lines()
                    .any(|source_line| source_line.trim() == needle.trim())
                {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source not to have a complete line {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::Order {
                line,
                before,
                after,
                ..
            } if check_positive_shape => {
                let before_pos = generated_source.find(before);
                let after_pos = generated_source.find(after);
                if !matches!((before_pos, after_pos), (Some(left), Some(right)) if left < right) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source to contain {before:?} before {after:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::MaxLineLength { line, max, .. } => {
                if let Some((physical_line, width, source_line)) = generated_source
                    .lines()
                    .enumerate()
                    .map(|(index, source_line)| {
                        (index + 1, source_line.chars().count(), source_line)
                    })
                    .find(|(_, width, _)| width > max)
                {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!(
                            "expected generated source lines to be at most {max} characters; physical line {physical_line} has {width}: {source_line:?}"
                        ),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::SourceCount {
                line,
                needle,
                bound,
                ..
            } if count_bound_runs(*bound, check_positive_shape) => {
                let actual = *source_counts
                    .entry(needle.as_str())
                    .or_insert_with(|| count_non_overlapping(generated_source, needle));
                if !count_bound_matches(*bound, actual) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!(
                            "expected {needle:?} to appear {}; actual count is {actual}",
                            count_bound_description(*bound)
                        ),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::AstCount {
                line,
                metric,
                bound,
                selector,
            } if check_positive_shape => {
                let Some(metrics) = ast_metrics.as_ref() else {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        "AST metrics were not collected for matching expect-ast-* assertion"
                            .to_owned(),
                        generated_source,
                    ));
                };
                let Some(counts) = metrics.count(selector.proto) else {
                    let proto = selector.proto.unwrap_or_default();
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!(
                            "expected proto#{proto} for AST readability assertion, but it is absent from final AST"
                        ),
                        generated_source,
                    ));
                };
                let actual = counts[metric.index()];
                if !count_bound_matches(*bound, actual) {
                    let scope = match selector.proto {
                        Some(proto) => format!("proto#{proto}"),
                        None => "full module".to_owned(),
                    };
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!(
                            "expected AST metric {} in {scope} to appear {}; actual count is {actual}",
                            metric.label(),
                            count_bound_description(*bound)
                        ),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::InstructionCount { .. }
            | ReadabilityAssertion::Name { .. }
            | ReadabilityAssertion::Contains { .. }
            | ReadabilityAssertion::Order { .. }
            | ReadabilityAssertion::SourceCount { .. }
            | ReadabilityAssertion::AstCount { .. } => {}
        }
    }

    Ok(())
}

pub(super) fn assert_instruction_contracts(
    stage: &str,
    lowered: &LoweredChunk,
    entry: &LuaCaseManifestEntry,
    assertions: &[ReadabilityAssertion],
) -> Result<(), TestFailure> {
    let expected = assertions
        .iter()
        .filter_map(|assertion| {
            if let ReadabilityAssertion::InstructionCount {
                line,
                operation,
                expected,
                ..
            } = assertion
                && assertion_selector_matches(assertion, entry)
            {
                Some((*line, operation, *expected))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    if expected.is_empty() {
        return Ok(());
    }
    let mut counts = [0usize; 2];
    let mut pending = vec![&lowered.main];
    while let Some(proto) = pending.pop() {
        for instr in &proto.instrs {
            match instr {
                LowInstr::UnaryOp(unary) if unary.op == unluac::transformer::UnaryOpKind::Not => {
                    counts[0] += 1
                }
                LowInstr::Call(_) => counts[1] += 1,
                _ => {}
            }
        }
        pending.extend(proto.children.iter().map(AsRef::as_ref));
    }
    for (line, operation, expected) in expected {
        let (count, name) = match operation {
            InstructionOperation::Not => (counts[0], "NOT"),
            InstructionOperation::Call => (counts[1], "CALL"),
        };
        if count != expected {
            let summary = format!(
                "[{stage}] instruction assertion failed at source line {line}: expected {expected} {name} operations, got {count}"
            );
            return Err(TestFailure::new(
                FailureKind::ReadabilityAssertionFailed,
                summary.clone(),
                format!("{}: {summary}", entry.path),
            ));
        }
    }
    Ok(())
}

pub(super) fn assert_compiled_instruction_contracts(
    stage: &str,
    path: &Path,
    entry: &LuaCaseManifestEntry,
    assertions: &[ReadabilityAssertion],
) -> Result<(), TestFailure> {
    if !assertions.iter().any(|assertion| {
        matches!(assertion, ReadabilityAssertion::InstructionCount { .. })
            && assertion_selector_matches(assertion, entry)
    }) {
        return Ok(());
    }
    // 仅显式要求这项合同的实例额外执行 Parse/Transformer；不重复 HIR 与 Generate。
    let mut options = decompile_options(entry);
    options.target_stage = DecompileStage::Transformer;
    let bytes = fs::read(path).map_err(|error| {
        TestFailure::new(
            FailureKind::ReadabilityAssertionFailed,
            format!("[{stage}] read instruction artifact failed"),
            error.to_string(),
        )
    })?;
    let result = decompile(&bytes, options).map_err(|error| {
        TestFailure::new(
            FailureKind::ReadabilityAssertionFailed,
            format!("[{stage}] lower instruction artifact failed"),
            error.to_string(),
        )
    })?;
    let lowered = result
        .state
        .lowered
        .as_ref()
        .expect("Transformer stage publishes LoweredChunk");
    assert_instruction_contracts(stage, lowered, entry, assertions)
}

fn assertion_selector_matches(
    assertion: &ReadabilityAssertion,
    entry: &LuaCaseManifestEntry,
) -> bool {
    selector_matches_entry(assertion_selector(assertion), entry)
}

fn assertion_selector(assertion: &ReadabilityAssertion) -> &ReadabilitySelector {
    match assertion {
        ReadabilityAssertion::InstructionCount { selector, .. }
        | ReadabilityAssertion::Name { selector, .. }
        | ReadabilityAssertion::Contains { selector, .. }
        | ReadabilityAssertion::NotContains { selector, .. }
        | ReadabilityAssertion::NotLine { selector, .. }
        | ReadabilityAssertion::Order { selector, .. }
        | ReadabilityAssertion::MaxLineLength { selector, .. }
        | ReadabilityAssertion::SourceCount { selector, .. }
        | ReadabilityAssertion::AstCount { selector, .. } => selector,
    }
}

fn assertion_line(assertion: &ReadabilityAssertion) -> usize {
    match assertion {
        ReadabilityAssertion::InstructionCount { line, .. }
        | ReadabilityAssertion::Name { line, .. }
        | ReadabilityAssertion::Contains { line, .. }
        | ReadabilityAssertion::NotContains { line, .. }
        | ReadabilityAssertion::NotLine { line, .. }
        | ReadabilityAssertion::Order { line, .. }
        | ReadabilityAssertion::MaxLineLength { line, .. }
        | ReadabilityAssertion::SourceCount { line, .. }
        | ReadabilityAssertion::AstCount { line, .. } => *line,
    }
}

fn selector_matches_entry(selector: &ReadabilitySelector, entry: &LuaCaseManifestEntry) -> bool {
    selector.naming_mode.is_none_or(|mode| {
        mode == entry
            .options
            .naming_mode
            .unwrap_or_else(|| DecompileOptions::default().naming.mode)
    }) && selector
        .dialect
        .is_none_or(|dialect| dialect == entry.dialect)
        && selector
            .debug
            .is_none_or(|expected| expected == debug_selector_for_entry(entry))
        && selector.variant.as_ref().is_none_or(|expected| {
            if expected == "default" {
                entry.variant.is_none()
            } else {
                entry
                    .variant
                    .is_some_and(|variant| variant.label() == expected)
            }
        })
}

fn debug_selector_for_entry(entry: &LuaCaseManifestEntry) -> ReadabilityDebugSelector {
    if entry.options.ignore_debug {
        ReadabilityDebugSelector::Ignored
    } else if entry.options.retain_debug {
        ReadabilityDebugSelector::Retained
    } else {
        ReadabilityDebugSelector::Stripped
    }
}

impl ReadabilitySelector {
    fn is_configured(&self) -> bool {
        self.naming_mode.is_some()
            || self.dialect.is_some()
            || self.debug.is_some()
            || self.variant.is_some()
            || self.proto.is_some()
    }

    fn describe(&self) -> String {
        let mut terms = Vec::new();
        if let Some(mode) = self.naming_mode {
            terms.push(format!("@naming-mode={mode}"));
        }
        if let Some(dialect) = self.dialect {
            terms.push(format!("@dialect={}", <&'static str>::from(dialect)));
        }
        if let Some(debug) = self.debug {
            terms.push(format!("@debug={}", debug.label()));
        }
        if let Some(variant) = &self.variant {
            terms.push(format!("@variant={variant}"));
        }
        if let Some(proto) = self.proto {
            terms.push(format!("@proto={proto}"));
        }
        terms.join(" ")
    }
}

impl ReadabilityDebugSelector {
    const fn label(self) -> &'static str {
        match self {
            Self::Retained => "retained",
            Self::Stripped => "stripped",
            Self::Ignored => "ignored",
        }
    }
}

fn count_non_overlapping(source: &str, needle: &str) -> usize {
    if needle.is_empty() {
        return 0;
    }
    source.match_indices(needle).count()
}

fn count_bound_runs(bound: ReadabilityCountBound, check_positive_shape: bool) -> bool {
    check_positive_shape || matches!(bound, ReadabilityCountBound::Max(_))
}

fn count_bound_matches(bound: ReadabilityCountBound, actual: usize) -> bool {
    match bound {
        ReadabilityCountBound::Exact(expected) => actual == expected,
        ReadabilityCountBound::Min(minimum) => actual >= minimum,
        ReadabilityCountBound::Max(maximum) => actual <= maximum,
    }
}

fn count_bound_description(bound: ReadabilityCountBound) -> String {
    match bound {
        ReadabilityCountBound::Exact(expected) => format!("exactly {expected} time(s)"),
        ReadabilityCountBound::Min(minimum) => format!("at least {minimum} time(s)"),
        ReadabilityCountBound::Max(maximum) => format!("at most {maximum} time(s)"),
    }
}

pub(super) fn assert_source_chunk(
    stage_label: &str,
    kind: GeneratedChunkKind,
    case_path: &str,
) -> Result<(), TestFailure> {
    if kind == GeneratedChunkKind::Source {
        return Ok(());
    }
    let summary = format!("[{stage_label}] generated diagnostic pseudocode in strict source test");
    Err(TestFailure::new(
        FailureKind::GeneratedChunkKindMismatch,
        summary.clone(),
        format!("{summary}: case={case_path}, kind={kind:?}"),
    ))
}

pub(super) fn assert_structure_contracts(
    entry: &LuaCaseManifestEntry,
    facts: Option<&StructureFacts>,
) -> Result<(), TestFailure> {
    for contract in entry
        .structure_contracts
        .iter()
        .copied()
        .filter(|contract| contract.dialect() == entry.dialect)
    {
        let facts = facts.ok_or_else(|| {
            source_structure_contract_failure(entry, "generate stage returned no StructureFacts")
        })?;
        if !structure_facts_match_contract(facts, contract) {
            let LuaCaseStructureContract::MixedUnstructuredChildLoop { protocol, .. } = contract;
            return Err(source_structure_contract_failure(
                entry,
                format!(
                    "no Unstructured layout contained both a direct block and a region child whose subtree owns a {} LoopVmProtocol",
                    loop_protocol_label(protocol)
                ),
            ));
        }
    }
    Ok(())
}

pub(super) fn structure_facts_match_contract(
    facts: &StructureFacts,
    contract: LuaCaseStructureContract,
) -> bool {
    let LuaCaseStructureContract::MixedUnstructuredChildLoop { protocol, .. } = contract;
    facts
        .ready()
        .is_some_and(|ready| plan_contains_mixed_unstructured_child_loop(ready.plan(), protocol))
        || facts
            .children
            .iter()
            .any(|child| structure_facts_match_contract(child, contract))
}

pub(super) fn plan_contains_mixed_unstructured_child_loop(
    plan: &StructurePlan,
    protocol: LuaCaseLoopProtocol,
) -> bool {
    plan.regions().any(|(_, region)| {
        let RegionPlan::Unstructured { layout, .. } = region else {
            return false;
        };
        layout
            .iter()
            .any(|item| matches!(item, UnstructuredLayoutItem::Block(_)))
            && layout.iter().any(|item| match item {
                UnstructuredLayoutItem::Block(_) => false,
                UnstructuredLayoutItem::Region(child) => {
                    region_subtree_contains_loop_protocol(plan, *child, protocol)
                }
            })
    })
}

pub(super) fn region_subtree_contains_loop_protocol(
    plan: &StructurePlan,
    subtree_root: RegionId,
    protocol: LuaCaseLoopProtocol,
) -> bool {
    plan.loops().any(|(loop_id, _)| {
        loop_protocol_matches(plan.loop_protocol(loop_id), protocol)
            && plan
                .loop_region(loop_id)
                .is_some_and(|region| region_is_in_subtree(plan, subtree_root, region))
    })
}

pub(super) fn region_is_in_subtree(
    plan: &StructurePlan,
    subtree_root: RegionId,
    mut region: RegionId,
) -> bool {
    for _ in 0..plan.regions().len() {
        if region == subtree_root {
            return true;
        }
        let Some(parent) = plan.region(region).and_then(RegionPlan::parent) else {
            return false;
        };
        region = parent;
    }
    false
}

pub(super) fn loop_protocol_matches(
    actual: Option<&LoopVmProtocol>,
    expected: LuaCaseLoopProtocol,
) -> bool {
    matches!(
        (actual, expected),
        (
            Some(LoopVmProtocol::NumericFor(_)),
            LuaCaseLoopProtocol::NumericFor
        ) | (
            Some(LoopVmProtocol::GenericFor(_)),
            LuaCaseLoopProtocol::GenericFor
        )
    )
}

pub(super) fn loop_protocol_label(protocol: LuaCaseLoopProtocol) -> &'static str {
    match protocol {
        LuaCaseLoopProtocol::NumericFor => "NumericFor",
        LuaCaseLoopProtocol::GenericFor => "GenericFor",
    }
}

pub(super) fn source_structure_contract_failure(
    entry: &LuaCaseManifestEntry,
    reason: impl Into<String>,
) -> TestFailure {
    let dialect = <&'static str>::from(entry.dialect);
    let reason = reason.into();
    TestFailure::new(
        FailureKind::StructureContractAssertionFailed,
        "StructurePlan source contract failed",
        format!(
            "StructurePlan source contract failed: case={}, dialect={dialect}: {reason}",
            entry.path
        ),
    )
}

pub(super) fn readability_assertion_failure(
    stage_label: &str,
    line: usize,
    reason: String,
    generated_source: &str,
) -> TestFailure {
    let summary =
        format!("[{stage_label}] readability assertion failed at source line {line}: {reason}");
    TestFailure::new(
        FailureKind::ReadabilityAssertionFailed,
        summary.clone(),
        format!("{summary}\ngenerated source:\n{generated_source}"),
    )
}
