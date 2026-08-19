//! 解析并校验源码中的可读性与结构合同指令；依赖 manifest/StructureFacts，不负责执行 Lua；例如检查生成源码包含、顺序及 loop protocol。

use super::*;

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

        match directive {
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
                });
            }
            "expect-not-contains" => {
                let [needle] = args.as_slice() else {
                    return Err(readability_parse_failure(
                        source_relative,
                        line_no,
                        "expect-not-contains requires exactly one [[...]] argument",
                    ));
                };
                assertions.push(ReadabilityAssertion::NotContains {
                    line: line_no,
                    needle: needle.clone(),
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
        let Some(rest) = raw.strip_prefix("[[") else {
            return Err("arguments must use Lua long-bracket form [[...]]");
        };
        let Some(end) = rest.find("]]") else {
            return Err("missing closing ]] in readability assertion argument");
        };
        args.push(rest[..end].to_owned());
        raw = &rest[end + 2..];
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
    assertions: &[ReadabilityAssertion],
    check_positive_shape: bool,
) -> Result<(), TestFailure> {
    for assertion in assertions {
        match assertion {
            ReadabilityAssertion::Contains { line, needle } if check_positive_shape => {
                if !generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::NotContains { line, needle } => {
                if generated_source.contains(needle) {
                    return Err(readability_assertion_failure(
                        stage_label,
                        *line,
                        format!("expected generated source not to contain {needle:?}"),
                        generated_source,
                    ));
                }
            }
            ReadabilityAssertion::Order {
                line,
                before,
                after,
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
            ReadabilityAssertion::Contains { .. } | ReadabilityAssertion::Order { .. } => {}
        }
    }

    Ok(())
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
    plan_contains_mixed_unstructured_child_loop(facts.plan(), protocol)
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
