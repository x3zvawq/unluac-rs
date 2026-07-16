//! 这个文件承载 Structure 层的共享调试输出。
//!
//! 对外只有一个 Structure dump；内部仍按 CFG、GraphFacts、Dataflow、StructureFacts
//! 分段输出，方便排查时沿着结构层内部事实链向后看。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, ProtoSummaryRow, build_proto_nodes,
    colorize_debug_text, compute_focus_plan, define_stage_dump, format_breadcrumb,
    format_display_set, format_proto_summary_row,
};
use crate::decompile::{DebugOptions, DecompileState};

use super::common::{
    BranchCandidate, BranchRegionFact, BranchValueMergeCandidate, GenericPhiMaterialization,
    GenericPhiSource, GotoRequirement, LoopCandidate, LoopExitValueMergeCandidate,
    LoopSourceBindings, LoopValueMerge, RegionFact, ScopeCandidate, ShortCircuitCandidate,
    ShortCircuitExit, ShortCircuitNode, ShortCircuitTarget, ShortCircuitValueIncoming,
    StructureFacts,
};
use super::{BlockOwner, CleanupDisposition, EdgeOwner, PhiIncomingDisposition};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    parent: Option<usize>,
    depth: usize,
    facts: &'a StructureFacts,
}

define_stage_dump! {
    /// Structure 阶段的调试导出。
    pub fn dump_structure(state, options) => Structure,
        dump_structure_stage(state, options)?;
}

fn dump_structure_stage(
    state: &DecompileState,
    options: &DebugOptions,
) -> Result<String, crate::decompile::DecompileError> {
    let mut output = String::new();

    append_section(
        &mut output,
        super::cfg::dump_cfg_graph(
            state.require_cfg()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );
    append_section(
        &mut output,
        super::cfg::dump_graph_facts_tree(
            state.require_graph_facts()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );
    append_section(
        &mut output,
        super::cfg::dump_dataflow_facts(
            state.require_lowered()?,
            state.require_cfg()?,
            state.require_dataflow()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );
    append_section(
        &mut output,
        dump_structure_facts(
            state.require_structure_facts()?,
            options.detail,
            &options.filters,
            options.color,
        ),
    );

    Ok(output)
}

fn append_section(output: &mut String, section: String) {
    if !output.is_empty() {
        output.push('\n');
    }
    output.push_str(&section);
    if !output.ends_with('\n') {
        output.push('\n');
    }
}

/// 输出 StructureFacts 的人类可读摘要。
fn dump_structure_facts(
    structure: &StructureFacts,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let entries = collect_proto_entries(structure);
    let plan = plan_focus(&entries, filters);

    let _ = writeln!(output, "===== Dump Structure =====");
    let _ = writeln!(
        output,
        "structure detail={} protos={}",
        detail,
        entries.len()
    );
    if let Some(proto_id) = filters.proto {
        let _ = writeln!(output, "filters proto=proto#{proto_id}");
    }
    let _ = writeln!(output, "filters proto_depth={}", filters.proto_depth);
    if let Some(breadcrumb) = format_breadcrumb(&plan) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    if plan.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return colorize_debug_text(&output, color);
    }

    for entry in &entries {
        if plan.is_elided(entry.id) {
            let indent = "  ".repeat(entry.depth);
            let _ = writeln!(
                output,
                "{indent}{}",
                format_proto_summary_row(&build_summary_row(entry)),
            );
            continue;
        }
        if !plan.is_visible(entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth);
        let _ = writeln!(
            output,
            "{indent}proto#{} branches={} branch-regions={} branch-values={} loops={} short-circuits={} gotos={} regions={} scopes={}",
            entry.id,
            entry.facts.branch_candidates.len(),
            entry.facts.branch_region_facts.len(),
            entry.facts.branch_value_merge_candidates.len(),
            entry.facts.loop_candidates.len(),
            entry.facts.short_circuit_candidates.len(),
            entry.facts.goto_requirements.len(),
            entry.facts.region_facts.len(),
            entry.facts.scope_candidates.len(),
        );

        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(output, "{indent}  branch candidates");
        write_branches(&mut output, &indent, &entry.facts.branch_candidates);

        let _ = writeln!(output, "{indent}  structure plan");
        write_plan(&mut output, &indent, entry.facts);

        let _ = writeln!(output, "{indent}  branch region facts");
        write_branch_regions(&mut output, &indent, &entry.facts.branch_region_facts);

        let _ = writeln!(output, "{indent}  branch value merges");
        write_branch_value_merges(
            &mut output,
            &indent,
            &entry.facts.branch_value_merge_candidates,
        );

        let _ = writeln!(output, "{indent}  generic phi materializations");
        write_generic_phi_materializations(
            &mut output,
            &indent,
            entry.facts.generic_phi_materializations(),
        );

        let _ = writeln!(output, "{indent}  loop candidates");
        write_loops(&mut output, &indent, &entry.facts.loop_candidates);

        let _ = writeln!(output, "{indent}  short-circuit candidates");
        write_short_circuits(&mut output, &indent, &entry.facts.short_circuit_candidates);

        let _ = writeln!(output, "{indent}  goto requirements");
        write_gotos(&mut output, &indent, &entry.facts.goto_requirements);

        let _ = writeln!(output, "{indent}  region facts");
        write_regions(&mut output, &indent, &entry.facts.region_facts);

        let _ = writeln!(output, "{indent}  scope candidates");
        write_scopes(&mut output, &indent, &entry.facts.scope_candidates);
    }

    colorize_debug_text(&output, color)
}

fn write_plan(output: &mut String, indent: &str, facts: &StructureFacts) {
    let blocks = facts
        .plan
        .block_owners
        .iter()
        .enumerate()
        .map(|(index, owner)| format!("#{index}={}", format_block_owner(*owner)))
        .collect::<Vec<_>>()
        .join(", ");
    let edges = facts
        .plan
        .edge_owners
        .iter()
        .enumerate()
        .map(|(index, owner)| format!("#{index}={}", format_edge_owner(*owner)))
        .collect::<Vec<_>>()
        .join(", ");
    let unstructured_membership = facts
        .plan
        .unstructured_region_by_block
        .iter()
        .enumerate()
        .filter_map(|(index, region)| region.map(|region| format!("#{index}=r{}", region.index())))
        .collect::<Vec<_>>()
        .join(", ");
    let cleanup_dispositions = facts
        .plan
        .cleanup_dispositions
        .iter()
        .enumerate()
        .filter_map(|(index, disposition)| {
            disposition
                .map(|disposition| format!("@{index}={}", format_cleanup_disposition(disposition)))
        })
        .collect::<Vec<_>>()
        .join(", ");
    let unstructured_layouts = facts
        .plan
        .unstructured_layouts
        .iter()
        .enumerate()
        .filter_map(|(index, layout)| {
            layout.as_ref().map(|layout| {
                format!(
                    "r{index}=blocks:{} continuation:#{}",
                    format_display_set(&layout.blocks),
                    layout.continuation.index()
                )
            })
        })
        .collect::<Vec<_>>()
        .join(", ");
    let phi_incomings = facts
        .plan
        .phi_incoming_dispositions
        .iter()
        .enumerate()
        .map(|(index, owners)| {
            format!(
                "p{index}=[{}]",
                owners
                    .iter()
                    .map(|owner| format_phi_incoming_disposition(*owner))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(output, "{indent}    blocks [{blocks}]");
    let _ = writeln!(output, "{indent}    edges [{edges}]");
    let _ = writeln!(
        output,
        "{indent}    unstructured-membership [{unstructured_membership}]"
    );
    let _ = writeln!(
        output,
        "{indent}    unstructured-layouts [{unstructured_layouts}]"
    );
    let _ = writeln!(output, "{indent}    phi-incomings [{phi_incomings}]");
    let _ = writeln!(output, "{indent}    cleanups [{cleanup_dispositions}]");
}

fn format_phi_incoming_disposition(disposition: PhiIncomingDisposition) -> &'static str {
    match disposition {
        PhiIncomingDisposition::Dead => "dead",
        PhiIncomingDisposition::Unreachable => "unreachable",
        PhiIncomingDisposition::EdgeCopy => "edge-copy",
        PhiIncomingDisposition::Merge => "merge",
    }
}

fn format_cleanup_disposition(disposition: CleanupDisposition) -> String {
    match disposition {
        CleanupDisposition::Unreachable => "unreachable".to_owned(),
        CleanupDisposition::ExplicitTbc => "explicit-tbc".to_owned(),
        CleanupDisposition::GenericFor(id) => format!("generic-for:c{}", id.index()),
        CleanupDisposition::LoopTbcBoundary(id) => {
            format!("loop-tbc-boundary:c{}", id.index())
        }
        CleanupDisposition::ExplicitTbcBoundary => "explicit-tbc-boundary".to_owned(),
        CleanupDisposition::LexicalScope(id) => format!("lexical-scope:s{}", id.index()),
    }
}

fn format_block_owner(owner: BlockOwner) -> String {
    match owner {
        BlockOwner::Unreachable => "unreachable".to_owned(),
        BlockOwner::Linear => "linear".to_owned(),
        BlockOwner::Branch(id) => format!("branch:c{}", id.index()),
        BlockOwner::Loop(id) => format!("loop:c{}", id.index()),
        BlockOwner::Unstructured(id) => format!("unstructured:r{}", id.index()),
        BlockOwner::Exit => "exit".to_owned(),
    }
}

fn format_edge_owner(owner: EdgeOwner) -> String {
    match owner {
        EdgeOwner::Unreachable => "unreachable".to_owned(),
        EdgeOwner::Linear => "linear".to_owned(),
        EdgeOwner::Branch(id) => format!("branch:c{}", id.index()),
        EdgeOwner::Loop(id) => format!("loop:c{}", id.index()),
        EdgeOwner::Unstructured(id) => format!("unstructured:r{}", id.index()),
        EdgeOwner::Goto(id) => format!("goto:g{}", id.index()),
        EdgeOwner::Terminal => "terminal".to_owned(),
    }
}

fn collect_proto_entries(root: &StructureFacts) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, None, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a>(
    facts: &'a StructureFacts,
    parent: Option<usize>,
    depth: usize,
    entries: &mut Vec<ProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(ProtoEntry {
        id,
        parent,
        depth,
        facts,
    });
    for child in &facts.children {
        collect_proto_entries_inner(child, Some(id), depth + 1, entries);
    }
}

fn plan_focus(entries: &[ProtoEntry<'_>], filters: &DebugFilters) -> FocusPlan {
    let parents: Vec<Option<usize>> = entries.iter().map(|e| e.parent).collect();
    let nodes = build_proto_nodes(&parents);
    compute_focus_plan(&nodes, &filters.as_focus_request())
}

fn build_summary_row(entry: &ProtoEntry<'_>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        depth_below_focus: entry.depth,
        name: None,
        first: None,
        lines: None,
        instrs: None,
        children: Some(entry.facts.children.len()),
    }
}

fn write_branches(output: &mut String, indent: &str, candidates: &[BranchCandidate]) {
    if candidates.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    header=#{} kind={} then=#{} else={} merge={} invert={}",
            candidate.header.index(),
            format_branch_kind(candidate.kind),
            candidate.then_entry.index(),
            format_optional_block(candidate.else_entry),
            format_optional_block(candidate.merge),
            candidate.invert_hint,
        );
    }
}

fn write_loops(output: &mut String, indent: &str, candidates: &[LoopCandidate]) {
    if candidates.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    header=#{} preheader={} kind={} bindings={} body-scope={} control={} continue={} continue-edges={} condition={} exits={} backedges={} blocks={}",
            candidate.header.index(),
            format_optional_block(candidate.preheader),
            format_loop_kind(candidate.kind_hint),
            format_loop_source_bindings(candidate.source_bindings),
            format_display_set(&candidate.body_scope_blocks),
            format_display_set(&candidate.control_blocks),
            format_optional_block(candidate.continue_target),
            format_display_set(&candidate.continue_edges),
            format_optional_block(candidate.condition_header),
            format_display_set(&candidate.exits),
            format_display_set(&candidate.backedges),
            format_display_set(&candidate.blocks),
        );
        for value in &candidate.header_value_merges {
            write_loop_value_merge(output, indent, "header", value);
        }
        for exit in &candidate.exit_value_merges {
            write_loop_exit_value_merge(output, indent, exit);
        }
    }
}

fn write_branch_regions(output: &mut String, indent: &str, facts: &[BranchRegionFact]) {
    if facts.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for fact in facts {
        let structured = fact.explicit_structured_blocks().map_or_else(
            || {
                format!(
                    "dom-subtree(#{}) - dom-subtree(#{})",
                    fact.header.index(),
                    fact.merge.index()
                )
            },
            format_display_set,
        );
        let _ = writeln!(
            output,
            "{indent}    header=#{} kind={} merge=#{} structured={}",
            fact.header.index(),
            format_branch_kind(fact.kind),
            fact.merge.index(),
            structured,
        );
    }
}

fn write_generic_phi_materializations(
    output: &mut String,
    indent: &str,
    candidates: impl IntoIterator<Item = GenericPhiMaterialization>,
) {
    let mut candidates = candidates.into_iter().peekable();
    if candidates.peek().is_none() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    block=#{} phi=p{} reg={} source={}",
            candidate.block.index(),
            candidate.phi_id.index(),
            candidate.reg,
            format_generic_phi_source(candidate.source),
        );
    }
}

fn format_generic_phi_source(source: GenericPhiSource) -> String {
    match source {
        GenericPhiSource::IdomExit(block) => format!("idom-exit:#{}", block.index()),
        GenericPhiSource::Unresolved => "unresolved".to_string(),
    }
}

fn write_branch_value_merges(
    output: &mut String,
    indent: &str,
    candidates: &[BranchValueMergeCandidate],
) {
    if candidates.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    header=#{} merge=#{} values={}",
            candidate.header.index(),
            candidate.merge.index(),
            candidate.values.len(),
        );
        for value in &candidate.values {
            let _ = writeln!(
                output,
                "{indent}      phi=p{} reg={} then-preds={} then-values={} then-entry-values={} then-update-values={} else-preds={} else-values={} else-entry-values={} else-update-values={}",
                value.phi_id.index(),
                value.reg,
                format_display_set(&value.then_arm.preds),
                format_display_set(&value.then_arm.values),
                format_display_set(&value.then_arm.entry_values),
                format_display_set(&value.then_arm.update_values),
                format_display_set(&value.else_arm.preds),
                format_display_set(&value.else_arm.values),
                format_display_set(&value.else_arm.entry_values),
                format_display_set(&value.else_arm.update_values),
            );
        }
    }
}

fn write_short_circuits(output: &mut String, indent: &str, candidates: &[ShortCircuitCandidate]) {
    if candidates.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    header=#{} entry=n{} nodes={} exit={} result={} phi={} reducible={} blocks={} entry-value={}",
            candidate.header.index(),
            candidate.entry.index(),
            candidate.nodes.len(),
            format_short_circuit_exit(&candidate.exit),
            candidate
                .result_reg
                .map(|r| r.to_string())
                .unwrap_or_else(|| "-".to_owned()),
            candidate
                .result_phi_id
                .map(|phi_id| format!("p{}", phi_id.index()))
                .unwrap_or_else(|| "-".to_owned()),
            candidate.reducible,
            format_display_set(&candidate.blocks),
            candidate
                .entry_value
                .map(|value| value.to_string())
                .unwrap_or_else(|| "-".to_string()),
        );
        if !candidate.value_incomings.is_empty() {
            let _ = writeln!(
                output,
                "{indent}      value-incomings={}",
                format_short_circuit_value_incomings(&candidate.value_incomings),
            );
        }
        write_short_circuit_nodes(output, indent, &candidate.nodes);
    }
}

fn write_short_circuit_nodes(output: &mut String, indent: &str, nodes: &[ShortCircuitNode]) {
    if nodes.is_empty() {
        return;
    }

    for node in nodes {
        let _ = writeln!(
            output,
            "{indent}      node n{} header=#{} truthy={} falsy={}",
            node.id.index(),
            node.header.index(),
            format_short_circuit_target(&node.truthy),
            format_short_circuit_target(&node.falsy),
        );
    }
}

fn format_short_circuit_exit(exit: &ShortCircuitExit) -> String {
    match exit {
        ShortCircuitExit::ValueMerge(block) => format!("value-merge=#{}", block.index()),
        ShortCircuitExit::BranchExit { truthy, falsy } => {
            format!(
                "branch(truthy=#{} falsy=#{})",
                truthy.index(),
                falsy.index()
            )
        }
    }
}

fn format_short_circuit_value_incomings(incomings: &[ShortCircuitValueIncoming]) -> String {
    incomings
        .iter()
        .map(|incoming| {
            format!(
                "{}=>{} local={}",
                incoming.pred,
                incoming.value,
                incoming
                    .latest_local_def
                    .map(|def| def.to_string())
                    .unwrap_or_else(|| "-".to_string())
            )
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_short_circuit_target(target: &ShortCircuitTarget) -> String {
    match target {
        ShortCircuitTarget::Node(node_ref) => format!("n{}", node_ref.index()),
        ShortCircuitTarget::Value(block) => format!("value=#{}", block.index()),
        ShortCircuitTarget::TruthyExit => "truthy-exit".to_owned(),
        ShortCircuitTarget::FalsyExit => "falsy-exit".to_owned(),
    }
}

fn write_gotos(output: &mut String, indent: &str, requirements: &[GotoRequirement]) {
    if requirements.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for requirement in requirements {
        let _ = writeln!(
            output,
            "{indent}    edge={} reason={}",
            requirement.edge,
            format_goto_reason(requirement.reason),
        );
    }
}

fn write_regions(output: &mut String, indent: &str, regions: &[RegionFact]) {
    if regions.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for region in regions {
        let _ = writeln!(
            output,
            "{indent}    entry=#{} kind=irreducible exits={} blocks={}",
            region.entry.index(),
            format_display_set(&region.exits),
            format_display_set(&region.blocks),
        );
    }
}

fn write_scopes(output: &mut String, indent: &str, scopes: &[ScopeCandidate]) {
    if scopes.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for scope in scopes {
        let _ = writeln!(
            output,
            "{indent}    entry=#{} kind=block-scope exit={} close-points={}",
            scope.entry.index(),
            format_optional_block(scope.exit),
            format_display_set(&scope.close_points),
        );
    }
}

fn format_optional_block(block: Option<crate::structure::BlockRef>) -> String {
    block
        .map(|block| block.to_string())
        .unwrap_or_else(|| "-".to_string())
}

fn format_branch_kind(kind: super::common::BranchKind) -> &'static str {
    match kind {
        super::common::BranchKind::IfThen => "if-then",
        super::common::BranchKind::IfElse => "if-else",
        super::common::BranchKind::Guard => "guard",
    }
}

fn format_loop_kind(kind: super::common::LoopKindHint) -> &'static str {
    match kind {
        super::common::LoopKindHint::WhileLike => "while-like",
        super::common::LoopKindHint::WhileTrueLike => "while-true-like",
        super::common::LoopKindHint::RepeatLike => "repeat-like",
        super::common::LoopKindHint::NumericForLike => "numeric-for-like",
        super::common::LoopKindHint::GenericForLike => "generic-for-like",
        super::common::LoopKindHint::Unknown => "unknown",
    }
}

fn format_loop_source_bindings(bindings: Option<LoopSourceBindings>) -> String {
    match bindings {
        Some(LoopSourceBindings::Numeric(reg)) => format!("numeric:{reg}"),
        Some(LoopSourceBindings::Generic(range)) => format!(
            "generic:{}..{}",
            range.start,
            range.start.index() + range.len
        ),
        None => "-".to_owned(),
    }
}

fn write_loop_exit_value_merge(
    output: &mut String,
    indent: &str,
    candidate: &LoopExitValueMergeCandidate,
) {
    let _ = writeln!(
        output,
        "{indent}      exit=#{} values={}",
        candidate.exit.index(),
        candidate.values.len(),
    );
    for value in &candidate.values {
        write_loop_value_merge(output, indent, "exit", value);
    }
}

fn write_loop_value_merge(output: &mut String, indent: &str, label: &str, value: &LoopValueMerge) {
    let _ = writeln!(
        output,
        "{indent}      {label} phi=p{} reg={} inside-preds={} inside-values={} outside-preds={} outside-values={}",
        value.phi_id.index(),
        value.reg,
        format_display_set(value.inside_arm.preds()),
        format_display_set(value.inside_arm.values()),
        format_display_set(value.outside_arm.preds()),
        format_display_set(value.outside_arm.values()),
    );
}

fn format_goto_reason(reason: super::common::GotoReason) -> &'static str {
    match reason {
        super::common::GotoReason::IrreducibleFlow => "irreducible-flow",
        super::common::GotoReason::MultiEntryRegion => "multi-entry-region",
        super::common::GotoReason::UnstructuredBreakLike => "unstructured-break-like",
        super::common::GotoReason::UnstructuredContinueLike => "unstructured-continue-like",
    }
}
