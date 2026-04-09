//! 这个文件承载 StructureFacts 层的共享调试输出。
//!
//! 结构候选本身就偏“解释型”事实，所以这里重点把 header / merge / exits /
//! reducible 这些最值钱的信息稳定打印出来，方便我们快速排查恢复决策。

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::debug::{DebugColorMode, DebugDetail, DebugFilters, colorize_debug_text};

use super::common::{
    BranchCandidate, BranchRegionFact, BranchValueMergeCandidate, GenericPhiMaterialization,
    GotoRequirement, LoopCandidate, LoopExitValueMergeCandidate, LoopSourceBindings,
    LoopValueMerge, RegionFact, ScopeCandidate, ShortCircuitCandidate, ShortCircuitExit,
    ShortCircuitNode, ShortCircuitTarget, ShortCircuitValueIncoming, StructureFacts,
};

#[derive(Debug, Clone, Copy)]
struct ProtoEntry<'a> {
    id: usize,
    depth: usize,
    facts: &'a StructureFacts,
}

/// 输出 StructureFacts 的人类可读摘要。
pub fn dump_structure(
    structure: &StructureFacts,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let entries = collect_proto_entries(structure);
    let visible = visible_proto_ids(&entries, filters);

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
    let _ = writeln!(output);

    for entry in &entries {
        if !visible.contains(&entry.id) {
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
            &entry.facts.generic_phi_materializations,
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

fn collect_proto_entries(root: &StructureFacts) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    collect_proto_entries_inner(root, 0, &mut entries);
    entries
}

fn collect_proto_entries_inner<'a>(
    facts: &'a StructureFacts,
    depth: usize,
    entries: &mut Vec<ProtoEntry<'a>>,
) {
    let id = entries.len();
    entries.push(ProtoEntry { id, depth, facts });
    for child in &facts.children {
        collect_proto_entries_inner(child, depth + 1, entries);
    }
}

fn visible_proto_ids(entries: &[ProtoEntry<'_>], filters: &DebugFilters) -> Vec<usize> {
    match filters.proto {
        Some(id) if entries.iter().any(|entry| entry.id == id) => vec![id],
        Some(_) => Vec::new(),
        None => entries.iter().map(|entry| entry.id).collect(),
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
            "{indent}    header=#{} preheader={} kind={} bindings={} continue={} exits={} reducible={} backedges={} blocks={}",
            candidate.header.index(),
            format_optional_block(candidate.preheader),
            format_loop_kind(candidate.kind_hint),
            format_loop_source_bindings(candidate.source_bindings),
            format_optional_block(candidate.continue_target),
            format_block_set(&candidate.exits),
            candidate.reducible,
            format_edge_refs(&candidate.backedges),
            format_block_set(&candidate.blocks),
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
        let _ = writeln!(
            output,
            "{indent}    header=#{} kind={} merge=#{} flow={} structured={} then-preds={} else-preds={}",
            fact.header.index(),
            format_branch_kind(fact.kind),
            fact.merge.index(),
            format_block_set(&fact.flow_blocks),
            format_block_set(&fact.structured_blocks),
            format_block_set(&fact.then_merge_preds),
            format_block_set(&fact.else_merge_preds),
        );
    }
}

fn write_generic_phi_materializations(
    output: &mut String,
    indent: &str,
    candidates: &[GenericPhiMaterialization],
) {
    if candidates.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }

    for candidate in candidates {
        let _ = writeln!(
            output,
            "{indent}    block=#{} phi=p{} reg={}",
            candidate.block.index(),
            candidate.phi_id.index(),
            format_reg(candidate.reg),
        );
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
                "{indent}      phi=p{} reg={} then-preds={} then-defs={} then-non-header-defs={} else-preds={} else-defs={} else-non-header-defs={}",
                value.phi_id.index(),
                format_reg(value.reg),
                format_block_set(&value.then_arm.preds),
                format_def_set(&value.then_arm.defs),
                format_def_set(&value.then_arm.non_header_defs),
                format_block_set(&value.else_arm.preds),
                format_def_set(&value.else_arm.defs),
                format_def_set(&value.else_arm.non_header_defs),
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
            "{indent}    header=#{} entry=n{} nodes={} exit={} result={} phi={} reducible={} blocks={} entry-defs={}",
            candidate.header.index(),
            candidate.entry.index(),
            candidate.nodes.len(),
            format_short_circuit_exit(&candidate.exit),
            candidate
                .result_reg
                .map(format_reg)
                .unwrap_or_else(|| "-".to_owned()),
            candidate
                .result_phi_id
                .map(|phi_id| format!("p{}", phi_id.index()))
                .unwrap_or_else(|| "-".to_owned()),
            candidate.reducible,
            format_block_set(&candidate.blocks),
            format_def_set(&candidate.entry_defs),
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
                format_def_set(&incoming.defs),
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
            "{indent}    #{} -> #{} reason={}",
            requirement.from.index(),
            requirement.to.index(),
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
            "{indent}    entry=#{} kind={} exits={} reducible={} structureable={} blocks={}",
            region.entry.index(),
            format_region_kind(region.kind),
            format_block_set(&region.exits),
            region.reducible,
            region.structureable,
            format_block_set(&region.blocks),
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
            "{indent}    entry=#{} kind={} exit={} close-points={}",
            scope.entry.index(),
            format_scope_kind(scope.kind),
            format_optional_block(scope.exit),
            format_instr_refs(&scope.close_points),
        );
    }
}

fn format_optional_block(block: Option<crate::cfg::BlockRef>) -> String {
    block
        .map(|block| block.to_string())
        .unwrap_or_else(|| "-".to_string())
}

fn format_block_set(blocks: &BTreeSet<crate::cfg::BlockRef>) -> String {
    if blocks.is_empty() {
        "[-]".to_string()
    } else {
        format!(
            "[{}]",
            blocks
                .iter()
                .map(|block| block.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_edge_refs(edges: &[crate::cfg::EdgeRef]) -> String {
    if edges.is_empty() {
        "[-]".to_string()
    } else {
        format!(
            "[{}]",
            edges
                .iter()
                .map(|edge| edge.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_instr_refs(instrs: &[crate::transformer::InstrRef]) -> String {
    if instrs.is_empty() {
        "[-]".to_string()
    } else {
        format!(
            "[{}]",
            instrs
                .iter()
                .map(|instr| instr.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_def_set(defs: &BTreeSet<crate::cfg::DefId>) -> String {
    if defs.is_empty() {
        "[-]".to_string()
    } else {
        format!(
            "[{}]",
            defs.iter()
                .map(|def| def.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn format_reg(reg: crate::transformer::Reg) -> String {
    reg.to_string()
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
        super::common::LoopKindHint::RepeatLike => "repeat-like",
        super::common::LoopKindHint::NumericForLike => "numeric-for-like",
        super::common::LoopKindHint::GenericForLike => "generic-for-like",
        super::common::LoopKindHint::Unknown => "unknown",
    }
}

fn format_loop_source_bindings(bindings: Option<LoopSourceBindings>) -> String {
    match bindings {
        Some(LoopSourceBindings::Numeric(reg)) => format!("numeric:{}", format_reg(reg)),
        Some(LoopSourceBindings::Generic(range)) => format!(
            "generic:{}..{}",
            format_reg(range.start),
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
        "{indent}      {label} phi=p{} reg={} inside-preds={} inside-defs={} outside-preds={} outside-defs={}",
        value.phi_id.index(),
        format_reg(value.reg),
        format_block_set_from_iter(value.inside_arm.preds()),
        format_def_set_from_iter(value.inside_arm.defs()),
        format_block_set_from_iter(value.outside_arm.preds()),
        format_def_set_from_iter(value.outside_arm.defs()),
    );
}

fn format_block_set_from_iter(blocks: impl Iterator<Item = crate::cfg::BlockRef>) -> String {
    format_block_set(&blocks.collect())
}

fn format_def_set_from_iter(defs: impl Iterator<Item = crate::cfg::DefId>) -> String {
    format_def_set(&defs.collect())
}

fn format_goto_reason(reason: super::common::GotoReason) -> &'static str {
    match reason {
        super::common::GotoReason::IrreducibleFlow => "irreducible-flow",
        super::common::GotoReason::CrossStructureJump => "cross-structure-jump",
        super::common::GotoReason::MultiEntryRegion => "multi-entry-region",
        super::common::GotoReason::UnstructuredBreakLike => "unstructured-break-like",
        super::common::GotoReason::UnstructuredContinueLike => "unstructured-continue-like",
    }
}

fn format_region_kind(kind: super::common::RegionKind) -> &'static str {
    match kind {
        super::common::RegionKind::Linear => "linear",
        super::common::RegionKind::BranchRegion => "branch-region",
        super::common::RegionKind::LoopRegion => "loop-region",
        super::common::RegionKind::Irreducible => "irreducible",
    }
}

fn format_scope_kind(kind: super::common::ScopeKind) -> &'static str {
    match kind {
        super::common::ScopeKind::BlockScope => "block-scope",
        super::common::ScopeKind::LoopScope => "loop-scope",
        super::common::ScopeKind::BranchScope => "branch-scope",
    }
}
