//! Structure 阶段的共享调试输出。
//!
//! dump 只展示已经冻结的 `StructurePlan` 与 `DebugBindingFacts`。候选是构建 plan 的
//! 临时 evidence，若继续把它们和最终 owner 并排打印，排错时就无法分辨 HIR 实际
//! 消费的是哪一套事实。

use std::fmt::Write as _;

use crate::debug::{
    DebugColorMode, DebugDetail, DebugFilters, FocusPlan, ProtoSummaryRow, build_proto_nodes,
    colorize_debug_text, compute_focus_plan, define_stage_dump, format_breadcrumb,
    format_display_set, format_proto_summary_row,
};
use crate::decompile::{DebugOptions, DecompileState};

use super::plan::EdgeActionPlacement;
use super::{
    BlockTerminatorKind, CleanupDisposition, ControlFlowFeature, EdgeTransfer,
    PhiIncomingDisposition, PlanRequirement, RegionId, RegionPlan, StructureFacts,
    UnstructuredLayoutItem,
};

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

fn dump_structure_facts(
    structure: &StructureFacts,
    detail: DebugDetail,
    filters: &DebugFilters,
    color: DebugColorMode,
) -> String {
    let mut output = String::new();
    let entries = collect_proto_entries(structure);
    let focus = plan_focus(&entries, filters);

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
    if let Some(breadcrumb) = format_breadcrumb(&focus) {
        let _ = writeln!(output, "focus {breadcrumb}");
    }
    let _ = writeln!(output);

    if focus.focus.is_none() {
        let _ = writeln!(output, "  <no proto matched filters>");
        return colorize_debug_text(&output, color);
    }

    for entry in &entries {
        if focus.is_elided(entry.id) {
            let indent = "  ".repeat(entry.depth);
            let _ = writeln!(
                output,
                "{indent}{}",
                format_proto_summary_row(&build_summary_row(entry)),
            );
            continue;
        }
        if !focus.is_visible(entry.id) {
            continue;
        }

        let indent = "  ".repeat(entry.depth);
        let plan = entry.facts.plan();
        let island_count = plan
            .regions()
            .filter(|(_, region)| matches!(region, RegionPlan::Unstructured { .. }))
            .count();
        let _ = writeln!(
            output,
            "{indent}proto#{} regions={} branches={} loops={} conditions={} islands={} labels={} edges={} phis={} scopes={} debug-bindings={} debug-conflicts={} requirements={}",
            entry.id,
            plan.regions.len(),
            plan.branches.len(),
            plan.loops.len(),
            plan.conditions.len(),
            island_count,
            plan.labels.len(),
            plan.edge_plans.len(),
            plan.phis.len(),
            plan.scopes.len(),
            entry.facts.debug_bindings.accepted.len(),
            entry.facts.debug_bindings.conflicts.len(),
            plan.requirements.entries.len(),
        );
        if matches!(detail, DebugDetail::Summary) {
            continue;
        }

        let _ = writeln!(output, "{indent}  region tree");
        write_region(&mut output, &indent, plan, plan.root(), 2, "root");

        let _ = writeln!(output, "{indent}  debug binding facts");
        write_debug_bindings(&mut output, &indent, entry.facts);

        let _ = writeln!(output, "{indent}  block terminators");
        write_block_terminators(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  condition plans");
        write_conditions(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  value decision plans");
        write_value_decisions(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  planned labels");
        write_labels(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  forward routes");
        write_forward_routes(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  edge transfers");
        write_edges(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  value owners");
        write_values(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  cleanup owners");
        write_cleanups(&mut output, &indent, plan);

        let _ = writeln!(output, "{indent}  requirements");
        write_requirements(&mut output, &indent, plan);
    }

    colorize_debug_text(&output, color)
}

fn write_debug_bindings(output: &mut String, indent: &str, facts: &StructureFacts) {
    if facts.debug_bindings.accepted.is_empty() && facts.debug_bindings.conflicts.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for binding in &facts.debug_bindings.accepted {
        let _ = writeln!(
            output,
            "{indent}    scope#{} source r{} pc={}..{} -> {}",
            binding.scope,
            binding.reg.index(),
            binding.start_pc,
            binding.end_pc,
            binding.value,
        );
    }
    for conflict in &facts.debug_bindings.conflicts {
        let scopes = conflict
            .scopes
            .iter()
            .map(|scope| format!("scope#{scope}"))
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            output,
            "{indent}    ignored conflict value={} scopes=[{}]",
            conflict.value, scopes,
        );
    }
}

fn write_value_decisions(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.value_decisions.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for (decision_id, decision) in plan.value_decisions() {
        let _ = writeln!(
            output,
            "{indent}    v{} entry=n{} merge=#{} result=p{} reg=r{} blocks={}",
            decision_id.index(),
            decision.entry.index(),
            decision.merge.index(),
            decision.result_phi.index(),
            decision.result_reg.index(),
            format_display_set(&decision.blocks),
        );
        for node in &decision.nodes {
            let _ = writeln!(
                output,
                "{indent}      n{} block=#{} predicate=@{} predicate-negated={}",
                node.id.index(),
                node.block.index(),
                node.predicate.index(),
                node.predicate_negated,
            );
            for (semantic, arc) in [("truthy", &node.truthy), ("falsy", &node.falsy)] {
                let target = match arc.target {
                    super::ValueDecisionTarget::Node(target) => {
                        format!("n{}", target.index())
                    }
                    super::ValueDecisionTarget::Leaf(target) => {
                        format!("leaf{}", target.index())
                    }
                    super::ValueDecisionTarget::CurrentValue(target) => {
                        format!("current(leaf{})", target.index())
                    }
                };
                let _ = writeln!(
                    output,
                    "{indent}        {semantic} polarity={:?} route={} target={target}",
                    arc.polarity,
                    format_display_set(&arc.route),
                );
            }
        }
        for leaf in &decision.leaves {
            let _ = writeln!(
                output,
                "{indent}      leaf{} block=#{} value={} latest-def={} terminal={} physical-pred=#{} physical-value={}",
                leaf.id.index(),
                leaf.block.index(),
                leaf.value,
                leaf.latest_local_def
                    .map_or_else(|| "-".to_owned(), |def| def.to_string()),
                leaf.terminal_edge,
                leaf.physical_pred.index(),
                leaf.physical_value,
            );
        }
    }
}

fn write_block_terminators(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.block_terminators.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for terminator in &plan.block_terminators {
        let kind = match terminator.kind {
            BlockTerminatorKind::SyntheticExit => "synthetic-exit".to_owned(),
            BlockTerminatorKind::Linear { edge } => edge.map_or_else(
                || "linear edge=-".to_owned(),
                |edge| format!("linear edge={edge}"),
            ),
            BlockTerminatorKind::Jump { instr, edge } => {
                format!("jump instr={instr} edge={edge}")
            }
            BlockTerminatorKind::Branch {
                instr,
                truthy,
                falsy,
            } => format!("branch instr={instr} truthy={truthy} falsy={falsy}"),
            BlockTerminatorKind::Return { instr, edge } => {
                format!("return instr={instr} edge={edge}")
            }
            BlockTerminatorKind::TailCall { instr, edge } => {
                format!("tail-call instr={instr} edge={edge}")
            }
            BlockTerminatorKind::NumericForInit { instr, body, exit } => {
                format!("numeric-for-init instr={instr} body={body} exit={exit}")
            }
            BlockTerminatorKind::NumericForLoop { instr, body, exit } => {
                format!("numeric-for-loop instr={instr} body={body} exit={exit}")
            }
            BlockTerminatorKind::GenericForLoop { instr, body, exit } => {
                format!("generic-for-loop instr={instr} body={body} exit={exit}")
            }
        };
        let _ = writeln!(
            output,
            "{indent}    {} instrs=[@{}..@{}) {kind}",
            terminator.block,
            terminator.instrs.start.index(),
            terminator.instrs.end(),
        );
    }
}

fn write_conditions(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.conditions.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for (condition_id, condition) in plan.conditions() {
        let _ = writeln!(
            output,
            "{indent}    c{} entry=n{} truthy={} falsy={}",
            condition_id.index(),
            condition.entry.index(),
            condition.truthy,
            condition.falsy,
        );
        for node in &condition.nodes {
            let value = node.materialized_value.map_or_else(
                || "control".to_owned(),
                |value| {
                    format!(
                        "value=p{} consumer=n{} use=@{} negated={} forwarded-callee={}",
                        value.phi.index(),
                        value.consumer.index(),
                        value.use_instr.index(),
                        value.negated,
                        value
                            .forwarded_callee
                            .map_or_else(|| "-".to_owned(), |def| def.to_string()),
                    )
                },
            );
            let _ = writeln!(
                output,
                "{indent}      n{} block=#{} predicate=@{} predicate-negated={} {value}",
                node.id.index(),
                node.block.index(),
                node.predicate.index(),
                node.predicate_negated,
            );
            for arc in &node.arcs {
                let target = match arc.target {
                    super::ConditionTarget::Node(target) => format!("n{}", target.index()),
                    super::ConditionTarget::Truthy => "truthy".to_owned(),
                    super::ConditionTarget::Falsy => "falsy".to_owned(),
                };
                let _ = writeln!(
                    output,
                    "{indent}        {:?} route={} connectors={} target={target}",
                    arc.polarity,
                    format_display_set(&arc.route),
                    format_display_set(&arc.connector_blocks),
                );
            }
        }
    }
}

fn write_region(
    output: &mut String,
    base_indent: &str,
    plan: &super::StructurePlan,
    id: RegionId,
    depth: usize,
    role: &str,
) {
    let indent = format!("{base_indent}{}", "  ".repeat(depth));
    let Some(region) = plan.region(id) else {
        let _ = writeln!(output, "{indent}{role}: r{} <missing>", id.index());
        return;
    };
    match region {
        RegionPlan::Block { block, .. } => {
            let emission = match plan.block_emission(*block) {
                Some(super::BlockEmissionPlan::ForwardedControl { outgoing }) => {
                    format!(" forwarded={outgoing}")
                }
                _ => String::new(),
            };
            let _ = writeln!(
                output,
                "{indent}{role}: r{} block #{}{}",
                id.index(),
                block.index(),
                emission,
            );
        }
        RegionPlan::Sequence { children, .. } => {
            let _ = writeln!(
                output,
                "{indent}{role}: r{} sequence children={}",
                id.index(),
                children.len()
            );
            for child in children {
                write_region(output, base_indent, plan, *child, depth + 1, "item");
            }
        }
        RegionPlan::Branch {
            plan: branch,
            entry,
            condition,
            then_arm,
            else_arm,
            continuation,
            ..
        } => {
            let payload = plan.branch(*branch);
            let _ = writeln!(
                output,
                "{indent}{role}: r{} branch b{} entry=#{} continuation={} condition={} inverted={} then={} else={}",
                id.index(),
                branch.index(),
                entry.index(),
                format_optional_block(*continuation),
                payload.map_or_else(
                    || "?".to_owned(),
                    |payload| format!("c{}", payload.condition.index())
                ),
                payload.is_some_and(|payload| payload.condition_inverted),
                payload.map_or_else(|| "?".to_owned(), |payload| payload.then_edge.to_string()),
                payload.map_or_else(|| "?".to_owned(), |payload| payload.else_edge.to_string()),
            );
            write_region(
                output,
                base_indent,
                plan,
                *condition,
                depth + 1,
                "condition",
            );
            write_region(output, base_indent, plan, *then_arm, depth + 1, "then");
            if let Some(else_arm) = else_arm {
                write_region(output, base_indent, plan, *else_arm, depth + 1, "else");
            }
        }
        RegionPlan::ValueDecision {
            plan: decision,
            entry,
            continuation,
            ..
        } => {
            let payload = plan.value_decision(*decision);
            let _ = writeln!(
                output,
                "{indent}{role}: r{} value-decision v{} entry=#{} continuation=#{} result={}",
                id.index(),
                decision.index(),
                entry.index(),
                continuation.index(),
                payload
                    .map(|payload| payload.result_phi.to_string())
                    .unwrap_or_else(|| "?".to_owned()),
            );
        }
        RegionPlan::Loop {
            plan: loop_,
            entry,
            preheader,
            control,
            body,
            normal_tail,
            ..
        } => {
            let payload = plan.loop_(*loop_);
            let _ = writeln!(
                output,
                "{indent}{role}: r{} loop l{} kind={} entry=#{} continuation={}",
                id.index(),
                loop_.index(),
                payload
                    .map(|payload| format_loop_kind(payload.kind))
                    .unwrap_or("<missing>"),
                entry.index(),
                payload
                    .map(|payload| format_optional_block(payload.continuation))
                    .unwrap_or_else(|| "-".to_owned()),
            );
            if let Some(payload) = payload {
                let _ = writeln!(output, "{indent}  normal-tail={:?}", payload.normal_tail);
                let _ = writeln!(
                    output,
                    "{indent}  propagated-break={}",
                    format_optional_region(payload.propagated_break),
                );
            }
            if let Some(preheader) = preheader {
                write_region(
                    output,
                    base_indent,
                    plan,
                    *preheader,
                    depth + 1,
                    "preheader",
                );
            }
            write_region(output, base_indent, plan, *control, depth + 1, "control");
            write_region(output, base_indent, plan, *body, depth + 1, "body");
            if let Some(normal_tail) = normal_tail {
                write_region(
                    output,
                    base_indent,
                    plan,
                    *normal_tail,
                    depth + 1,
                    "normal-tail",
                );
            }
            if let Some(tail) = payload.and_then(|payload| payload.exit_tail.as_ref()) {
                let _ = writeln!(
                    output,
                    "{indent}  exit-tail: normal={} block=#{} instrs=[@{}..@{}) continuation=#{} early=[{}] cleanup-block=#{} cleanup-route=[{}] cleanup=[{}]",
                    tail.normal_exit,
                    tail.block.index(),
                    tail.range.start.index(),
                    tail.range.end(),
                    tail.continuation.index(),
                    format_display_set(&tail.early_exits),
                    tail.cleanup_block.index(),
                    format_display_set(&tail.cleanup_route),
                    tail.cleanup
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(", "),
                );
            }
        }
        RegionPlan::Unstructured {
            entry,
            entries,
            layout,
            exits,
            ..
        } => {
            let layout_text = layout
                .iter()
                .map(|item| match item {
                    UnstructuredLayoutItem::Block(block) => format!("#{}", block.index()),
                    UnstructuredLayoutItem::Region(region) => format!("r{}", region.index()),
                })
                .collect::<Vec<_>>()
                .join(", ");
            let _ = writeln!(
                output,
                "{indent}{role}: r{} island entry=#{} entry-ports={} exit-ports={} layout=[{}]",
                id.index(),
                entry.index(),
                format_display_set(entries),
                format_display_set(exits),
                layout_text,
            );
            for child in layout.iter().filter_map(|item| match item {
                UnstructuredLayoutItem::Region(region) => Some(*region),
                UnstructuredLayoutItem::Block(_) => None,
            }) {
                write_region(
                    output,
                    base_indent,
                    plan,
                    child,
                    depth + 1,
                    "structured-item",
                );
            }
        }
    }
}

fn write_labels(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.labels.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for (id, label) in plan.labels() {
        let barriers = label
            .tbc_barriers
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let _ = writeln!(
            output,
            "{indent}    l{} block=#{} placement={:?} tbc=[{}]",
            id.index(),
            label.block.index(),
            label.placement,
            barriers,
        );
    }
}

fn write_edges(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.edge_plans.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for edge in &plan.edge_plans {
        let forwarded = edge
            .forward_route
            .map_or_else(|| "-".to_owned(), |route| format!("fr{}", route.index()));
        let copies = edge
            .phi_copies
            .iter()
            .map(|copy| format!("p{}<-{}", copy.phi_id.index(), copy.value))
            .collect::<Vec<_>>()
            .join(", ");
        let iteration = edge
            .iteration
            .iter()
            .map(|disposition| {
                format!(
                    "r{}:p{}<-{} via {:?}",
                    disposition.loop_region.index(),
                    disposition.target.index(),
                    disposition.incoming,
                    disposition.source,
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        let actions = match edge.action_placement {
            EdgeActionPlacement::BeforeTransfer => "before-transfer".to_owned(),
            EdgeActionPlacement::BeforeTrailingCleanup { cleanup } => format!(
                "before-cleanup[@{}..@{})",
                cleanup.start.index(),
                cleanup.end()
            ),
        };
        let relation = plan.edge_region_relation(edge.edge);
        let relation = relation.map_or_else(
            || "relation=-".to_owned(),
            |relation| {
                format!(
                    "relation=src:{} dst:{} lca:{} src-child:{} dst-child:{}",
                    format_optional_region(relation.source_owner),
                    format_optional_region(relation.target_owner),
                    format_optional_region(relation.lca),
                    format_optional_region(relation.source_child),
                    format_optional_region(relation.target_child),
                )
            },
        );
        let _ = writeln!(
            output,
            "{indent}    {} owner=r{} transfer={} actions={} forwarded={} {} phi=[{}] iteration=[{}]",
            edge.edge,
            edge.owner.index(),
            format_edge_transfer(plan, edge.transfer),
            actions,
            forwarded,
            relation,
            copies,
            iteration,
        );
    }
}

fn write_forward_routes(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.forward_routes().len() == 0 {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for (route_id, route) in plan.forward_routes() {
        let edges = plan.forward_route_edges(route_id).collect::<Vec<_>>();
        let _ = writeln!(
            output,
            "{indent}    fr{} owner=r{} kind={:?} edges={}",
            route_id.index(),
            route.loop_region.index(),
            route.kind,
            format_display_set(&edges),
        );
    }
}

fn write_values(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    if plan.phis.is_empty() {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for phi in &plan.phis {
        let _ = writeln!(
            output,
            "{indent}    p{} block=#{} reg={}{}",
            phi.phi.index(),
            phi.block.index(),
            phi.reg,
            plan.condition_value_owner(phi.phi).map_or_else(
                String::new,
                |(condition, node)| format!(
                    " condition-value=c{}/n{}",
                    condition.index(),
                    node.index()
                ),
            ),
        );
        for incoming in &phi.incomings {
            let edge = incoming
                .edge
                .map(|edge| edge.to_string())
                .unwrap_or_else(|| "entry".to_owned());
            let _ = writeln!(
                output,
                "{indent}      {edge} value={} owner={}",
                incoming.value,
                format_phi_disposition(incoming.disposition),
            );
        }
    }
}

fn write_cleanups(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    let mut any = false;
    for (index, disposition) in plan.cleanup_dispositions.iter().enumerate() {
        let Some(disposition) = disposition else {
            continue;
        };
        any = true;
        let _ = writeln!(
            output,
            "{indent}    @{index} owner={}",
            format_cleanup_disposition(*disposition)
        );
    }
    if !any {
        let _ = writeln!(output, "{indent}    <none>");
    }
}

fn write_requirements(output: &mut String, indent: &str, plan: &super::StructurePlan) {
    let requirements = plan.requirements();
    let required = requirements
        .required_features()
        .iter()
        .map(|feature| format_control_feature(*feature))
        .collect::<Vec<_>>()
        .join(", ");
    let unavailable = requirements
        .unavailable_features()
        .iter()
        .map(|feature| format_control_feature(*feature))
        .collect::<Vec<_>>()
        .join(", ");
    let _ = writeln!(
        output,
        "{indent}    features=[{}] unavailable=[{}]",
        required, unavailable
    );
    if requirements.iter().len() == 0 {
        let _ = writeln!(output, "{indent}    <none>");
        return;
    }
    for (id, requirement) in requirements.iter() {
        let text = match requirement {
            PlanRequirement::Goto {
                edge,
                label,
                reason,
            } => format!(
                "goto edge={} label=l{} block={} reason={}",
                edge,
                label.index(),
                plan.label(*label)
                    .map(|label| format!("#{}", label.block.index()))
                    .unwrap_or_else(|| "<missing>".to_owned()),
                format_goto_reason(*reason)
            ),
            PlanRequirement::Continue { edge, loop_region } => {
                format!("continue edge={} loop=r{}", edge, loop_region.index())
            }
            PlanRequirement::MultiEntryIsland {
                region,
                entry_count,
            } => format!(
                "multi-entry-island region=r{} entries={}",
                region.index(),
                entry_count
            ),
            PlanRequirement::UnresolvedValue { phi_id, block, reg } => format!(
                "unresolved-value phi=p{} block=#{} reg={}",
                phi_id.index(),
                block.index(),
                reg
            ),
        };
        let _ = writeln!(output, "{indent}    q{} {text}", id.index());
    }
}

fn format_edge_transfer(plan: &super::StructurePlan, transfer: EdgeTransfer) -> String {
    match transfer {
        EdgeTransfer::Unreachable => "unreachable".to_owned(),
        EdgeTransfer::Fallthrough => "fallthrough".to_owned(),
        EdgeTransfer::BranchArm(arm) => format!("branch-arm:{arm:?}"),
        EdgeTransfer::LoopBack(region) => format!("loop-back:r{}", region.index()),
        EdgeTransfer::Break(region) => format!("break:r{}", region.index()),
        EdgeTransfer::Continue(region) => format!("continue:r{}", region.index()),
        EdgeTransfer::Return => "return".to_owned(),
        EdgeTransfer::TailCall => "tail-call".to_owned(),
        EdgeTransfer::Goto(label, reason) => {
            let block = plan
                .label(label)
                .map(|label| format!("#{}", label.block.index()))
                .unwrap_or_else(|| "<missing>".to_owned());
            format!(
                "goto:l{}({block}):{}",
                label.index(),
                format_goto_reason(reason)
            )
        }
    }
}

fn format_phi_disposition(disposition: PhiIncomingDisposition) -> String {
    match disposition {
        PhiIncomingDisposition::Dead => "dead".to_owned(),
        PhiIncomingDisposition::EdgeCopy => "edge-copy".to_owned(),
        PhiIncomingDisposition::RegionInput(region) => {
            format!("region-input:r{}", region.index())
        }
        PhiIncomingDisposition::RegionResult(region) => {
            format!("region-result:r{}", region.index())
        }
        PhiIncomingDisposition::LoopCarried(region) => {
            format!("loop-carried:r{}", region.index())
        }
        PhiIncomingDisposition::DiagnosticUnresolved => "diagnostic-unresolved".to_owned(),
    }
}

fn format_cleanup_disposition(disposition: CleanupDisposition) -> String {
    match disposition {
        CleanupDisposition::Unreachable => "unreachable".to_owned(),
        CleanupDisposition::ExplicitTbc => "explicit-tbc".to_owned(),
        CleanupDisposition::LoopTbcBoundary(id) => {
            format!("loop-tbc-boundary:r{}", id.index())
        }
        CleanupDisposition::ExplicitTbcBoundary(id) => {
            format!("explicit-tbc-boundary:t{}", id.index())
        }
        CleanupDisposition::ExplicitTbcExit(id) => {
            format!("explicit-tbc-exit:t{}", id.index())
        }
        CleanupDisposition::LexicalScope(id) => format!("lexical-scope:s{}", id.index()),
    }
}

fn format_control_feature(feature: ControlFlowFeature) -> &'static str {
    match feature {
        ControlFlowFeature::GotoLabel => "goto-label",
        ControlFlowFeature::ContinueStatement => "continue",
    }
}

fn collect_proto_entries(root: &StructureFacts) -> Vec<ProtoEntry<'_>> {
    let mut entries = Vec::new();
    let mut pending = vec![(root, None, 0usize)];
    while let Some((facts, parent, depth)) = pending.pop() {
        let id = entries.len();
        entries.push(ProtoEntry {
            id,
            parent,
            depth,
            facts,
        });
        pending.extend(
            facts
                .children
                .iter()
                .rev()
                .map(|child| (child, Some(id), depth + 1)),
        );
    }
    entries
}

fn plan_focus(entries: &[ProtoEntry<'_>], filters: &DebugFilters) -> FocusPlan {
    let parents = entries.iter().map(|entry| entry.parent).collect::<Vec<_>>();
    let nodes = build_proto_nodes(&parents);
    compute_focus_plan(&nodes, &filters.as_focus_request())
}

fn build_summary_row(entry: &ProtoEntry<'_>) -> ProtoSummaryRow {
    ProtoSummaryRow {
        id: entry.id,
        name: None,
        first: None,
        lines: None,
        instrs: None,
        children: Some(entry.facts.children.len()),
    }
}

fn format_optional_block(block: Option<super::BlockRef>) -> String {
    block
        .map(|block| block.to_string())
        .unwrap_or_else(|| "-".to_owned())
}

fn format_optional_region(region: Option<RegionId>) -> String {
    region.map_or_else(|| "-".to_owned(), |region| format!("r{}", region.index()))
}

fn format_loop_kind(kind: super::LoopKindHint) -> &'static str {
    match kind {
        super::LoopKindHint::WhileLike => "while",
        super::LoopKindHint::WhileTrueLike => "while-true",
        super::LoopKindHint::RepeatLike => "repeat",
        super::LoopKindHint::NumericForLike => "numeric-for",
        super::LoopKindHint::GenericForLike => "generic-for",
        super::LoopKindHint::Unknown => "unknown",
    }
}

fn format_goto_reason(reason: super::GotoReason) -> &'static str {
    match reason {
        super::GotoReason::IrreducibleFlow => "irreducible-flow",
        super::GotoReason::MultiEntryRegion => "multi-entry-region",
        super::GotoReason::UnstructuredBreakLike => "unstructured-break-like",
        super::GotoReason::UnstructuredContinueLike => "unstructured-continue-like",
        super::GotoReason::CrossLoopContinueLike => "cross-loop-continue-like",
    }
}
