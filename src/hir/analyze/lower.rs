//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造、线性 block 降低、phi 物化和 low-IR 语句
//! 映射。这样做是为了让“公开入口”和“内部 lowering 细节”分开，后续继续拆 analyze
//! 子模块时边界会更清楚。

use std::collections::{BTreeMap, BTreeSet};

use super::bindings::build_bindings;
use super::exprs::{
    expr_for_closure_capture, expr_for_const, expr_for_reg_at_block_exit, expr_for_reg_use,
    expr_for_value_operand, is_multiret_results, lower_binary_op, lower_branch_cond,
    lower_table_access_expr, lower_table_access_target, lower_unary_op, lower_value_pack,
    lower_value_pack_components,
};
use super::helpers::{
    assign_stmt, branch_stmt, build_label_map_for_summary, decode_raw_string, empty_proto,
    goto_block, goto_stmt, label_for_block, return_stmt, unresolved_expr, unstructured_stmt,
};
use super::short_circuit::{recover_value_phi_expr, recover_value_phi_expr_with_allowed_blocks};
use super::structure::try_build_structured_body;
use crate::cfg::{BlockRef, Cfg, CfgGraph, DataflowFacts, GraphFacts, PhiId};
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirCapture, HirClosureExpr,
    HirExpr, HirLValue, HirLabel, HirLabelId, HirProto, HirProtoRef, HirStmt, HirTableSetList,
    HirUnaryExpr, LocalId, ParamId, TempId, UpvalueId,
};
use crate::structure::StructureFacts;
use crate::transformer::{CallKind, InstrRef, LowInstr, LoweredProto, Reg, ResultPack, ValuePack};

pub(super) struct ProtoBindings {
    pub(super) params: Vec<ParamId>,
    pub(super) locals: Vec<LocalId>,
    pub(super) upvalues: Vec<UpvalueId>,
    pub(super) temps: Vec<TempId>,
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) open_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
    pub(super) instr_open_defs: Vec<Option<TempId>>,
    pub(super) numeric_for_locals: BTreeMap<BlockRef, LocalId>,
    pub(super) generic_for_locals: BTreeMap<BlockRef, Vec<LocalId>>,
    pub(super) block_local_regs: BTreeMap<BlockRef, BTreeMap<Reg, LocalId>>,
}

pub(super) struct ProtoLowering<'a> {
    pub(super) proto: &'a LoweredProto,
    pub(super) cfg: &'a Cfg,
    pub(super) graph_facts: &'a GraphFacts,
    pub(super) dataflow: &'a DataflowFacts,
    pub(super) structure: &'a StructureFacts,
    pub(super) child_refs: &'a [HirProtoRef],
    pub(super) bindings: ProtoBindings,
}

#[derive(Clone, Copy)]
pub(super) struct ChildAnalyses<'a> {
    pub(super) cfg_graphs: &'a [CfgGraph],
    pub(super) graph_facts: &'a [GraphFacts],
    pub(super) dataflow: &'a [DataflowFacts],
    pub(super) structure: &'a [StructureFacts],
}

pub(super) fn lower_proto(
    proto: &LoweredProto,
    cfg: &Cfg,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    child_analyses: ChildAnalyses<'_>,
    protos: &mut Vec<HirProto>,
) -> HirProtoRef {
    let id = HirProtoRef(protos.len());
    protos.push(empty_proto(id));

    let child_refs = proto
        .children
        .iter()
        .zip(child_analyses.cfg_graphs.iter())
        .zip(child_analyses.graph_facts.iter())
        .zip(child_analyses.dataflow.iter())
        .zip(child_analyses.structure.iter())
        .map(
            |((((child_proto, child_cfg), child_graph_facts), child_dataflow), child_structure)| {
                lower_proto(
                    child_proto,
                    &child_cfg.cfg,
                    child_graph_facts,
                    child_dataflow,
                    child_structure,
                    ChildAnalyses {
                        cfg_graphs: &child_cfg.children,
                        graph_facts: &child_graph_facts.children,
                        dataflow: &child_dataflow.children,
                        structure: &child_structure.children,
                    },
                    protos,
                )
            },
        )
        .collect::<Vec<_>>();

    let bindings = build_bindings(proto, cfg, dataflow, structure);
    let lowering = ProtoLowering {
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
    };

    protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(decode_raw_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: lowering.bindings.params.clone(),
        locals: lowering.bindings.locals.clone(),
        upvalues: lowering.bindings.upvalues.clone(),
        temps: lowering.bindings.temps.clone(),
        body: build_proto_body(&lowering),
        children: child_refs,
    };

    id
}

fn build_proto_body(lowering: &ProtoLowering<'_>) -> HirBlock {
    if let Some(body) = try_build_structured_body(lowering) {
        body
    } else {
        lower_label_goto_body(lowering)
    }
}

fn unique_reachable_successor(cfg: &Cfg, block: BlockRef) -> Option<BlockRef> {
    let mut successors = cfg.succs[block.index()]
        .iter()
        .map(|edge_ref| cfg.edges[edge_ref.index()].to)
        .filter(|succ| cfg.reachable_blocks.contains(succ));
    let succ = successors.next()?;
    if successors.next().is_none() {
        Some(succ)
    } else {
        None
    }
}

fn lower_label_goto_body(lowering: &ProtoLowering<'_>) -> HirBlock {
    let label_map = build_label_map_for_summary(lowering.cfg);
    let reachable_blocks = lowering
        .cfg
        .block_order
        .iter()
        .copied()
        .filter(|block| lowering.cfg.reachable_blocks.contains(block))
        .filter(|block| *block != lowering.cfg.exit_block)
        .collect::<Vec<_>>();

    let mut stmts = Vec::new();
    for (index, block) in reachable_blocks.iter().copied().enumerate() {
        if let Some(label_id) = label_map.get(&block) {
            stmts.push(HirStmt::Label(Box::new(HirLabel { id: *label_id })));
        }

        let next_block = reachable_blocks.get(index + 1).copied();
        stmts.extend(lower_block_with_edge_copies(
            lowering, block, next_block, &label_map,
        ));
    }

    HirBlock { stmts }
}

fn lower_block_with_edge_copies(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    let range = lowering.cfg.blocks[block.index()].instrs;
    if range.is_empty() {
        return lower_linear_edge(lowering, block, next_block, label_map);
    }

    let last_instr = range
        .last()
        .expect("non-empty block should have a last instruction");
    let mut stmts = Vec::new();
    for instr_index in range.start.index()..range.end() {
        let instr_ref = InstrRef(instr_index);
        let instr = &lowering.proto.instrs[instr_index];
        if instr_ref == last_instr && is_control_terminator(instr) {
            stmts.extend(lower_control_instr_with_edge_copies(
                lowering, block, instr_ref, instr, next_block, label_map,
            ));
        } else {
            stmts.extend(lower_regular_instr(lowering, block, instr_ref, instr));
        }
    }

    if !is_control_terminator(&lowering.proto.instrs[last_instr.index()]) {
        stmts.extend(lower_linear_edge(lowering, block, next_block, label_map));
    }

    stmts
}

fn lower_linear_edge(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    let Some(target) = unique_reachable_successor(lowering.cfg, block) else {
        return Vec::new();
    };
    if target == lowering.cfg.exit_block {
        return Vec::new();
    }

    lower_edge_block(lowering, block, target, next_block, label_map).stmts
}

fn lower_control_instr_with_edge_copies(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Jump(jump) => {
            lower_edge_block(
                lowering,
                block,
                lowering.cfg.instr_to_block[jump.target.index()],
                next_block,
                label_map,
            )
            .stmts
        }
        LowInstr::Branch(branch) => {
            let then_target = lowering.cfg.instr_to_block[branch.then_target.index()];
            let else_target = lowering.cfg.instr_to_block[branch.else_target.index()];
            vec![branch_stmt(
                lower_branch_cond(lowering, block, instr_ref, branch.cond),
                lower_edge_block(lowering, block, then_target, next_block, label_map),
                Some(lower_edge_block(
                    lowering,
                    block,
                    else_target,
                    next_block,
                    label_map,
                )),
            )]
        }
        _ => lower_control_instr(lowering, block, instr_ref, instr, label_map),
    }
}

fn lower_edge_block(
    lowering: &ProtoLowering<'_>,
    from: BlockRef,
    to: BlockRef,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> HirBlock {
    let mut stmts = lower_edge_phi_copies(lowering, from, to);
    if to != lowering.cfg.exit_block && Some(to) != next_block {
        stmts.push(goto_stmt(label_map[&to]));
    }
    HirBlock { stmts }
}

fn lower_edge_phi_copies(
    lowering: &ProtoLowering<'_>,
    from: BlockRef,
    to: BlockRef,
) -> Vec<HirStmt> {
    if to == lowering.cfg.exit_block {
        return Vec::new();
    }

    let mut targets = Vec::new();
    let mut values = Vec::new();
    for phi in lowering
        .dataflow
        .phi_candidates
        .iter()
        .filter(|phi| phi.block == to)
    {
        targets.push(HirLValue::Temp(lowering.bindings.phi_temps[phi.id.index()]));
        values.push(expr_for_reg_at_block_exit(lowering, from, phi.reg));
    }

    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

/// 某些结构化路径会先把短路 header 的前缀语句物化出来，再跳到 merge block。
///
/// 这时 merge 上的 phi 表达式虽然跨过了候选区域，但其中引用的 header 临时值其实已经
/// 在当前 HIR 位置稳定存在。这里额外接收一组 `allowed_blocks`，显式告诉 phi 恢复逻辑
/// 哪些 block 的临时值已经“在更早的语句里落地”，避免把简单 `a and b` / `a or b`
/// 错误地退化回 `if + assign`。
pub(super) fn lower_phi_materialization_with_allowed_blocks_except(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    suppressed: &BTreeSet<PhiId>,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Vec<HirStmt> {
    lowering
        .dataflow
        .phi_candidates
        .iter()
        .filter(|phi| phi.block == block)
        .filter(|phi| !suppressed.contains(&phi.id))
        .filter_map(|phi| {
            let temp = lowering.bindings.phi_temps.get(phi.id.index()).copied()?;
            let value = recover_value_phi_expr_with_allowed_blocks(lowering, phi, allowed_blocks)
                .or_else(|| recover_value_phi_expr(lowering, phi))
                .unwrap_or_else(|| {
                    unresolved_expr(format!(
                        "phi block=#{} reg=r{}",
                        phi.block.index(),
                        phi.reg.index()
                    ))
                });
            Some(assign_stmt(vec![HirLValue::Temp(temp)], vec![value]))
        })
        .collect()
}

pub(super) fn lower_regular_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Move(move_instr) => fixed_assign(
            lowering,
            instr_ref,
            vec![expr_for_reg_use(lowering, block, instr_ref, move_instr.src)],
        ),
        LowInstr::LoadNil(_instr) => fixed_assign(
            lowering,
            instr_ref,
            lowering.bindings.instr_fixed_defs[instr_ref.index()]
                .iter()
                .map(|_temp| HirExpr::Nil)
                .collect(),
        ),
        LowInstr::LoadBool(load_bool) => {
            fixed_assign(lowering, instr_ref, vec![HirExpr::Boolean(load_bool.value)])
        }
        LowInstr::LoadConst(load_const) => fixed_assign(
            lowering,
            instr_ref,
            vec![expr_for_const(lowering.proto, load_const.value)],
        ),
        LowInstr::UnaryOp(unary) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Unary(Box::new(HirUnaryExpr {
                op: lower_unary_op(unary.op),
                expr: expr_for_reg_use(lowering, block, instr_ref, unary.src),
            }))],
        ),
        LowInstr::BinaryOp(binary) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Binary(Box::new(HirBinaryExpr {
                op: lower_binary_op(binary.op),
                lhs: expr_for_value_operand(lowering, block, instr_ref, binary.lhs),
                rhs: expr_for_value_operand(lowering, block, instr_ref, binary.rhs),
            }))],
        ),
        LowInstr::Concat(concat) => {
            let value = (0..concat.src.len)
                .map(|offset| {
                    expr_for_reg_use(
                        lowering,
                        block,
                        instr_ref,
                        Reg(concat.src.start.index() + offset),
                    )
                })
                .reduce(|lhs, rhs| {
                    HirExpr::Binary(Box::new(HirBinaryExpr {
                        op: HirBinaryOpKind::Concat,
                        lhs,
                        rhs,
                    }))
                })
                .unwrap_or_else(|| unresolved_expr("concat empty source"));
            fixed_assign(lowering, instr_ref, vec![value])
        }
        LowInstr::GetUpvalue(get_upvalue) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::UpvalueRef(UpvalueId(get_upvalue.src.index()))],
        ),
        LowInstr::SetUpvalue(set_upvalue) => vec![assign_stmt(
            vec![HirLValue::Upvalue(UpvalueId(set_upvalue.dst.index()))],
            vec![expr_for_reg_use(
                lowering,
                block,
                instr_ref,
                set_upvalue.src,
            )],
        )],
        LowInstr::GetTable(get_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![lower_table_access_expr(
                lowering,
                block,
                instr_ref,
                get_table.base,
                get_table.key,
            )],
        ),
        LowInstr::SetTable(set_table) => vec![assign_stmt(
            vec![lower_table_access_target(
                lowering,
                block,
                instr_ref,
                set_table.base,
                set_table.key,
            )],
            vec![expr_for_value_operand(
                lowering,
                block,
                instr_ref,
                set_table.value,
            )],
        )],
        LowInstr::NewTable(_new_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::TableConstructor(Box::default())],
        ),
        LowInstr::SetList(set_list) => lower_set_list(lowering, block, instr_ref, set_list),
        LowInstr::Call(call) => lower_call(
            lowering,
            block,
            instr_ref,
            call.kind,
            call.args,
            call.results,
            call.callee,
        ),
        LowInstr::TailCall(tail_call) => {
            vec![return_stmt(vec![HirExpr::Call(Box::new(HirCallExpr {
                callee: expr_for_reg_use(lowering, block, instr_ref, tail_call.callee),
                args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                multiret: true,
                method: matches!(tail_call.kind, CallKind::Method),
            }))])]
        }
        LowInstr::VarArg(vararg) => lower_vararg(lowering, instr_ref, vararg.results),
        LowInstr::Return(ret) => vec![return_stmt(lower_value_pack(
            lowering, block, instr_ref, ret.values,
        ))],
        LowInstr::Closure(closure) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Closure(Box::new(HirClosureExpr {
                proto: lowering.child_refs[closure.proto.index()],
                captures: closure
                    .captures
                    .iter()
                    .map(|capture| HirCapture {
                        value: expr_for_closure_capture(
                            lowering,
                            block,
                            instr_ref,
                            closure.dst,
                            capture.source,
                        ),
                    })
                    .collect(),
            }))],
        ),
        LowInstr::Close(close) => vec![unstructured_stmt(format!(
            "close from r{}",
            close.from.index()
        ))],
        LowInstr::NumericForInit(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-init index=r{} limit=r{} step=r{}",
                    instr.index.index(),
                    instr.limit.index(),
                    instr.step.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-init cond"),
                goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.body_target,
                )),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::NumericForLoop(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-loop index=r{} limit=r{} step=r{}",
                    instr.index.index(),
                    instr.limit.index(),
                    instr.step.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-loop cond"),
                goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.body_target,
                )),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    &build_label_map_for_summary(lowering.cfg),
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::GenericForCall(_instr) => fixed_or_open_assign(
            lowering,
            instr_ref,
            vec![unresolved_expr("generic-for-call")],
        ),
        LowInstr::GenericForLoop(_instr) => vec![unstructured_stmt("generic-for-loop")],
        LowInstr::Jump(_) | LowInstr::Branch(_) => Vec::new(),
    }
}

pub(super) fn lower_control_instr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &LowInstr,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> Vec<HirStmt> {
    match instr {
        LowInstr::Jump(jump) => vec![goto_stmt(label_for_block(
            lowering.cfg,
            label_map,
            jump.target,
        ))],
        LowInstr::Branch(branch) => vec![branch_stmt(
            lower_branch_cond(lowering, block, instr_ref, branch.cond),
            goto_block(label_for_block(lowering.cfg, label_map, branch.then_target)),
            Some(goto_block(label_for_block(
                lowering.cfg,
                label_map,
                branch.else_target,
            ))),
        )],
        LowInstr::Return(ret) => vec![return_stmt(lower_value_pack(
            lowering, block, instr_ref, ret.values,
        ))],
        LowInstr::TailCall(tail_call) => {
            vec![return_stmt(vec![HirExpr::Call(Box::new(HirCallExpr {
                callee: expr_for_reg_use(lowering, block, instr_ref, tail_call.callee),
                args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                multiret: true,
                method: matches!(tail_call.kind, CallKind::Method),
            }))])]
        }
        LowInstr::NumericForInit(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-init index=r{}",
                    instr.index.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-init cond"),
                goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    label_map,
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::NumericForLoop(instr) => vec![
            assign_stmt(
                lower_fixed_targets(lowering, instr_ref),
                vec![unresolved_expr(format!(
                    "numeric-for-loop index=r{}",
                    instr.index.index()
                ))],
            ),
            branch_stmt(
                unresolved_expr("numeric-for-loop cond"),
                goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)),
                Some(goto_block(label_for_block(
                    lowering.cfg,
                    label_map,
                    instr.exit_target,
                ))),
            ),
        ],
        LowInstr::GenericForLoop(instr) => vec![branch_stmt(
            unresolved_expr("generic-for-loop cond"),
            goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)),
            Some(goto_block(label_for_block(
                lowering.cfg,
                label_map,
                instr.exit_target,
            ))),
        )],
        _ => lower_regular_instr(lowering, block, instr_ref, instr),
    }
}

pub(super) fn is_control_terminator(instr: &LowInstr) -> bool {
    matches!(
        instr,
        LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::Return(_)
            | LowInstr::TailCall(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForLoop(_)
    )
}

fn lower_set_list(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    set_list: &crate::transformer::SetListInstr,
) -> Vec<HirStmt> {
    let (values, trailing_multivalue) =
        lower_value_pack_components(lowering, block, instr_ref, set_list.values);
    vec![HirStmt::TableSetList(Box::new(HirTableSetList {
        base: expr_for_reg_use(lowering, block, instr_ref, set_list.base),
        start_index: set_list.start_index,
        values,
        trailing_multivalue,
    }))]
}

fn lower_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    kind: CallKind,
    args: ValuePack,
    results: ResultPack,
    callee: Reg,
) -> Vec<HirStmt> {
    let expr = HirExpr::Call(Box::new(HirCallExpr {
        callee: expr_for_reg_use(lowering, block, instr_ref, callee),
        args: lower_value_pack(lowering, block, instr_ref, args),
        multiret: is_multiret_results(results),
        method: matches!(kind, CallKind::Method),
    }));

    if matches!(results, ResultPack::Ignore) {
        vec![HirStmt::CallStmt(Box::new(HirCallStmt {
            call: match expr {
                HirExpr::Call(call) => *call,
                _ => unreachable!("call lowering should always build a call expression"),
            },
        }))]
    } else {
        fixed_or_open_assign(lowering, instr_ref, vec![expr])
    }
}

fn lower_vararg(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    results: ResultPack,
) -> Vec<HirStmt> {
    let expr = HirExpr::VarArg;
    match results {
        ResultPack::Ignore => vec![unstructured_stmt("vararg ignore")],
        _ => fixed_or_open_assign(lowering, instr_ref, vec![expr]),
    }
}

fn fixed_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: Vec<HirExpr>,
) -> Vec<HirStmt> {
    let targets = lower_fixed_targets(lowering, instr_ref);
    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

fn fixed_or_open_assign(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    values: Vec<HirExpr>,
) -> Vec<HirStmt> {
    let mut targets = lower_fixed_targets(lowering, instr_ref);
    if let Some(open_target) = lowering.bindings.instr_open_defs[instr_ref.index()] {
        targets.push(HirLValue::Temp(open_target));
    }

    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

fn lower_fixed_targets(lowering: &ProtoLowering<'_>, instr_ref: InstrRef) -> Vec<HirLValue> {
    lowering.bindings.instr_fixed_defs[instr_ref.index()]
        .iter()
        .map(|temp| HirLValue::Temp(*temp))
        .collect()
}
