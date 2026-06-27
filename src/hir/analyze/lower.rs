//! 这个文件承载 HIR 初始恢复里真正的 lowering 内核。
//!
//! 外层 [analyze.rs](/Users/x3zvawq/workspace/unluac-rs/src/hir/analyze/mod.rs) 只负责组织模块和
//! 暴露主入口，这里集中放 proto 递归构造、线性 block 降低、phi 物化和 low-IR 语句
//! 映射。这样做是为了让“公开入口”和“内部 lowering 细节”分开，后续继续拆 analyze
//! 子模块时边界会更清楚。

use std::collections::{BTreeMap, BTreeSet};

use super::super::promotion::ProtoPromotionFacts;
use super::bindings::build_bindings;
use super::exprs::{
    expr_for_closure_capture, expr_for_const, expr_for_reg_at_block_exit, expr_for_reg_use,
    expr_for_value_operand, is_multiret_results, lower_binary_op, lower_branch_cond,
    lower_method_name, lower_table_access_expr, lower_table_access_target, lower_unary_op,
    lower_value_pack, lower_value_pack_components,
};
use super::helpers::{
    assign_stmt, binary_expr, branch_stmt, build_label_map_for_summary, concat_expr,
    decode_raw_string, empty_proto, goto_block, goto_stmt, label_for_block, return_stmt,
    unresolved_expr, unstructured_stmt,
};
use super::short_circuit::{
    recover_short_value_merge_expr_with_allowed_blocks, value_merge_candidates_in_block,
};
use super::structure::try_build_structured_body;
use crate::ast::AstTargetDialect;
use crate::decompile::{DecompileContext, DecompileState};
use crate::hir::common::{
    HirBinaryExpr, HirBinaryOpKind, HirBlock, HirCallExpr, HirCallStmt, HirCapture, HirClose,
    HirClosureExpr, HirExpr, HirLValue, HirLabel, HirLabelId, HirProto, HirProtoRef, HirStmt,
    HirTableSetList, HirToBeClosed, HirUnaryExpr, LocalId, ParamId, TempId, UpvalueId,
};
use crate::structure::{BlockRef, Cfg, CfgGraph, DataflowFacts, GraphFacts, PhiId};
use crate::structure::{ShortCircuitExit, StructureFacts};
use crate::transformer::{
    AccessKey, CallKind, GenericForCallInstr, GenericForLoopInstr, InstrRef, LowInstr,
    LoweredProto, Reg, ResultPack,
};

pub(super) struct ProtoBindings {
    pub(super) params: Vec<ParamId>,
    pub(super) param_debug_hints: Vec<Option<String>>,
    pub(super) locals: Vec<LocalId>,
    pub(super) local_debug_hints: Vec<Option<String>>,
    pub(super) upvalues: Vec<UpvalueId>,
    pub(super) upvalue_debug_hints: Vec<Option<String>>,
    pub(super) temps: Vec<TempId>,
    pub(super) temp_debug_locals: Vec<Option<String>>,
    pub(super) fixed_temps: Vec<TempId>,
    pub(super) open_temps: Vec<TempId>,
    pub(super) phi_temps: Vec<TempId>,
    pub(super) instr_fixed_defs: Vec<Vec<TempId>>,
    pub(super) instr_open_defs: Vec<Option<TempId>>,
    pub(super) entry_local_regs: BTreeMap<Reg, LocalId>,
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
    pub(super) dead_phis: BTreeSet<PhiId>,
}

#[derive(Default)]
pub(super) struct LowerArtifacts {
    pub(super) protos: Vec<HirProto>,
    pub(super) promotion_facts: Vec<ProtoPromotionFacts>,
}

pub(super) fn lower_proto(
    state: &DecompileState,
    context: &DecompileContext<'_>,
    artifacts: &mut LowerArtifacts,
) -> HirProtoRef {
    let lowered = state.lowered.as_ref().unwrap();
    let cfg = state.cfg.as_ref().unwrap();
    let graph_facts = state.graph_facts.as_ref().unwrap();
    let dataflow = state.dataflow.as_ref().unwrap();
    let structure = state.structure_facts.as_ref().unwrap();
    lower_proto_node(
        context.requested_target,
        &lowered.main,
        cfg,
        graph_facts,
        dataflow,
        structure,
        artifacts,
    )
}

fn lower_proto_node(
    target: AstTargetDialect,
    proto: &LoweredProto,
    cfg_graph: &CfgGraph,
    graph_facts: &GraphFacts,
    dataflow: &DataflowFacts,
    structure: &StructureFacts,
    artifacts: &mut LowerArtifacts,
) -> HirProtoRef {
    let cfg = &cfg_graph.cfg;
    let id = HirProtoRef(artifacts.protos.len());
    artifacts.protos.push(empty_proto(id));
    artifacts
        .promotion_facts
        .push(ProtoPromotionFacts::default());

    let child_refs = proto
        .children
        .iter()
        .zip(cfg_graph.children.iter())
        .zip(graph_facts.children.iter())
        .zip(dataflow.children.iter())
        .zip(structure.children.iter())
        .map(
            |((((child_proto, child_cfg), child_graph_facts), child_dataflow), child_structure)| {
                lower_proto_node(
                    target,
                    child_proto,
                    child_cfg,
                    child_graph_facts,
                    child_dataflow,
                    child_structure,
                    artifacts,
                )
            },
        )
        .collect::<Vec<_>>();

    let bindings = build_bindings(proto, cfg, graph_facts, dataflow, structure);
    let dead_phis = dataflow.compute_truly_dead_phis(cfg);
    let lowering = ProtoLowering {
        proto,
        cfg,
        graph_facts,
        dataflow,
        structure,
        child_refs: &child_refs,
        bindings,
        dead_phis,
    };

    artifacts.protos[id.index()] = HirProto {
        id,
        source: proto.source.as_ref().map(decode_raw_string),
        line_range: proto.line_range,
        signature: proto.signature,
        params: lowering.bindings.params.clone(),
        param_debug_hints: lowering.bindings.param_debug_hints.clone(),
        locals: lowering.bindings.locals.clone(),
        local_debug_hints: lowering.bindings.local_debug_hints.clone(),
        upvalues: lowering.bindings.upvalues.clone(),
        upvalue_debug_hints: lowering.bindings.upvalue_debug_hints.clone(),
        temps: lowering.bindings.temps.clone(),
        temp_debug_locals: lowering.bindings.temp_debug_locals.clone(),
        body: build_proto_body(target, &lowering),
        children: child_refs,
    };
    artifacts.promotion_facts[id.index()] = ProtoPromotionFacts::from_dataflow(proto, dataflow);

    id
}

fn build_proto_body(target: AstTargetDialect, lowering: &ProtoLowering<'_>) -> HirBlock {
    if let Some(body) = try_build_structured_body(target, lowering) {
        body
    } else {
        lower_label_goto_body(lowering)
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
    let Some(target) = lowering.cfg.unique_reachable_successor(block) else {
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
        LowInstr::GenericForLoop(generic_for) => vec![branch_stmt(
            generic_for_loop_continue_cond(lowering, block, instr_ref, generic_for),
            lower_generic_for_body_edge_block(lowering, block, generic_for, next_block, label_map),
            Some(lower_edge_block(
                lowering,
                block,
                lowering.cfg.instr_to_block[generic_for.exit_target.index()],
                next_block,
                label_map,
            )),
        )],
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
    for phi in lowering.dataflow.phi_candidates_in_block(to) {
        if lowering.dead_phis.contains(&phi.id) {
            continue;
        }
        targets.push(HirLValue::Temp(lowering.bindings.phi_temps[phi.id.index()]));
        values.push(expr_for_reg_at_block_exit(lowering, from, phi.reg));
    }

    if targets.is_empty() {
        Vec::new()
    } else {
        vec![assign_stmt(targets, values)]
    }
}

fn lower_generic_for_body_edge_block(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    generic_for: &GenericForLoopInstr,
    next_block: Option<BlockRef>,
    label_map: &BTreeMap<BlockRef, HirLabelId>,
) -> HirBlock {
    let instr_ref = lowering.cfg.blocks[block.index()]
        .instrs
        .last()
        .expect("generic-for-loop block should contain its terminator");
    let target = lowering.cfg.instr_to_block[generic_for.body_target.index()];
    let mut stmts = generic_for_control_update(lowering, block, instr_ref, generic_for);
    stmts.extend(lower_edge_block(lowering, block, target, next_block, label_map).stmts);
    HirBlock { stmts }
}

fn generic_phi_materializations_in_block<'a>(
    lowering: &'a ProtoLowering<'a>,
    block: BlockRef,
) -> impl Iterator<Item = crate::structure::GenericPhiMaterialization> + 'a {
    lowering
        .structure
        .generic_phi_materializations
        .iter()
        .copied()
        .filter(move |phi| phi.block == block)
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
    is_suppressed: impl Fn(PhiId) -> bool,
    allowed_blocks: &BTreeSet<BlockRef>,
) -> Vec<HirStmt> {
    let mut stmts = Vec::new();
    let mut covered_phi_ids = BTreeSet::new();
    let mut short_value_merges =
        value_merge_candidates_in_block(lowering, block).collect::<Vec<_>>();
    short_value_merges.sort_by_key(|candidate| match candidate.result_phi_id {
        Some(phi_id) => phi_id,
        None => unreachable!("value-merge short-circuit should carry a phi id"),
    });

    for short in short_value_merges {
        let Some(phi_id) = short.result_phi_id else {
            unreachable!("value-merge short-circuit should carry a phi id");
        };
        if is_suppressed(phi_id) || lowering.dead_phis.contains(&phi_id) {
            continue;
        }

        let ShortCircuitExit::ValueMerge(merge) = short.exit else {
            unreachable!("value merge candidate iterator should only yield value merges");
        };
        let Some(reg) = short.result_reg else {
            unreachable!("value merge short-circuit should carry a result reg");
        };
        let Some(temp) = lowering.bindings.phi_temps.get(phi_id.index()).copied() else {
            unreachable!("every phi id should have a temp binding");
        };
        covered_phi_ids.insert(phi_id);
        let value =
            recover_short_value_merge_expr_with_allowed_blocks(lowering, short, allowed_blocks)
                .unwrap_or_else(|| {
                    // 短路恢复失败时，兜底用支配者出口值近似。
                    lowering
                        .graph_facts
                        .dominator_tree
                        .parent
                        .get(merge.index())
                        .copied()
                        .flatten()
                        .map(|idom| expr_for_reg_at_block_exit(lowering, idom, reg))
                        .unwrap_or_else(|| {
                            unresolved_expr(format!(
                                "phi block=#{} reg=r{}",
                                merge.index(),
                                reg.index()
                            ))
                        })
                });
        stmts.push(assign_stmt(vec![HirLValue::Temp(temp)], vec![value]));
    }

    stmts.extend(
        generic_phi_materializations_in_block(lowering, block)
            .filter(|phi| !is_suppressed(phi.phi_id))
            .filter(|phi| !lowering.dead_phis.contains(&phi.phi_id))
            .filter(|phi| !covered_phi_ids.contains(&phi.phi_id))
            .filter_map(|phi| {
                let temp = lowering
                    .bindings
                    .phi_temps
                    .get(phi.phi_id.index())
                    .copied()?;
                // 兜底策略：用 phi 所在 block 的直接支配者出口处的寄存器值
                // 作为近似恢复。这是控制流分歧前的"初始值"——在大多数
                // "部分路径赋值、其余路径保留原值"的模式下语义正确。
                // 只有当所有到达路径都各自赋了不同的值、且没有被
                // branch_value_merge / short_circuit / loop 任何一种
                // 专用 pass 认领时，这个近似才可能偏离原始语义，但仍比
                // unresolved_expr（直接输出 nil + 错误注释）好得多。
                let value = lowering
                    .graph_facts
                    .dominator_tree
                    .parent
                    .get(phi.block.index())
                    .copied()
                    .flatten()
                    .map(|idom| expr_for_reg_at_block_exit(lowering, idom, phi.reg))
                    .unwrap_or_else(|| {
                        unresolved_expr(format!(
                            "phi block=#{} reg=r{}",
                            phi.block.index(),
                            phi.reg.index()
                        ))
                    });
                Some(assign_stmt(vec![HirLValue::Temp(temp)], vec![value]))
            }),
    );

    stmts
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
        LowInstr::LoadInteger(load_integer) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Integer(load_integer.value)],
        ),
        LowInstr::LoadNumber(load_number) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::Number(load_number.value)],
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
            vec![binary_expr(
                lower_binary_op(binary.op),
                expr_for_value_operand(lowering, block, instr_ref, binary.lhs),
                expr_for_value_operand(lowering, block, instr_ref, binary.rhs),
            )],
        ),
        LowInstr::Concat(concat) => {
            let value = concat_expr((0..concat.src.len).map(|offset| {
                expr_for_reg_use(
                    lowering,
                    block,
                    instr_ref,
                    Reg(concat.src.start.index() + offset),
                )
            }));
            fixed_assign(lowering, instr_ref, vec![value])
        }
        LowInstr::GetUpvalue(get_upvalue) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::UpvalueRef(UpvalueId(get_upvalue.src.index()))],
        ),
        LowInstr::SetUpvalue(set_upvalue) => vec![assign_stmt(
            vec![HirLValue::Upvalue(UpvalueId(set_upvalue.dst.index()))],
            vec![expr_for_value_operand(
                lowering,
                block,
                instr_ref,
                set_upvalue.src,
            )],
        )],
        LowInstr::GetTable(get_table) => {
            // `SELF` / `NAMECALL` 三元式会在 Move + GetTable 之后紧跟一个方法调用，
            // 该调用的 `method_name` 命中时 AST 端会走 `obj:method()` 糖，彻底忽略
            // GetTable 写入的目标寄存器。这里在 HIR 降级阶段直接丢弃这类装饰性的
            // GetTable，避免下游 `temp-inline` / `locals` 等 pass 把它保留成无意义的
            // `local x = obj.method` 语句。
            //
            // 只在 method_load 标记为真、键是字符串常量时跳过：这样和
            // `lower_method_name` 对 `MethodNameHint` 的成功条件一一对应，若常量不是
            // 字符串（理论上不会出现，但保险），依然按普通表访问发射。
            if get_table.method_load
                && let AccessKey::Const(const_ref) = get_table.key
                && matches!(
                    lowering
                        .proto
                        .constants
                        .common
                        .literals
                        .get(const_ref.index()),
                    Some(crate::parser::RawLiteralConst::String(_))
                )
            {
                Vec::new()
            } else {
                fixed_assign(
                    lowering,
                    instr_ref,
                    vec![lower_table_access_expr(
                        lowering,
                        block,
                        instr_ref,
                        get_table.base,
                        get_table.key,
                    )],
                )
            }
        }
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
        LowInstr::ErrNil(err_nnil) => {
            vec![HirStmt::ErrNil(Box::new(crate::hir::common::HirErrNil {
                value: expr_for_reg_use(lowering, block, instr_ref, err_nnil.subject),
                name: err_nnil.name.and_then(|const_ref| {
                    match lowering
                        .proto
                        .constants
                        .common
                        .literals
                        .get(const_ref.index())
                    {
                        Some(crate::parser::RawLiteralConst::String(value)) => {
                            Some(decode_raw_string(value))
                        }
                        _ => None,
                    }
                }),
            }))]
        }
        LowInstr::NewTable(_new_table) => fixed_assign(
            lowering,
            instr_ref,
            vec![HirExpr::TableConstructor(Box::default())],
        ),
        LowInstr::SetList(set_list) => lower_set_list(lowering, block, instr_ref, set_list),
        LowInstr::Call(call) => lower_call(lowering, block, instr_ref, call),
        LowInstr::TailCall(tail_call) => {
            // TailCall 总是展开所有返回值
            let method_name = lower_method_name(lowering.proto, tail_call.method_name);
            let is_method_sugar =
                matches!(tail_call.kind, CallKind::Method) && method_name.is_some();
            let callee = if is_method_sugar {
                // 方法调用糖下，AST 直接用 args[0]+method_name 重建 callee；
                // 这里主动置空，避免上游 method-load GetTable 的目标温度被
                // `temp-inline` / `locals` 等 pass 当成被读取的 live 值留下来。
                HirExpr::Nil
            } else {
                expr_for_reg_use(lowering, block, instr_ref, tail_call.callee)
            };
            vec![return_stmt(
                vec![HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    multiret: true,
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))],
                true,
            )]
        }
        LowInstr::VarArg(vararg) => lower_vararg(lowering, instr_ref, vararg.results),
        LowInstr::Return(ret) => {
            let trailing_multiret = matches!(ret.values, crate::transformer::ValuePack::Open(_));
            vec![return_stmt(
                lower_value_pack(lowering, block, instr_ref, ret.values),
                trailing_multiret,
            )]
        }
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
        LowInstr::Close(close) => vec![HirStmt::Close(Box::new(HirClose {
            from_reg: close.from.index(),
        }))],
        LowInstr::Tbc(tbc) => vec![HirStmt::ToBeClosed(Box::new(HirToBeClosed {
            reg_index: tbc.reg.index(),
            value: expr_for_reg_use(lowering, block, instr_ref, tbc.reg),
        }))],
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
        LowInstr::GenericForCall(instr) => {
            lower_generic_for_call(lowering, block, instr_ref, instr)
        }
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
        LowInstr::Return(ret) => {
            let trailing_multiret = matches!(ret.values, crate::transformer::ValuePack::Open(_));
            vec![return_stmt(
                lower_value_pack(lowering, block, instr_ref, ret.values),
                trailing_multiret,
            )]
        }
        LowInstr::TailCall(tail_call) => {
            let method_name = lower_method_name(lowering.proto, tail_call.method_name);
            let is_method_sugar =
                matches!(tail_call.kind, CallKind::Method) && method_name.is_some();
            let callee = if is_method_sugar {
                HirExpr::Nil
            } else {
                expr_for_reg_use(lowering, block, instr_ref, tail_call.callee)
            };
            vec![return_stmt(
                vec![HirExpr::Call(Box::new(HirCallExpr {
                    callee,
                    args: lower_value_pack(lowering, block, instr_ref, tail_call.args),
                    multiret: true,
                    method: matches!(tail_call.kind, CallKind::Method),
                    method_name,
                }))],
                true,
            )]
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
            generic_for_loop_continue_cond(lowering, block, instr_ref, instr),
            {
                let mut body = generic_for_control_update(lowering, block, instr_ref, instr);
                body.extend(
                    goto_block(label_for_block(lowering.cfg, label_map, instr.body_target)).stmts,
                );
                HirBlock { stmts: body }
            },
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

fn lower_generic_for_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> Vec<HirStmt> {
    fixed_or_open_assign(
        lowering,
        instr_ref,
        vec![generic_for_iterator_call(lowering, block, instr_ref, instr)],
    )
}

fn generic_for_iterator_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForCallInstr,
) -> HirExpr {
    let callee = expr_for_reg_use(lowering, block, instr_ref, instr.state.start);
    let args = (1..instr.state.len)
        .map(|offset| {
            expr_for_reg_use(
                lowering,
                block,
                instr_ref,
                Reg(instr.state.start.index() + offset),
            )
        })
        .collect();

    HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args,
        multiret: true,
        method: false,
        method_name: None,
    }))
}

fn generic_for_loop_continue_cond(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> HirExpr {
    let first_binding = generic_for_loop_first_binding_expr(lowering, block, instr_ref, instr);
    HirExpr::Binary(Box::new(HirBinaryExpr {
        op: HirBinaryOpKind::Eq,
        lhs: first_binding,
        rhs: HirExpr::Nil,
    }))
    .negate()
}

fn generic_for_control_update(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> Vec<HirStmt> {
    let target = match expr_for_reg_use(lowering, block, instr_ref, instr.control) {
        HirExpr::TempRef(temp) => HirLValue::Temp(temp),
        HirExpr::LocalRef(local) => HirLValue::Local(local),
        _ => return Vec::new(),
    };
    let value = generic_for_loop_first_binding_expr(lowering, block, instr_ref, instr);
    vec![assign_stmt(vec![target], vec![value])]
}

fn generic_for_loop_first_binding_expr(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    instr: &GenericForLoopInstr,
) -> HirExpr {
    // `TFORLOOP` 的判空对象是同一 header 中前一条 `GenericForCall` 刚写出的
    // 第一个返回值；不能用 loop 指令处对 binding 寄存器的 reaching value，否则会
    // 读到上一轮迭代的源码 local。
    let range = lowering.cfg.blocks[block.index()].instrs;
    if instr_ref.index() > range.start.index()
        && let Some(LowInstr::GenericForCall(_)) = lowering.proto.instrs.get(instr_ref.index() - 1)
        && let Some(temp) = lowering.bindings.instr_fixed_defs[instr_ref.index() - 1].first()
    {
        return HirExpr::TempRef(*temp);
    }

    expr_for_reg_use(lowering, block, instr_ref, instr.bindings.start)
}

fn lower_call(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    call: &crate::transformer::CallInstr,
) -> Vec<HirStmt> {
    let method_name = lower_method_name(lowering.proto, call.method_name);
    let is_method_sugar = matches!(call.kind, CallKind::Method) && method_name.is_some();
    // 当调用会被 AST 渲染成 `obj:method()` 糖时，AST 只读 args[0] 和
    // method_name，callee 被丢弃。这里直接把 callee 置为 Nil，从而让源自
    // `SELF` / `NAMECALL` 的 method-load GetTable 在 HIR 中也真正失去读者，
    // 配合同一 pass 里对 `method_load` 的跳过逻辑建立闭环。
    let callee = if is_method_sugar {
        HirExpr::Nil
    } else {
        expr_for_reg_use(lowering, block, instr_ref, call.callee)
    };
    let expr = HirExpr::Call(Box::new(HirCallExpr {
        callee,
        args: lower_value_pack(lowering, block, instr_ref, call.args),
        multiret: is_multiret_results(call.results),
        method: matches!(call.kind, CallKind::Method),
        method_name,
    }));

    if matches!(call.results, ResultPack::Ignore) {
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
