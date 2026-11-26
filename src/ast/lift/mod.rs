//! AST Lift 入口：将 `LoweredChunk` + `AnalysisChunk` 直接提升为干净的目标方言 `AstModule`。
//!
//! 跳过重型 HIR 层，直接沿 `Region` 控制树提升语句与表达式，
//! 采用顺序消费栈正向树化临时值，只在真正需要语义身份时物化为 `local`。

mod expr;
mod vars;

use std::collections::{BTreeMap, BTreeSet};

use crate::LuaString;
use crate::analysis::{AnalysisChunk, BlockId, ProtoAnalysis, SlotKey, SsaDef, UseSite, ValueId};
use crate::generate::GenerateMode;
use crate::parser::{ProtoLineRange, ProtoSignature, RawLiteralConst};
use crate::transformer::{
    CaptureSource, CloseKind, ClosureCreation, InstrRef, LowInstr, LoweredChunk, LoweredProto, Reg,
    SharedClosureRef,
};

use super::common::{
    AstAssign, AstBinaryExpr, AstBinaryOpKind, AstBindingRef, AstBlock, AstCallExpr, AstCapture,
    AstCaptureBinding, AstCaptureMode, AstExpr, AstFunctionExpr, AstGenericFor, AstGlobalAttr,
    AstGlobalBinding, AstGlobalBindingTarget, AstGlobalDecl, AstGlobalName, AstGoto, AstIf,
    AstLValue, AstLabel, AstLabelId, AstLocalAttr, AstLocalBinding, AstLocalDecl, AstModule,
    AstNameRef, AstNumericFor, AstProtoMeta, AstRepeat, AstReturn, AstStmt, AstSyntheticLocalId,
    AstTargetDialect, AstWhile, LocalId, ParamId, ProtoId, UpvalueId,
};
use super::error::AstLowerError;
use super::structure::{CondExpr, Region, StateArm, StateTransition, structure_proto};

use expr::PendingExpr;

#[derive(Clone)]
enum SyntheticProtoKind {
    Factory {
        upvalue_count: usize,
        inner_func: AstFunctionExpr,
    },
    /// `(function(t, offset, ...) local p = { ... }; for i = 1, select("#", ...) do t[offset + i] = p[i] end end)`
    OpenSetListPack,
}

#[derive(Clone)]
struct LiftJob {
    orig_idx: usize,
    parent_captures: Option<(ProtoId, Vec<AstCapture>)>,
    synthetic_wrapper: Option<SyntheticProtoKind>,
}

/// 维护全模块 proto 实例化注册表：
/// 1. 同一字节码子 proto 在不同调用点以不同捕获列表实例化（如 Luau `-O2` 内联）时自动克隆独立 `ProtoId`，
///    确保 Naming 为每个实例解析各自的父绑定名；
/// 2. 为动态 `DUPCLOSURE` 工厂包装分配合成 `ProtoId`，并严格保证 `parent_id < child_id` 拓扑序。
pub(super) struct ProtoRegistry {
    jobs: Vec<LiftJob>,
    instantiations: BTreeMap<(usize, ProtoId, Vec<AstCapture>), ProtoId>,
}

impl ProtoRegistry {
    fn new(proto_count: usize) -> Self {
        let jobs = (0..proto_count)
            .map(|orig_idx| LiftJob {
                orig_idx,
                parent_captures: None,
                synthetic_wrapper: None,
            })
            .collect();
        Self {
            jobs,
            instantiations: BTreeMap::new(),
        }
    }

    pub(super) fn claim_child(
        &mut self,
        orig_idx: usize,
        parent: ProtoId,
        captures: Vec<AstCapture>,
    ) -> ProtoId {
        let key = (orig_idx, parent, captures.clone());
        if let Some(&existing) = self.instantiations.get(&key) {
            return existing;
        }
        // 仅当原编号大于 parent（维持严格拓扑序 `parent < child`）且尚未被认领时直接复用原 `ProtoId`。
        if orig_idx > parent.index() && self.jobs[orig_idx].parent_captures.is_none() {
            self.jobs[orig_idx].parent_captures = Some((parent, captures));
            let id = ProtoId(orig_idx);
            self.instantiations.insert(key, id);
            return id;
        }
        let new_id = ProtoId(self.jobs.len());
        self.jobs.push(LiftJob {
            orig_idx,
            parent_captures: Some((parent, captures)),
            synthetic_wrapper: None,
        });
        self.instantiations.insert(key, new_id);
        new_id
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn alloc_synthetic_factory(
        &mut self,
        parent: ProtoId,
        wrapper_captures: Vec<AstCapture>,
        inner_orig_idx: usize,
        inner_params: Vec<ParamId>,
        inner_is_vararg: bool,
        captured_bindings: BTreeSet<AstBindingRef>,
        captured_params: BTreeSet<ParamId>,
    ) -> AstFunctionExpr {
        let wrapper_id = ProtoId(self.jobs.len());
        let upvalue_count = wrapper_captures.len();
        self.jobs.push(LiftJob {
            orig_idx: inner_orig_idx,
            parent_captures: Some((parent, wrapper_captures)),
            synthetic_wrapper: None,
        });
        let inner_captures: Vec<AstCapture> = (0..upvalue_count)
            .map(|i| AstCapture {
                binding: AstCaptureBinding::Upvalue(UpvalueId(i)),
                mode: AstCaptureMode::ByReference,
            })
            .collect();
        // `wrapper_id >= orig_count > inner_orig_idx`，`claim_child` 会自动分配 `inner_id > wrapper_id`，保持严格拓扑序。
        let inner_id = self.claim_child(inner_orig_idx, wrapper_id, inner_captures);
        let inner_func = AstFunctionExpr {
            function: inner_id,
            params: inner_params,
            is_vararg: inner_is_vararg,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_write_names: BTreeSet::new(),
        };
        self.jobs[wrapper_id.index()].synthetic_wrapper = Some(SyntheticProtoKind::Factory {
            upvalue_count,
            inner_func,
        });
        AstFunctionExpr {
            function: wrapper_id,
            params: Vec::new(),
            is_vararg: false,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings,
            captured_params,
            capture_write_names: BTreeSet::new(),
        }
    }

    pub(super) fn alloc_synthetic_open_setlist_pack(&mut self) -> AstFunctionExpr {
        let helper_id = ProtoId(self.jobs.len());
        self.jobs.push(LiftJob {
            orig_idx: 0,
            parent_captures: None,
            synthetic_wrapper: Some(SyntheticProtoKind::OpenSetListPack),
        });
        AstFunctionExpr {
            function: helper_id,
            params: vec![ParamId(0), ParamId(1)],
            is_vararg: true,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings: BTreeSet::new(),
            captured_params: BTreeSet::new(),
            capture_write_names: BTreeSet::new(),
        }
    }
}

/// 提升整个 chunk 为 `AstModule`（所有 proto 已完成结构化、表达式树化与最窄声明下沉）。
pub fn lift_module(
    lowered: &LoweredChunk,
    analysis: &AnalysisChunk,
    target: AstTargetDialect,
    _mode: GenerateMode,
) -> Result<AstModule, AstLowerError> {
    // 按 DFS 先序平铺 LoweredProto 引用，与 analysis.protos 一一对应。
    let mut lowered_protos = Vec::with_capacity(analysis.protos.len());
    let mut stack = vec![&lowered.main];
    while let Some(proto) = stack.pop() {
        lowered_protos.push(proto);
        for child in proto.children.iter().rev() {
            stack.push(child.as_ref());
        }
    }

    let proto_count = analysis.protos.len();
    let mut structured_cache: Vec<Option<(Region, usize)>> = vec![None; proto_count];
    let mut registry = ProtoRegistry::new(proto_count);
    let mut protos: Vec<AstProtoMeta> = Vec::with_capacity(proto_count);
    let mut ready_bodies: Vec<AstBlock> = Vec::with_capacity(proto_count);
    let mut next_synthetic = 0usize;

    // 先序提升（动态包含因不同捕获克隆出的 proto 与合成共享工厂包装），保证父先于子。
    let mut proto_idx = 0usize;
    while proto_idx < registry.jobs.len() {
        let job = registry.jobs[proto_idx].clone();
        if let Some(synth) = job.synthetic_wrapper {
            match synth {
                SyntheticProtoKind::Factory {
                    upvalue_count,
                    inner_func,
                } => {
                    let upvalues = (0..upvalue_count).map(UpvalueId).collect();
                    let meta = AstProtoMeta {
                        id: ProtoId(proto_idx),
                        source: None,
                        line_range: ProtoLineRange {
                            defined_start: 0,
                            defined_end: 0,
                        },
                        signature: ProtoSignature {
                            num_params: 0,
                            is_vararg: false,
                            has_vararg_param_reg: false,
                            named_vararg_table: false,
                            legacy_arg_slot: false,
                            legacy_arg_table: false,
                        },
                        params: Vec::new(),
                        param_debug_hints: Vec::new(),
                        local_count: 0,
                        local_debug_hints: Vec::new(),
                        vararg_param_local: None,
                        lexical_environment_local: None,
                        upvalues,
                        upvalue_debug_hints: vec![None; upvalue_count],
                        environment_upvalues: Vec::new(),
                        parent_captures: job.parent_captures,
                        source_origin: None,
                        state_machine_count: 0,
                    };
                    let body = AstBlock {
                        stmts: vec![AstStmt::Return(Box::new(AstReturn {
                            values: vec![AstExpr::FunctionExpr(Box::new(inner_func))],
                        }))],
                    };
                    protos.push(meta);
                    ready_bodies.push(body);
                }
                SyntheticProtoKind::OpenSetListPack => {
                    let t_ref = AstNameRef::Param(ParamId(0));
                    let offset_ref = AstNameRef::Param(ParamId(1));
                    let pack_local = LocalId(0);
                    let idx_local = LocalId(1);
                    let pack_ref = AstNameRef::Local(pack_local);
                    let idx_ref = AstNameRef::Local(idx_local);
                    let meta = AstProtoMeta {
                        id: ProtoId(proto_idx),
                        source: None,
                        line_range: ProtoLineRange {
                            defined_start: 0,
                            defined_end: 0,
                        },
                        signature: ProtoSignature {
                            num_params: 2,
                            is_vararg: true,
                            has_vararg_param_reg: false,
                            named_vararg_table: false,
                            legacy_arg_slot: false,
                            legacy_arg_table: false,
                        },
                        params: vec![ParamId(0), ParamId(1)],
                        param_debug_hints: vec![None, None],
                        local_count: 2,
                        local_debug_hints: vec![None, None],
                        vararg_param_local: None,
                        lexical_environment_local: None,
                        upvalues: Vec::new(),
                        upvalue_debug_hints: Vec::new(),
                        environment_upvalues: Vec::new(),
                        parent_captures: None,
                        source_origin: None,
                        state_machine_count: 0,
                    };
                    let select_count = AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Global(AstGlobalName {
                            text: "select".to_owned(),
                        })),
                        args: vec![
                            AstExpr::String(LuaString::from_bytes(b"#".to_vec())),
                            AstExpr::VarArg,
                        ],
                    }));
                    let dst_index = AstExpr::Binary(Box::new(AstBinaryExpr {
                        op: AstBinaryOpKind::Add,
                        lhs: AstExpr::Var(offset_ref),
                        rhs: AstExpr::Var(idx_ref.clone()),
                    }));
                    let body = AstBlock {
                        stmts: vec![
                            AstStmt::LocalDecl(Box::new(AstLocalDecl {
                                bindings: vec![AstLocalBinding {
                                    id: AstBindingRef::Local(pack_local),
                                    attr: AstLocalAttr::None,
                                    is_debug_hinted: false,
                                }],
                                values: vec![AstExpr::TableConstructor(Box::new(
                                    super::common::AstTableConstructor {
                                        fields: vec![super::common::AstTableField::Array(
                                            AstExpr::VarArg,
                                        )],
                                        is_puc_batched: false,
                                    },
                                ))],
                            })),
                            AstStmt::NumericFor(Box::new(AstNumericFor {
                                binding: AstBindingRef::Local(idx_local),
                                start: AstExpr::Integer(1),
                                limit: select_count,
                                step: AstExpr::Integer(1),
                                body: AstBlock {
                                    stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                                        targets: vec![AstLValue::IndexAccess(Box::new(
                                            super::common::AstIndexAccess {
                                                base: AstExpr::Var(t_ref),
                                                index: dst_index,
                                            },
                                        ))],
                                        values: vec![AstExpr::IndexAccess(Box::new(
                                            super::common::AstIndexAccess {
                                                base: AstExpr::Var(pack_ref),
                                                index: AstExpr::Var(idx_ref),
                                            },
                                        ))],
                                        compound_op: None,
                                    }))],
                                },
                            })),
                        ],
                    };
                    protos.push(meta);
                    ready_bodies.push(body);
                }
            }
            proto_idx += 1;
            continue;
        }

        let lproto = lowered_protos[job.orig_idx];
        let panalysis = &analysis.protos[job.orig_idx];
        if structured_cache[job.orig_idx].is_none() {
            let region = structure_proto(lproto, panalysis, target.version.control_flow_caps());
            let state_machine_count = region.count_state_machines();
            structured_cache[job.orig_idx] = Some((region, state_machine_count));
        }
        let (region, state_machine_count) = structured_cache[job.orig_idx].as_ref().unwrap();
        let state_machine_count = *state_machine_count;

        let mut lifter = ProtoLifter::new(
            ProtoId(proto_idx),
            lproto,
            panalysis,
            target,
            &mut next_synthetic,
            &mut registry,
        );
        count_region_gotos(region, &mut lifter.total_gotos_by_label);
        let mut body = lifter.lift_region_with_scope(region, true);
        lifter.flush_all_pending(&mut body.stmts);

        // 最窄支配块声明下沉（对跨循环回边未关闭的共享按引用捕获变量，保持声明在循环外部；
        // 对即将提升为共享局部函数的 `DUPCLOSURE` 局部标记为预声明，避免重复插入空 `local`）
        let loop_shared_capture_locals = lifter.compute_loop_shared_capture_locals();
        let predeclared_shared: BTreeSet<LocalId> = lifter
            .hoisted_shared_closures
            .iter()
            .map(|h| h.local)
            .collect();
        vars::insert_local_declarations(
            &mut body,
            &lifter.tbc_locals,
            &lifter.debug_hinted_locals,
            lifter.vararg_param_local,
            &loop_shared_capture_locals,
            &predeclared_shared,
        );
        // Lua 5.1 会省略函数入口处 `local x = nil` 的 `LOADNIL` 指令；若保留了源码 debug 信息且
        // 某 `start_pc == 0` 非形参源码局部在整个函数体内完全未被读写，仍须在入口声明以保住 `debug.getlocal`！
        lifter.prepend_unreferenced_entry_debug_locals(&mut body);
        // 把已计划的共享 `DUPCLOSURE` 局部函数按依赖顺序插入到其全部捕获局部声明之后，
        // 严格保持跨调用/跨迭代的闭包对象身份等价性（`f1 == f2` / NaN 捕获保鲜）。
        lifter.insert_hoisted_shared_closures(&mut body);
        // Luau `NEWCLOSURE` 捕获单定义字面量局部时插入死写保护 `if false then x = nil end`，
        // 阻止目标 Luau 编译器常量传播将其降格为共享 `DUPCLOSURE` 破坏新鲜闭包身份（`first ~= second`）。
        lifter.insert_luau_fresh_const_capture_guards(&mut body);

        let meta = lifter.into_proto_meta(job.parent_captures, state_machine_count);
        protos.push(meta);
        ready_bodies.push(body);
        proto_idx += 1;
    }

    // 把已提升的子函数体和 Lua 5.5 具名变参表绑定填回父函数体内的 `AstFunctionExpr`（后序挂接，支持共享闭包克隆体）。
    let supports_named_vararg = target.version == crate::decompile::DecompileDialect::Lua55;
    let total_protos = ready_bodies.len();
    for proto_idx in (0..total_protos).rev() {
        let mut block = std::mem::take(&mut ready_bodies[proto_idx]);
        attach_child_bodies(&mut block, &ready_bodies, &protos, supports_named_vararg);
        ready_bodies[proto_idx] = block;
    }

    let entry_body = ready_bodies.into_iter().next().unwrap_or_default();

    Ok(AstModule {
        entry_function: ProtoId(0),
        body: entry_body,
        protos,
        target_dialect: Some(target.version),
        next_synthetic_local: next_synthetic,
    })
}

fn attach_child_bodies(
    block: &mut AstBlock,
    bodies: &[AstBlock],
    protos: &[AstProtoMeta],
    supports_named_vararg: bool,
) {
    for stmt in &mut block.stmts {
        attach_child_bodies_stmt(stmt, bodies, protos, supports_named_vararg);
    }
}

fn attach_child_bodies_stmt(
    stmt: &mut AstStmt,
    bodies: &[AstBlock],
    protos: &[AstProtoMeta],
    supports_named_vararg: bool,
) {
    use super::traverse::{
        traverse_call_children, traverse_lvalue_children, traverse_stmt_children,
    };
    traverse_stmt_children!(
        stmt,
        iter = iter_mut,
        opt = as_mut,
        borrow = [&mut],
        expr(expr) => { attach_child_bodies_expr(expr, bodies, protos, supports_named_vararg); },
        lvalue(lv) => {
            traverse_lvalue_children!(lv, borrow = [&mut], expr(e) => {
                attach_child_bodies_expr(e, bodies, protos, supports_named_vararg);
            });
        },
        block(b) => { attach_child_bodies(b, bodies, protos, supports_named_vararg); },
        function(func) => {
            if let Some(child_body) = bodies.get(func.function.index()) {
                func.body = child_body.clone();
            }
            if supports_named_vararg
                && let Some(meta) = protos.get(func.function.index())
                && meta.signature.has_vararg_param_reg
                && (meta.signature.named_vararg_table
                    || meta
                        .vararg_param_local
                        .is_some_and(|l| block_mentions_local(&func.body, l)))
            {
                func.named_vararg = meta.vararg_param_local.map(AstBindingRef::Local);
            }
        },
        condition(cond) => { attach_child_bodies_expr(cond, bodies, protos, supports_named_vararg); },
        call(call) => {
            traverse_call_children!(call, iter = iter_mut, borrow = [&mut], expr(e) => {
                attach_child_bodies_expr(e, bodies, protos, supports_named_vararg);
            });
        }
    );
}

fn attach_child_bodies_expr(
    expr: &mut AstExpr,
    bodies: &[AstBlock],
    protos: &[AstProtoMeta],
    supports_named_vararg: bool,
) {
    use super::traverse::traverse_expr_children;
    traverse_expr_children!(
        expr,
        iter = iter_mut,
        borrow = [&mut],
        expr(child) => { attach_child_bodies_expr(child, bodies, protos, supports_named_vararg); },
        function(func) => {
            if let Some(child_body) = bodies.get(func.function.index()) {
                func.body = child_body.clone();
            }
            if supports_named_vararg
                && let Some(meta) = protos.get(func.function.index())
                && meta.signature.has_vararg_param_reg
                && (meta.signature.named_vararg_table
                    || meta
                        .vararg_param_local
                        .is_some_and(|l| block_mentions_local(&func.body, l)))
            {
                func.named_vararg = meta.vararg_param_local.map(AstBindingRef::Local);
            }
        }
    );
}

/// 检查 `block` 及其内嵌语句/表达式（不进入子函数自身遮蔽，但包含子闭包对父绑定的捕获）是否引用了指定 `LocalId`。
fn block_mentions_local(block: &AstBlock, target: LocalId) -> bool {
    let target_ref = AstNameRef::Local(target);
    let target_binding = AstBindingRef::Local(target);
    block.stmts.iter().any(|s| stmt_mentions_local(s, &target_ref, target_binding))
}

fn stmt_mentions_local(stmt: &AstStmt, target: &AstNameRef, target_binding: AstBindingRef) -> bool {
    use super::traverse::traverse_lvalue_children;
    match stmt {
        AstStmt::LocalDecl(d) => d
            .values
            .iter()
            .any(|v| expr_mentions_local_or_capture(v, target, target_binding)),
        AstStmt::GlobalDecl(d) => d
            .values
            .iter()
            .any(|v| expr_mentions_local_or_capture(v, target, target_binding)),
        AstStmt::Assign(a) => {
            a.targets.iter().any(|t| {
                let mut found = matches!(t, AstLValue::Name(n) if n == target);
                traverse_lvalue_children!(t, borrow = [&], expr(e) => {
                    if expr_mentions_local_or_capture(e, target, target_binding) {
                        found = true;
                    }
                });
                found
            }) || a
                .values
                .iter()
                .any(|v| expr_mentions_local_or_capture(v, target, target_binding))
        }
        AstStmt::CallStmt(c) => match &c.call {
            super::common::AstCallKind::Call(call) => {
                expr_mentions_local_or_capture(&call.callee, target, target_binding)
                    || call
                        .args
                        .iter()
                        .any(|a| expr_mentions_local_or_capture(a, target, target_binding))
            }
            super::common::AstCallKind::MethodCall(m) => {
                expr_mentions_local_or_capture(&m.receiver, target, target_binding)
                    || m.args
                        .iter()
                        .any(|a| expr_mentions_local_or_capture(a, target, target_binding))
            }
        },
        AstStmt::Return(r) => r
            .values
            .iter()
            .any(|v| expr_mentions_local_or_capture(v, target, target_binding)),
        AstStmt::If(i) => {
            expr_mentions_local_or_capture(&i.cond, target, target_binding)
                || block_mentions_local(&i.then_block, match target_binding {
                    AstBindingRef::Local(l) => l,
                    _ => unreachable!(),
                })
                || i.else_block.as_ref().is_some_and(|eb| {
                    block_mentions_local(eb, match target_binding {
                        AstBindingRef::Local(l) => l,
                        _ => unreachable!(),
                    })
                })
        }
        AstStmt::While(w) => {
            expr_mentions_local_or_capture(&w.cond, target, target_binding)
                || block_mentions_local(&w.body, match target_binding {
                    AstBindingRef::Local(l) => l,
                    _ => unreachable!(),
                })
        }
        AstStmt::Repeat(r) => {
            block_mentions_local(&r.body, match target_binding {
                AstBindingRef::Local(l) => l,
                _ => unreachable!(),
            }) || expr_mentions_local_or_capture(&r.cond, target, target_binding)
        }
        AstStmt::NumericFor(nf) => {
            expr_mentions_local_or_capture(&nf.start, target, target_binding)
                || expr_mentions_local_or_capture(&nf.limit, target, target_binding)
                || expr_mentions_local_or_capture(&nf.step, target, target_binding)
                || block_mentions_local(&nf.body, match target_binding {
                    AstBindingRef::Local(l) => l,
                    _ => unreachable!(),
                })
        }
        AstStmt::GenericFor(gf) => {
            gf.iterator
                .iter()
                .any(|e| expr_mentions_local_or_capture(e, target, target_binding))
                || block_mentions_local(&gf.body, match target_binding {
                    AstBindingRef::Local(l) => l,
                    _ => unreachable!(),
                })
        }
        AstStmt::DoBlock(b) => block_mentions_local(b, match target_binding {
            AstBindingRef::Local(l) => l,
            _ => unreachable!(),
        }),
        AstStmt::FunctionDecl(d) => d.func.captured_bindings.contains(&target_binding),
        AstStmt::LocalFunctionDecl(d) => d.func.captured_bindings.contains(&target_binding),
        _ => false,
    }
}

fn expr_mentions_local_or_capture(
    expr: &AstExpr,
    target: &AstNameRef,
    target_binding: AstBindingRef,
) -> bool {
    if expr_mentions_name(expr, target) {
        return true;
    }
    for node in super::visit::expr_nodes(expr) {
        if let super::visit::ExprNode::Function(func) = node
            && func.captured_bindings.contains(&target_binding)
        {
            return true;
        }
    }
    false
}

/// Lua 5.5 `ERRNNIL` 紧随的待配对 `global name = expr` 上下文。
#[derive(Debug, Clone)]
pub(super) struct PendingGlobalInit {
    pub name: String,
    /// 若探针 `GetTable` 读取自当前函数的局部 `_ENV` 寄存器，记录 `(env_reg, env_local)`。
    pub local_env: Option<(Reg, LocalId)>,
}

/// Luau `ClosureCreation::Reusable`（`DUPCLOSURE`）的提升策略。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SharedClosureHoistKind {
    /// 全部捕获均为 upvalue 或静态非 NaN 单定义局部/已提升闭包：直接提升为共享局部函数 `local function s() ... end`，引用为 `s`。
    Direct,
    /// 含动态不可判 NaN 的单定义局部捕获（如 `_G` 或运行期结果）：提升为词法工厂 `local function make_s() return function() ... end end`，引用为 `make_s()`，
    /// 既在非 NaN 时共享同一闭包身份，又在 NaN 时遵循 Luau VM `DUPCLOSURE` 语义分配新闭包。
    FactoryWrapper,
}

#[derive(Debug, Clone)]
pub(super) struct SharedClosurePlan {
    pub local: LocalId,
    pub kind: SharedClosureHoistKind,
    /// 若某捕获槽位经由已直接提升的共享闭包传导而来（如 `s11 -> s12`），记录对应的共享 `LocalId`。
    pub hoisted_cap_locals: BTreeMap<usize, LocalId>,
}

#[derive(Debug, Clone)]
pub(super) struct HoistedSharedClosure {
    pub local: LocalId,
    pub func: AstFunctionExpr,
    pub dep_locals: BTreeSet<LocalId>,
}

/// 单个 proto 的提升上下文。
pub(super) struct ProtoLifter<'a> {
    pub(super) proto_id: ProtoId,
    pub(super) proto: &'a LoweredProto,
    pub(super) analysis: &'a ProtoAnalysis,
    pub(super) target: AstTargetDialect,
    pub(super) next_synthetic: &'a mut usize,
    proto_registry: &'a mut ProtoRegistry,

    /// 每个 SSA `ValueId` 所属的 Web 根编号（Union-Find 压缩结果）。
    /// 同一个物理寄存器在不重叠的生命周期（且非 pinned/Phi/同 debug local/自更新）时
    /// 拆分为独立 Web，避免伪造复用阻断 `local a, b = f()` 合并与引发重编译膨胀。
    pub(super) value_web: Vec<usize>,
    /// 每个 SSA `ValueId` 若属于某个 `NumericFor`/`GenericFor` 的循环控制变量，则记录该循环的 `body_entry`，
    /// 确保循环变量绝不与循环外复用同一物理寄存器的变量混并或别名到外层 `slot_locals`。
    pub(super) for_binding_owners: Vec<Option<BlockId>>,
    /// 每个 Web 根对应的精确源码 debug 名字提示（按实际覆盖该 Web 定义 PC 的 DebugLocal 选取）。
    pub(super) web_debug_hints: BTreeMap<usize, String>,
    /// Web 根 -> 已分配的 `LocalId`（形参槽位优先映射为 `ParamId`）。
    pub(super) web_locals: BTreeMap<usize, LocalId>,
    /// 兜底：无精确 SSA ValueId 时按槽位 `(Reg, epoch)` -> `LocalId`。
    pub(super) slot_locals: BTreeMap<SlotKey, LocalId>,
    pub(super) local_debug_hints: Vec<Option<String>>,
    /// 每个 `LocalId` 对应的物理槽位 `(Reg, epoch)`，用于精确匹配 `Close(Explicit)` 的作用域边界。
    pub(super) local_slots: Vec<Option<SlotKey>>,
    /// 嵌套 `lift_region_with_scope` 调用栈中最近一次由 `Close(Explicit)` 包装出的 `DoBlock` 时的语句长度。
    pub(super) block_last_close_len: Vec<Option<usize>>,
    pub(super) tbc_locals: BTreeSet<LocalId>,
    /// 实际被本函数内子闭包按引用（`ByReference`）捕获的精确 `LocalId` 集合，
    /// 避免同 `(Reg, epoch)` 上已离域的未捕获局部被 `wrap_explicit_close_scope` 误卷入后续 `do ... end`。
    pub(super) ref_captured_locals: BTreeSet<LocalId>,
    pub(super) debug_hinted_locals: BTreeSet<LocalId>,
    pub(super) vararg_param_local: Option<LocalId>,
    pub(super) lexical_environment_local: Option<LocalId>,
    /// 哪些 SSA ValueId 必须物化为具名变量（跨块、多用、pinned 等）。
    pub(super) materialized_values: BTreeSet<ValueId>,
    /// 当前基本块内的顺序消费表达式栈（核心无中转变量引擎）。
    pub(in crate::ast::lift) pending: Vec<PendingExpr>,
    /// 单调递增求值序号（用于还原交错表构造器 `{ [k]=v, a, tag=b, c }` 的精确求值顺序）。
    pub(super) next_eval_order: usize,
    /// NumericFor / GenericFor 控制变量预分配的独立 LocalId。
    pub(super) for_bindings: BTreeMap<(InstrRef, Reg), LocalId>,
    /// Lua 5.5 `ERRNNIL` 紧随的待配对 `global name = expr` 声明上下文（避免把探针 `GETTABUP`/`GETTABLE` 误冲刷成多余局部读取）。
    pub(super) pending_global_init: Option<PendingGlobalInit>,
    /// 本 proto 控制流 Region 树中每个 `Region::Goto(lbl)` 出现的总次数，用于防止 `wrap_explicit_close_scope`
    /// 把仍被后续 `goto` 指向的标签提前封进内层 `do ... end` 导致跨块不可见。
    pub(super) total_gotos_by_label: BTreeMap<usize, usize>,
    /// Luau `ClosureCreation::Reusable`（`DUPCLOSURE`）提升计划：`(child_proto_idx, shared_slot) -> plan`。
    pub(super) shared_reusable_closures: BTreeMap<(usize, SharedClosureRef), SharedClosurePlan>,
    /// 仅作为其他已提升共享闭包捕获源的直接提升闭包指令（免发射无用副本赋值，仍确保按依赖序物化目标函数）。
    pub(super) skipped_hoisted_closure_defs: BTreeSet<InstrRef>,
    /// 已构造的待按依赖顺序插入函数体的共享 `DUPCLOSURE` 局部函数列表。
    pub(super) hoisted_shared_closures: Vec<HoistedSharedClosure>,
    pub(super) hoisted_shared_emitted: BTreeSet<(usize, SharedClosureRef)>,
    /// Luau `ClosureCreation::Fresh` 捕获的单定义字面量局部集合，须补 `if false then x = nil end` 防常量传播破坏闭包新鲜性。
    pub(super) luau_fresh_const_capture_locals: BTreeSet<LocalId>,
    /// 按准备块索引的 `GenericFor` 协议下标，避免 `plan_materialized_values` 对每个 SSA 值线性扫描全部循环。
    generic_for_by_setup_block: BTreeMap<BlockId, Vec<usize>>,
}

impl<'a> ProtoLifter<'a> {
    fn new(
        proto_id: ProtoId,
        proto: &'a LoweredProto,
        analysis: &'a ProtoAnalysis,
        target: AstTargetDialect,
        next_synthetic: &'a mut usize,
        proto_registry: &'a mut ProtoRegistry,
    ) -> Self {
        let mut generic_for_by_setup_block: BTreeMap<BlockId, Vec<usize>> = BTreeMap::new();
        for (idx, hint) in analysis.cfg.loop_protocols.iter().enumerate() {
            let crate::analysis::LoopProtocolHint::GenericFor {
                prep_block,
                header_block,
                ..
            } = hint
            else {
                continue;
            };
            if let Some(pb) = *prep_block {
                generic_for_by_setup_block.entry(pb).or_default().push(idx);
            } else {
                generic_for_by_setup_block
                    .entry(*header_block)
                    .or_default()
                    .push(idx);
                for pred in analysis.cfg.pred_blocks(*header_block) {
                    if analysis.graph.dominates(pred, *header_block)
                        && matches!(
                            analysis.cfg.succs[pred.index()].as_slice(),
                            [eid] if analysis.cfg.edges[eid.index()].to == *header_block
                        )
                    {
                        generic_for_by_setup_block.entry(pred).or_default().push(idx);
                    }
                }
            }
        }

        let mut lifter = Self {
            proto_id,
            proto,
            analysis,
            target,
            next_synthetic,
            proto_registry,
            value_web: Vec::new(),
            for_binding_owners: Vec::new(),
            web_debug_hints: BTreeMap::new(),
            web_locals: BTreeMap::new(),
            slot_locals: BTreeMap::new(),
            local_debug_hints: Vec::new(),
            local_slots: Vec::new(),
            block_last_close_len: Vec::new(),
            tbc_locals: BTreeSet::new(),
            ref_captured_locals: BTreeSet::new(),
            debug_hinted_locals: BTreeSet::new(),
            vararg_param_local: None,
            lexical_environment_local: None,
            materialized_values: BTreeSet::new(),
            pending: Vec::new(),
            next_eval_order: 0,
            for_bindings: BTreeMap::new(),
            pending_global_init: None,
            total_gotos_by_label: BTreeMap::new(),
            shared_reusable_closures: BTreeMap::new(),
            skipped_hoisted_closure_defs: BTreeSet::new(),
            hoisted_shared_closures: Vec::new(),
            hoisted_shared_emitted: BTreeSet::new(),
            luau_fresh_const_capture_locals: BTreeSet::new(),
            generic_for_by_setup_block,
        };

        // 先预标记必须物化的 SSA 值（pinned / Phi / 跨块读 / 多次使用），再构建 SSA Web，
        // 使 Web 上限保护仅统计真正会物化为局部变量的 Web，避免中等函数被误按物理寄存器混并。
        lifter.plan_materialized_values();
        let (value_web, web_debug_hints, for_binding_owners) =
            build_ssa_webs(proto, analysis, &mut lifter.materialized_values);
        lifter.value_web = value_web;
        lifter.web_debug_hints = web_debug_hints;
        lifter.for_binding_owners = for_binding_owners;

        // 识别需要提升为共享局部或词法工厂的 `ClosureCreation::Reusable`（Luau `DUPCLOSURE`）
        lifter.plan_shared_reusable_closures();

        // 入口变参表局部（Lua 5.1 `arg` / Lua 5.5 具名 vararg）
        if let Some((vr, vval)) = analysis.ssa.vararg_param_value {
            let slot = SlotKey { reg: vr, epoch: 0 };
            let local = lifter.alloc_local_for_value(vval, slot, None);
            lifter.vararg_param_local = Some(local);
        }

        lifter
    }

    fn plan_materialized_values(&mut self) {
        let ssa = &self.analysis.ssa;
        for (vi, def) in ssa.defs.iter().enumerate() {
            let val = ValueId(vi);
            match *def {
                SsaDef::Param { .. } | SsaDef::VarArgParam { .. } | SsaDef::Undef { .. } => {}
                SsaDef::Phi { .. } => {
                    self.materialized_values.insert(val);
                }
                SsaDef::Instr {
                    instr,
                    block,
                    slot,
                    ..
                } => {
                    if ssa.pinned_values.contains(&val) {
                        self.materialized_values.insert(val);
                        continue;
                    }
                    // 多结果指令（Call/VarArg 等）默认物化为多赋值左值；
                    // 但 `LoadNil` 是多个独立的纯 nil 加载（常用于表构造器 `{ nil, nil, "tail" }` 或实参），
                    // 不按多结果调用强制物化。
                    if ssa.instr_defs[instr.index()].len() > 1
                        && !matches!(self.proto.instrs[instr.index()], LowInstr::LoadNil(_))
                    {
                        self.materialized_values.insert(val);
                        continue;
                    }
                    let new_table_alloc = match &self.proto.instrs[instr.index()] {
                        LowInstr::NewTable(nt) => Some(&nt.allocation),
                        _ => None,
                    };
                    let is_new_table = new_table_alloc.is_some();
                    let accepts_set_table = new_table_alloc.is_some_and(table_accepts_set_table);
                    let uses = &ssa.uses[vi];

                    // 对于 `NumericFor` 头准备的 `start/limit/step` 槽位，`NumericForLoop` 读的是 VM 隐藏控制槽，
                    // 不算源码级的二次消费或跨块使用，避免把 `for i = 1, 10 do` 拆成 3 个多余 `local`。
                    let is_only_numeric_for_bound = uses.iter().any(|u| {
                        matches!(
                            *u,
                            UseSite::Instr { block: ub, instr: ui }
                                if ub == block && matches!(self.proto.instrs[ui.index()], LowInstr::NumericForInit(_))
                        )
                    }) && uses.iter().all(|u| {
                        matches!(
                            *u,
                            UseSite::Instr { instr: ui, .. }
                                if matches!(
                                    self.proto.instrs[ui.index()],
                                    LowInstr::NumericForInit(_) | LowInstr::NumericForLoop(_)
                                )
                        )
                    });

                    // 对于 `GenericFor` 在 `prep_block`（或同块 `header_block`）内准备的迭代初值槽
                    // (`iterator / state / control / closing`)，其后续在 `header_block` 的 `GenericForCall`
                    // 或控制槽 Phi 读取属于 VM 协议消费，允许保留在 `pending` 栈直接内联进 `for ... in ... do`，
                    // 避免每轮重编译为 `for k, v in a, b, c do` 复制 3 个多余 `local`！
                    let is_only_generic_for_iter = !uses.is_empty()
                        && self.is_only_generic_for_iter_setup(
                            block,
                            slot.reg,
                            is_new_table,
                            accepts_set_table,
                            uses,
                        );

                    // `SELF` 协议将 `obj:m(...)` 拆成 `self_arg = obj; callee = GetTable(self_arg, "m", Method); Call(callee, self_arg, ...)`：
                    // `self_arg` 在同块内被 `GetTable(Method)` 和 `Call(Method)` 各读一次，本质仅是一次接收者求值，不应强制物化为临时局部！
                    let is_method_self_pair = uses.len() == 2
                        && uses.iter().any(|u| {
                            matches!(
                                *u,
                                UseSite::Instr { block: ub, instr: ui }
                                    if ub == block
                                        && matches!(
                                            &self.proto.instrs[ui.index()],
                                            LowInstr::GetTable(gt)
                                                if gt.kind == crate::transformer::GetTableKind::Method
                                                    && gt.base == crate::transformer::AccessBase::Reg(slot.reg)
                                        )
                            )
                        })
                        && uses.iter().any(|u| {
                            matches!(
                                *u,
                                UseSite::Instr { block: ub, instr: ui }
                                    if ub == block
                                        && matches!(
                                            &self.proto.instrs[ui.index()],
                                            LowInstr::Call(c) if c.kind == crate::transformer::CallKind::Method
                                        )
                                        || (ub == block
                                            && matches!(
                                                &self.proto.instrs[ui.index()],
                                                LowInstr::TailCall(tc) if tc.kind == crate::transformer::CallKind::Method
                                            ))
                            )
                        });

                    if is_only_generic_for_iter {
                        continue;
                    }

                    // 对于 NewTable，同块内 `SetList` 封口之前且表允许吸收 SetTable 时的构造写不算外部实质使用；
                    // 一旦经历 `SetList` 封口（或空 PUC 表不吸收 SetTable），后续 `SetTable` 计入实质使用。
                    let mut effective_use_count = 0usize;
                    let mut cross_block = false;
                    let mut single_use_block: Option<BlockId> = None;
                    let mut table_sealed = false;
                    let mut last_table_init_instr = instr;
                    let mut ordered_uses: Vec<UseSite> = uses.clone();
                    if is_new_table {
                        ordered_uses.sort_by_key(|u| match *u {
                            UseSite::Instr { instr: ui, .. } => ui.index(),
                            UseSite::Phi { .. } => usize::MAX,
                        });
                    }
                    for u in &ordered_uses {
                        match *u {
                            UseSite::Phi { .. } => {
                                cross_block = true;
                                effective_use_count += 1;
                            }
                            UseSite::Instr {
                                block: ub,
                                instr: ui,
                            } => {
                                if is_only_numeric_for_bound
                                    && matches!(
                                        self.proto.instrs[ui.index()],
                                        LowInstr::NumericForLoop(_)
                                    )
                                {
                                    continue;
                                }
                                if is_method_self_pair
                                    && matches!(
                                        &self.proto.instrs[ui.index()],
                                        LowInstr::GetTable(gt)
                                            if gt.kind == crate::transformer::GetTableKind::Method
                                                && gt.base == crate::transformer::AccessBase::Reg(slot.reg)
                                    )
                                {
                                    continue;
                                }
                                if ub != block {
                                    cross_block = true;
                                    effective_use_count += 1;
                                    single_use_block = Some(ub);
                                    continue;
                                }
                                let ureg = slot.reg;
                                let is_set_list_init = is_new_table
                                    && matches!(
                                        &self.proto.instrs[ui.index()],
                                        LowInstr::SetList(sl) if sl.base == ureg
                                    );
                                if is_set_list_init {
                                    table_sealed = true;
                                    last_table_init_instr = ui;
                                    continue;
                                }
                                let is_set_table_init = is_new_table
                                    && accepts_set_table
                                    && !table_sealed
                                    && matches!(
                                        &self.proto.instrs[ui.index()],
                                        LowInstr::SetTable(st)
                                            if st.base == crate::transformer::AccessBase::Reg(ureg)
                                                && !matches!(
                                                    st.key,
                                                    crate::transformer::AccessKey::Reg(r) if r == ureg
                                                )
                                                && !matches!(
                                                    st.value,
                                                    crate::transformer::ValueOperand::Reg(r) if r == ureg
                                                )
                                    );
                                if is_set_table_init {
                                    last_table_init_instr = ui;
                                } else {
                                    effective_use_count += 1;
                                    single_use_block = Some(ub);
                                }
                            }
                        }
                    }

                    // 只有当该定值不是“同块内立刻被覆写进同一槽位的中间求值步骤”
                    // 且该寄存器在当前指令（或表构造器最后一条初始化写）之后的原始 PC 上确实进入源码 debug 作用域时，
                    // 才因 debug 提示强制物化；若该指令恰好是某个源码 `DebugLocal` 的声明起点（如 `local previous = nil`
                    // 随后未直接读取，但 `debug.getlocal` 可观测），同样保留物化（stripped 模式下 `debug_locals` 为空，零额外开销）。
                    let is_active_debug_local =
                        self.analysis.dataflow.debug_slot_hints.contains_key(&slot)
                            && !is_only_numeric_for_bound
                            && !self.is_same_block_self_overwrite_step(instr, block, slot, uses)
                            && ((effective_use_count > 0
                                && (self.debug_local_active_after_instr(instr, slot.reg)
                                    || self.debug_local_active_after_instr(
                                        last_table_init_instr,
                                        slot.reg,
                                    )))
                                || self.debug_local_starts_after_instr(instr, slot.reg)
                                || self.debug_local_starts_after_instr(
                                    last_table_init_instr,
                                    slot.reg,
                                ));
                    if is_active_debug_local {
                        self.materialized_values.insert(val);
                        continue;
                    }
                    if cross_block {
                        let control_equiv_single_use = effective_use_count == 1
                            && uses.iter().all(|u| matches!(u, UseSite::Instr { .. }))
                            && single_use_block.is_some_and(|ub| {
                                self.analysis.graph.dominates(block, ub)
                                    && self.analysis.graph.postdominates(ub, block)
                            });
                        if !control_equiv_single_use {
                            self.materialized_values.insert(val);
                            continue;
                        }
                    }
                    // 任何被实质使用 >= 2 次的值（包含字符串/数字字面量，防止第一次弹出消耗后后续读取变成 nil）都必须物化。
                    if effective_use_count >= 2 {
                        self.materialized_values.insert(val);
                    }
                }
            }
        }
    }

    fn is_only_generic_for_iter_setup(
        &self,
        def_block: BlockId,
        def_reg: Reg,
        is_new_table: bool,
        accepts_set_table: bool,
        uses: &[UseSite],
    ) -> bool {
        let Some(indices) = self.generic_for_by_setup_block.get(&def_block) else {
            return false;
        };
        let ssa = &self.analysis.ssa;
        let cfg = &self.analysis.cfg;
        for &idx in indices {
            let crate::analysis::LoopProtocolHint::GenericFor {
                header_block,
                call_instr,
                ..
            } = &cfg.loop_protocols[idx]
            else {
                continue;
            };
            let mut has_for_use = false;
            let mut table_sealed = false;
            let mut ordered: Vec<UseSite> = uses.to_vec();
            if is_new_table {
                ordered.sort_by_key(|u| match *u {
                    UseSite::Instr { instr: ui, .. } => ui.index(),
                    UseSite::Phi { .. } => usize::MAX,
                });
            }
            let all_for_setup = ordered.iter().all(|u| match *u {
                UseSite::Instr { block: ub, instr: ui } => {
                    if ub == def_block && is_new_table {
                        match &self.proto.instrs[ui.index()] {
                            LowInstr::SetList(sl) if sl.base == def_reg => {
                                table_sealed = true;
                                return true;
                            }
                            LowInstr::SetTable(st)
                                if !table_sealed
                                    && accepts_set_table
                                    && st.base == crate::transformer::AccessBase::Reg(def_reg) =>
                            {
                                return true;
                            }
                            _ => {}
                        }
                    }
                    let is_for = (ub == def_block || ub == *header_block)
                        && matches!(
                            self.proto.instrs[ui.index()],
                            LowInstr::GenericForPrep(_)
                                | LowInstr::GenericForCall(_)
                                | LowInstr::GenericForLoop(_)
                        );
                    if is_for {
                        has_for_use = true;
                    }
                    is_for
                }
                UseSite::Phi { phi: pid, .. } => {
                    let phi = &ssa.phis[pid.index()];
                    let ok = phi.block == *header_block
                        && ssa.uses[phi.value.index()].iter().all(|pu| {
                            matches!(*pu, UseSite::Instr { instr: ui, .. } if ui == *call_instr)
                        });
                    if ok {
                        has_for_use = true;
                    }
                    ok
                }
            });
            if all_for_setup && has_for_use {
                return true;
            }
        }
        false
    }

    /// 判断某个单用 SSA 值是否只是“同块内下一条链式求值立刻覆写同一寄存器”的临时步骤
    /// （例如 `r0 = debug; r0 = r0.getlocal` 中的第一步），这类步骤不应因 debug 名被提前拆断。
    fn is_same_block_self_overwrite_step(
        &self,
        def_instr: InstrRef,
        block: BlockId,
        slot: SlotKey,
        uses: &[UseSite],
    ) -> bool {
        let [UseSite::Instr {
            block: ub,
            instr: ui,
            ..
        }] = uses
        else {
            return false;
        };
        if *ub != block || *ui == def_instr {
            return false;
        }
        self.analysis.ssa.instr_defs[ui.index()]
            .iter()
            .any(|(r, _)| *r == slot.reg)
    }

    fn debug_local_active_after_instr(&self, instr: InstrRef, reg: Reg) -> bool {
        let Some(next_pc) = after_instr_pc(self.proto, self.analysis, instr) else {
            return false;
        };
        self.proto
            .debug_locals
            .iter()
            .any(|l| l.is_source() && l.reg == reg && l.start_pc <= next_pc && next_pc < l.end_pc)
    }

    fn tbc_debug_hint_at(&self, tbc_iref: InstrRef, reg: Reg) -> Option<String> {
        let next_pc = after_instr_pc(self.proto, self.analysis, tbc_iref);
        let cur_pc = self
            .proto
            .lowering_map
            .pc_map()
            .get(tbc_iref.index())
            .and_then(|pcs| pcs.iter().min().copied());
        for pc in next_pc.into_iter().chain(cur_pc) {
            if let Some(local) = self
                .proto
                .debug_locals
                .iter()
                .find(|l| l.is_source() && l.reg == reg && l.start_pc <= pc && pc < l.end_pc)
                && let Ok(name) = std::str::from_utf8(&local.name.bytes)
            {
                return Some(name.to_owned());
            }
        }
        None
    }

    fn debug_local_starts_after_instr(&self, instr: InstrRef, reg: Reg) -> bool {
        let Some(next_pc) = after_instr_pc(self.proto, self.analysis, instr) else {
            return false;
        };
        // Luau 编译多变量无初值声明 `local a, b, c` 时会发出多条连续 `LOADNIL`，但把三者的
        // `debug_local.start_pc` 统一记在最后一条 `LOADNIL` 之后；向前跨过同块连续 `LoadNil`
        // 统一匹配，防止重编译时每轮逐个剥离产生 1-per-round 收敛漂移！
        let mut max_next_pc = next_pc;
        if matches!(self.proto.instrs[instr.index()], LowInstr::LoadNil(_))
            && let Some(block) = self.analysis.cfg.block_of_instr[instr.index()]
        {
            let range = self.analysis.cfg.blocks[block.index()].instrs;
            let mut cursor = instr.index() + 1;
            while cursor < range.end()
                && matches!(self.proto.instrs[cursor], LowInstr::LoadNil(_))
            {
                if let Some(pc) = after_instr_pc(self.proto, self.analysis, InstrRef(cursor)) {
                    max_next_pc = max_next_pc.max(pc);
                }
                cursor += 1;
            }
        }
        let is_call = matches!(self.proto.instrs[instr.index()], LowInstr::Call(_));
        self.proto.debug_locals.iter().any(|l| {
            l.is_source()
                && l.reg == reg
                && l.start_pc >= next_pc
                && l.start_pc <= max_next_pc
                && (l.start_pc < l.end_pc || (is_call && l.start_pc == next_pc && l.start_pc == l.end_pc))
        })
    }

    fn plan_shared_reusable_closures(&mut self) {
        let mut loop_blocks = BTreeSet::new();
        for nl in &self.analysis.graph.natural_loops {
            loop_blocks.extend(nl.blocks.iter().copied());
        }
        for hint in &self.analysis.cfg.loop_protocols {
            match hint {
                crate::analysis::LoopProtocolHint::NumericFor {
                    body_entry,
                    latch_blocks,
                    ..
                } => {
                    loop_blocks.insert(*body_entry);
                    loop_blocks.extend(latch_blocks.iter().copied());
                }
                crate::analysis::LoopProtocolHint::GenericFor {
                    header_block,
                    body_entry,
                    ..
                } => {
                    loop_blocks.insert(*header_block);
                    loop_blocks.insert(*body_entry);
                }
            }
        }

        // 按 `(child_proto_idx, shared_slot)` 分组收集所有 `ClosureCreation::Reusable` 指令点
        let mut groups: BTreeMap<(usize, SharedClosureRef), Vec<InstrRef>> = BTreeMap::new();
        for (idx, instr) in self.proto.instrs.iter().enumerate() {
            if let LowInstr::Closure(c) = instr
                && let ClosureCreation::Reusable(shared) = c.creation
            {
                groups
                    .entry((c.proto.index(), shared))
                    .or_default()
                    .push(InstrRef(idx));
            }
        }
        if groups.is_empty() {
            return;
        }

        #[derive(Clone, PartialEq, Eq)]
        enum CapSummary {
            Upvalue(usize),
            HoistedDirect(LocalId),
            ImmutableNonNan(ValueId),
            ImmutableDynamic(ValueId),
        }

        let ssa = &self.analysis.ssa;
        let graph = &self.analysis.graph;
        let classify_val_nan = |val: ValueId| -> Option<bool> {
            match ssa.def_of(val) {
                SsaDef::Instr { instr, .. } => match &self.proto.instrs[instr.index()] {
                    LowInstr::LoadNumber(n) => Some(!n.value.is_nan()),
                    LowInstr::LoadConst(lc) => match self.proto.constants.get(lc.value.index()) {
                        Some(RawLiteralConst::Number(n)) => Some(!n.is_nan()),
                        Some(_) => Some(true),
                        None => None,
                    },
                    LowInstr::LoadNil(_)
                    | LowInstr::LoadBool(_)
                    | LowInstr::LoadInteger(_)
                    | LowInstr::NewTable(_)
                    | LowInstr::Closure(_) => Some(true),
                    _ => None,
                },
                SsaDef::Param { .. } | SsaDef::VarArgParam { .. } => None,
                SsaDef::Phi { .. } | SsaDef::Undef { .. } => None,
            }
        };

        // 迭代不动点解析可提升共享闭包（支持 `s6 -> s7`、`s11 -> s12` 传递依赖链）
        let mut progressed = true;
        while progressed {
            progressed = false;
            for (&key, sites) in &groups {
                if self.shared_reusable_closures.contains_key(&key) {
                    continue;
                }
                let in_loop = sites.iter().any(|&iref| {
                    self.analysis.cfg.block_of_instr[iref.index()]
                        .is_some_and(|b| loop_blocks.contains(&b))
                });
                let LowInstr::Closure(first_c) = &self.proto.instrs[sites[0].index()] else {
                    continue;
                };
                let has_caps = !first_c.captures.is_empty();
                let should_hoist = sites.len() >= 2 || (in_loop && has_caps);
                if !should_hoist {
                    continue;
                }

                // 检查全部站点是否共享完全一致的不可变捕获集合，并按 NaN 语义分类为 Direct 或 FactoryWrapper
                let mut canonical_caps: Option<Vec<CapSummary>> = None;
                let mut all_valid = true;
                for &iref in sites {
                    let LowInstr::Closure(c) = &self.proto.instrs[iref.index()] else {
                        all_valid = false;
                        break;
                    };
                    let Some(site_block) = self.analysis.cfg.block_of_instr[iref.index()] else {
                        all_valid = false;
                        break;
                    };
                    let mut cur_caps = Vec::with_capacity(c.captures.len());
                    for cap in &c.captures {
                        match cap.source {
                            CaptureSource::Upvalue(u) => {
                                cur_caps.push(CapSummary::Upvalue(u.index()));
                            }
                            CaptureSource::ByValue(reg) if reg != c.dst => {
                                let Some(val) = ssa.instr_use_value(iref, reg) else {
                                    all_valid = false;
                                    break;
                                };
                                // 情形 1：捕获源本身是已直接提升的共享闭包（允许各站点经由不同寄存器名中转）
                                if let SsaDef::Instr {
                                    instr: def_iref, ..
                                } = ssa.def_of(val)
                                    && let LowInstr::Closure(dep_c) =
                                        &self.proto.instrs[def_iref.index()]
                                    && let ClosureCreation::Reusable(dep_slot) = dep_c.creation
                                    && let Some(dep_plan) = self
                                        .shared_reusable_closures
                                        .get(&(dep_c.proto.index(), dep_slot))
                                    && dep_plan.kind == SharedClosureHoistKind::Direct
                                {
                                    cur_caps.push(CapSummary::HoistedDirect(dep_plan.local));
                                    continue;
                                }
                                // 情形 2：捕获源为支配所有站点的非循环单定义不可变值（形参或单定义指令）
                                let def_dominates_all = match ssa.def_of(val) {
                                    SsaDef::Param { .. } | SsaDef::VarArgParam { .. } => true,
                                    SsaDef::Instr {
                                        block: def_block, ..
                                    } => {
                                        !loop_blocks.contains(&def_block)
                                            && graph.dominates(def_block, site_block)
                                    }
                                    SsaDef::Phi { .. } | SsaDef::Undef { .. } => false,
                                };
                                if !def_dominates_all {
                                    all_valid = false;
                                    break;
                                }
                                match classify_val_nan(val) {
                                    // 静态确定为 NaN（如 `0/0`）：Luau VM `DUPCLOSURE` 必分配新闭包，严禁提升共享！
                                    Some(false) => {
                                        all_valid = false;
                                        break;
                                    }
                                    Some(true) => {
                                        cur_caps.push(CapSummary::ImmutableNonNan(val));
                                    }
                                    None => {
                                        cur_caps.push(CapSummary::ImmutableDynamic(val));
                                    }
                                }
                            }
                            _ => {
                                all_valid = false;
                                break;
                            }
                        }
                    }
                    if !all_valid {
                        break;
                    }
                    match &canonical_caps {
                        None => canonical_caps = Some(cur_caps),
                        Some(prev) if prev == &cur_caps => {}
                        Some(_) => {
                            all_valid = false;
                            break;
                        }
                    }
                }

                if !all_valid {
                    continue;
                }
                let caps = canonical_caps.unwrap_or_default();
                let has_dynamic = caps
                    .iter()
                    .any(|c| matches!(c, CapSummary::ImmutableDynamic(_)));
                let kind = if has_dynamic {
                    SharedClosureHoistKind::FactoryWrapper
                } else {
                    SharedClosureHoistKind::Direct
                };
                let mut hoisted_cap_locals = BTreeMap::new();
                for (cap_idx, cap) in caps.iter().enumerate() {
                    if let CapSummary::HoistedDirect(dep_local) = *cap {
                        hoisted_cap_locals.insert(cap_idx, dep_local);
                    }
                }
                let local = self.alloc_fresh_local(None);
                self.shared_reusable_closures.insert(
                    key,
                    SharedClosurePlan {
                        local,
                        kind,
                        hoisted_cap_locals,
                    },
                );
                progressed = true;
            }
        }

        // 若某直接提升共享闭包的全部 SSA 使用点均是另一已提升共享闭包的捕获源，
        // 标记该指令跳过死副本赋值（`r = shared_s`），消除中转变量。
        for (idx, instr) in self.proto.instrs.iter().enumerate() {
            let LowInstr::Closure(c) = instr else {
                continue;
            };
            let ClosureCreation::Reusable(shared) = c.creation else {
                continue;
            };
            let Some(plan) = self.shared_reusable_closures.get(&(c.proto.index(), shared)) else {
                continue;
            };
            if plan.kind != SharedClosureHoistKind::Direct {
                continue;
            }
            let iref = InstrRef(idx);
            let Some(def_val) = ssa.instr_def_value(iref, c.dst) else {
                continue;
            };
            let uses = &ssa.uses[def_val.index()];
            if uses.is_empty() {
                continue;
            }
            let all_uses_hoisted_closure_caps = uses.iter().all(|u| {
                let UseSite::Instr { instr: ui, .. } = *u else {
                    return false;
                };
                let LowInstr::Closure(uc) = &self.proto.instrs[ui.index()] else {
                    return false;
                };
                let ClosureCreation::Reusable(ushared) = uc.creation else {
                    return false;
                };
                self.shared_reusable_closures
                    .contains_key(&(uc.proto.index(), ushared))
            });
            if all_uses_hoisted_closure_caps {
                self.skipped_hoisted_closure_defs.insert(iref);
            }
        }
    }

    fn insert_hoisted_shared_closures(&mut self, body: &mut AstBlock) {
        if self.hoisted_shared_closures.is_empty() {
            return;
        }
        let items = std::mem::take(&mut self.hoisted_shared_closures);
        for item in items {
            let decl = AstStmt::LocalFunctionDecl(Box::new(super::common::AstLocalFunctionDecl {
                name: AstBindingRef::Local(item.local),
                func: item.func,
            }));
            if !insert_hoisted_decl_after_deps(body, &decl, &item.dep_locals) {
                body.stmts.insert(0, decl);
            }
        }
    }

    fn insert_luau_fresh_const_capture_guards(&mut self, body: &mut AstBlock) {
        if self.target.version != crate::decompile::DecompileDialect::Luau
            || self.luau_fresh_const_capture_locals.is_empty()
        {
            return;
        }
        // 仅对在函数体内从无后续覆写（单一字面量 LocalDecl）的局部插入 `if false then x = nil end`
        let mut reassigned = BTreeSet::new();
        collect_assigned_locals_in_block(body, &mut reassigned);
        let targets: BTreeSet<LocalId> = self
            .luau_fresh_const_capture_locals
            .iter()
            .copied()
            .filter(|l| !reassigned.contains(l))
            .collect();
        if targets.is_empty() {
            return;
        }
        inject_luau_fresh_const_guards_in_block(body, &targets);
    }

    /// 还原 Lua 5.1 省略 `LOADNIL` 的函数入口未引用源码局部（`start_pc == 0 && reg >= num_params`）。
    fn prepend_unreferenced_entry_debug_locals(&mut self, body: &mut AstBlock) {
        if self.proto.debug_locals.is_empty() {
            return;
        }
        let num_params = usize::from(self.proto.signature.num_params);
        let mut missing: Vec<(usize, String)> = Vec::new();
        for dl in self.proto.debug_locals.iter() {
            if !dl.is_source()
                || dl.start_pc != 0
                || dl.start_pc >= dl.end_pc
                || dl.reg.index() < num_params
            {
                continue;
            }
            let already_allocated = self
                .local_slots
                .iter()
                .flatten()
                .any(|slot| slot.reg == dl.reg);
            if already_allocated {
                continue;
            }
            if let Ok(name) = std::str::from_utf8(&dl.name.bytes) {
                missing.push((dl.reg.index(), name.to_owned()));
            }
        }
        if missing.is_empty() {
            return;
        }
        missing.sort_by_key(|(reg, _)| *reg);
        missing.dedup_by_key(|(reg, _)| *reg);
        let mut decls = Vec::with_capacity(missing.len());
        for (_, name) in missing {
            let id = self.alloc_fresh_local(Some(name));
            decls.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                bindings: vec![AstLocalBinding {
                    id: AstBindingRef::Local(id),
                    attr: AstLocalAttr::None,
                    is_debug_hinted: true,
                }],
                values: Vec::new(),
            })));
        }
        decls.append(&mut body.stmts);
        body.stmts = decls;
    }

    pub(super) fn alloc_eval_order(&mut self) -> usize {
        self.next_eval_order += 1;
        self.next_eval_order
    }

    /// 识别在循环体内被按引用捕获、但该循环体内没有 `Close(Explicit)` 覆盖该寄存器的局部变量。
    /// 这类变量在原字节码中属于“声明于循环外、跨迭代共享同一 upvalue cell”的变量（如 `local v; ::again:: ... goto again`），
    /// LCA 声明下沉时绝不能将其下沉到循环体内部，否则重编译时会每轮迭代关闭并分裂 upvalue 身份！
    fn compute_loop_shared_capture_locals(&self) -> BTreeSet<LocalId> {
        let mut shared = BTreeSet::new();
        let cfg = &self.analysis.cfg;
        let ssa = &self.analysis.ssa;
        // 预先为每个自然循环计算其内部显式 CLOSE 覆盖的最低寄存器号
        let loop_min_close: Vec<Option<usize>> = self
            .analysis
            .graph
            .natural_loops
            .iter()
            .map(|nat_loop| {
                let mut min_r: Option<usize> = None;
                for &b in &nat_loop.blocks {
                    for iref in cfg.blocks[b.index()].instrs.iter() {
                        if let LowInstr::Close(close) = &self.proto.instrs[iref.index()]
                            && close.kind == CloseKind::Explicit
                        {
                            let r = close.from.index();
                            min_r = Some(min_r.map_or(r, |m| m.min(r)));
                        }
                    }
                }
                min_r
            })
            .collect();
        for (li, nat_loop) in self.analysis.graph.natural_loops.iter().enumerate() {
            let min_closed_reg = loop_min_close[li];
            for &b in &nat_loop.blocks {
                for iref in cfg.blocks[b.index()].instrs.iter() {
                    if let LowInstr::Closure(c) = &self.proto.instrs[iref.index()] {
                        for cap in &c.captures {
                            if let CaptureSource::ByReference(r) = cap.source {
                                let closed_in_loop =
                                    min_closed_reg.is_some_and(|from| r.index() >= from);
                                // 若外层仍有包含该闭包的自然循环对此寄存器执行了显式 CLOSE（如 while 内嵌 repeat），
                                // 说明变量声明属于外层循环体内而非全部循环之外，绝不能上提到最外层！
                                let closed_in_any_enclosing_loop = self
                                    .analysis
                                    .graph
                                    .natural_loops
                                    .iter()
                                    .enumerate()
                                    .any(|(oi, other)| {
                                        other.blocks.contains(&b)
                                            && loop_min_close[oi]
                                                .is_some_and(|from| r.index() >= from)
                                    });
                                if !closed_in_loop
                                    && !closed_in_any_enclosing_loop
                                    && let Some(uv) = ssa.instr_use_value(iref, r)
                                {
                                    let web = self
                                        .value_web
                                        .get(uv.index())
                                        .copied()
                                        .unwrap_or(uv.index());
                                    if let Some(&local) = self.web_locals.get(&web) {
                                        shared.insert(local);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        shared
    }

    pub(super) fn alloc_synthetic_local(&mut self) -> AstSyntheticLocalId {
        let id = AstSyntheticLocalId(*self.next_synthetic);
        *self.next_synthetic += 1;
        id
    }

    pub(super) fn alloc_fresh_local(&mut self, hint: Option<String>) -> LocalId {
        let id = LocalId(self.local_debug_hints.len());
        if hint.is_some() {
            self.debug_hinted_locals.insert(id);
        }
        self.local_debug_hints.push(hint);
        self.local_slots.push(None);
        id
    }

    pub(super) fn alloc_local_for_slot(&mut self, slot: SlotKey, hint: Option<String>) -> LocalId {
        if let Some(&existing) = self.slot_locals.get(&slot) {
            return existing;
        }
        let hint = hint.or_else(|| self.analysis.dataflow.debug_slot_hints.get(&slot).cloned());
        let id = self.alloc_fresh_local(hint);
        self.local_slots[id.index()] = Some(slot);
        if self.analysis.ssa.tbc_slots.contains(&slot) {
            self.tbc_locals.insert(id);
        }
        self.slot_locals.insert(slot, id);
        id
    }

    pub(super) fn alloc_local_for_value(
        &mut self,
        val: ValueId,
        slot: SlotKey,
        hint: Option<String>,
    ) -> LocalId {
        let web = self.value_web.get(val.index()).copied().unwrap_or(val.index());
        if let Some(&existing) = self.web_locals.get(&web) {
            return existing;
        }
        let is_tbc = self.analysis.ssa.tbc_values.contains(&val);
        let is_for_binding = self
            .for_binding_owners
            .get(val.index())
            .copied()
            .flatten()
            .is_some();
        // `<close>` 变量具备 `<const>` 语义，`for` 循环控制变量严格限于循环体作用域，
        // 二者均绝不通过 `slot_locals` 与外层同寄存器槽位别名混并。
        let is_pinned =
            self.analysis.ssa.pinned_values.contains(&val) && !is_tbc && !is_for_binding;
        if is_pinned && let Some(&existing) = self.slot_locals.get(&slot) {
            self.web_locals.insert(web, existing);
            return existing;
        }
        let hint = hint.or_else(|| self.web_debug_hints.get(&web).cloned());
        let id = self.alloc_fresh_local(hint);
        self.local_slots[id.index()] = Some(slot);
        if is_tbc {
            self.tbc_locals.insert(id);
        }
        self.web_locals.insert(web, id);
        if is_pinned {
            // 同步登记到 slot_locals，使无 Pruned Phi 的回退路径（如闭包捕获变量的 BoolAssign）
            // 仍精确写回同一捕获单元格，绝不分裂为新局部！
            self.slot_locals.entry(slot).or_insert(id);
        }
        id
    }

    /// 按 SSA `ValueId` 获取其所属 Web 的具名引用（形参保持 `ParamId`，其余按 Web 分配 `LocalId`）。
    pub(super) fn name_for_value(&mut self, val: ValueId, fallback_slot: SlotKey) -> AstNameRef {
        let slot = ssa_value_slot(&self.analysis.ssa, val).unwrap_or(fallback_slot);
        if slot.epoch == 0 && slot.reg.index() < usize::from(self.proto.signature.num_params) {
            return AstNameRef::Param(ParamId(slot.reg.index()));
        }
        let local = self.alloc_local_for_value(val, slot, None);
        AstNameRef::Local(local)
    }

    /// 只读查询指令 `iref` 写入寄存器 `reg` 若已分配对应的变量名（绝不分配幽灵 LocalId）。
    pub(super) fn existing_name_for_def_at(&self, iref: InstrRef, reg: Reg) -> Option<AstNameRef> {
        let slot = self.analysis.ssa.slot_at(iref, reg);
        if let Some(val) = self.analysis.ssa.instr_def_value(iref, reg) {
            let vslot = ssa_value_slot(&self.analysis.ssa, val).unwrap_or(slot);
            if vslot.epoch == 0 && vslot.reg.index() < usize::from(self.proto.signature.num_params)
            {
                return Some(AstNameRef::Param(ParamId(vslot.reg.index())));
            }
            let web = self.value_web.get(val.index()).copied().unwrap_or(val.index());
            return self.web_locals.get(&web).copied().map(AstNameRef::Local);
        }
        if slot.epoch == 0 && slot.reg.index() < usize::from(self.proto.signature.num_params) {
            return Some(AstNameRef::Param(ParamId(slot.reg.index())));
        }
        self.slot_locals.get(&slot).copied().map(AstNameRef::Local)
    }

    /// 获取指令 `iref` **写入**寄存器 `reg` 的目标变量名（按 Def 的 SSA Web 解析）。
    pub(super) fn name_for_def_at(&mut self, iref: InstrRef, reg: Reg) -> AstNameRef {
        let slot = self.analysis.ssa.slot_at(iref, reg);
        if let Some(val) = self.analysis.ssa.instr_def_value(iref, reg) {
            return self.name_for_value(val, slot);
        }
        self.name_for_slot(slot)
    }

    /// 获取指令 `iref` **读取**寄存器 `reg` 的来源变量名（按 Use 的 SSA Web 解析）。
    pub(super) fn name_for_use_at(&mut self, iref: InstrRef, reg: Reg) -> AstNameRef {
        let slot = self.analysis.ssa.slot_at(iref, reg);
        if let Some(val) = self.analysis.ssa.instr_use_value(iref, reg) {
            return self.name_for_value(val, slot);
        }
        self.name_for_slot(slot)
    }

    /// 获取挂起项落盘时的目标变量名。
    pub(in crate::ast::lift) fn name_for_pending(&mut self, item: &PendingExpr) -> AstNameRef {
        let slot = self.analysis.ssa.slot_at(item.anchor, item.reg);
        if let Some(val) = item.val {
            return self.name_for_value(val, slot);
        }
        self.name_for_def_at(item.anchor, item.reg)
    }

    pub(super) fn name_for_slot(&mut self, slot: SlotKey) -> AstNameRef {
        if slot.epoch == 0 && slot.reg.index() < usize::from(self.proto.signature.num_params) {
            return AstNameRef::Param(ParamId(slot.reg.index()));
        }
        let local = self.alloc_local_for_slot(slot, None);
        AstNameRef::Local(local)
    }

    pub(super) fn into_proto_meta(
        self,
        parent_captures: Option<(ProtoId, Vec<AstCapture>)>,
        state_machine_count: usize,
    ) -> AstProtoMeta {
        let num_params = usize::from(self.proto.signature.num_params);
        let params: Vec<ParamId> = (0..num_params).map(ParamId).collect();
        let mut param_debug_hints = vec![None; num_params];
        for local in self.proto.debug_locals.iter() {
            if local.is_source()
                && local.start_pc == 0
                && local.reg.index() < num_params
                && param_debug_hints[local.reg.index()].is_none()
            {
                param_debug_hints[local.reg.index()] =
                    std::str::from_utf8(&local.name.bytes).ok().map(ToOwned::to_owned);
            }
        }
        let upvalue_count = usize::from(self.proto.upvalue_count);
        let upvalues = (0..upvalue_count).map(UpvalueId).collect();
        let upvalue_debug_hints = (0..upvalue_count)
            .map(|i| {
                self.proto
                    .upvalue_debug_names
                    .get(i)
                    .and_then(|o| o.as_ref())
                    .and_then(|s| std::str::from_utf8(&s.bytes).ok().map(ToOwned::to_owned))
            })
            .collect();
        let environment_upvalues = self
            .proto
            .environment_upvalues
            .iter()
            .map(|u| UpvalueId(u.index()))
            .collect();

        AstProtoMeta {
            id: self.proto_id,
            source: self.proto.source.as_ref().map(LuaString::from_raw),
            line_range: self.proto.line_range,
            signature: self.proto.signature,
            params,
            param_debug_hints,
            local_count: self.local_debug_hints.len(),
            local_debug_hints: self.local_debug_hints,
            vararg_param_local: self.vararg_param_local,
            lexical_environment_local: self.lexical_environment_local,
            upvalues,
            upvalue_debug_hints,
            environment_upvalues,
            parent_captures,
            source_origin: Some(self.proto.origin),
            state_machine_count,
        }
    }

    // ── 控制流 Region 提升 ───────────────────────────────────

    pub(super) fn lift_region(&mut self, region: &Region) -> AstBlock {
        self.lift_region_with_scope(region, false)
    }

    pub(super) fn lift_region_with_scope(
        &mut self,
        region: &Region,
        preserve_trailing_close_block: bool,
    ) -> AstBlock {
        self.block_last_close_len.push(None);
        let mut stmts = Vec::new();
        self.lift_region_into(region, &mut stmts);
        self.flush_pending_global_init(&mut stmts);
        self.flush_all_pending(&mut stmts);
        truncate_unreachable_after_terminator(&mut stmts);
        let last_close_len = self.block_last_close_len.pop().flatten();
        // 在 `if`/`while`/`for` 等普通子块末尾，若 `Close(Explicit)` 之后没有任何后续语句，
        // 外层块自身 `end` 已在同一位置关闭这些局部，拆去冗余尾部 `do ... end`；
        // 但在函数根块（`debug_06` `explicit_tail` 的 `"return"` hook 时序）和 `repeat` 体（`until cond` 前关闭）
        // 必须保留显式 `do ... end`！
        if !preserve_trailing_close_block
            && last_close_len == Some(stmts.len())
            && matches!(stmts.last(), Some(AstStmt::DoBlock(_)))
            && let Some(AstStmt::DoBlock(inner)) = stmts.pop()
        {
            stmts.extend(inner.stmts);
        }
        AstBlock { stmts }
    }

    fn lift_region_into(&mut self, region: &Region, out: &mut Vec<AstStmt>) {
        match region {
            Region::Empty => {}
            Region::Block(block) => {
                // 不在普通块尾无条件 flush，允许紧随其后的 BoolAssign / For / If 顺滑消费 pending 栈。
                self.lift_block_instrs(*block, false, out);
            }
            Region::BlockPrefix(block) => {
                self.lift_block_instrs(*block, true, out);
            }
            Region::BlockSlice {
                block,
                start_instr,
                end_instr,
            } => {
                let range = self.analysis.cfg.blocks[block.index()].instrs;
                let lo = start_instr.index().max(range.start.index());
                let hi = end_instr.index().min(range.end());
                for idx in lo..hi {
                    self.lift_instr(InstrRef(idx), out);
                }
            }
            Region::DoScope(inner) => {
                self.flush_all_pending(out);
                let scope_block = self.lift_region_with_scope(inner, false);
                out.push(AstStmt::DoBlock(Box::new(scope_block)));
            }
            Region::BoolAssign {
                dst,
                cond,
                join_block,
            } => {
                // `BoolAssign` 对应 `if cond then dst = true else dst = false end`，结果必为布尔值：
                // 若条件表达式本身不保证产出 boolean（如 `f()`、`x`、`a and b`），需用 `not not` 强制转布尔。
                let mut expr = self.lift_cond_expr(cond, out);
                if !expr_is_guaranteed_bool(&expr) {
                    expr = AstExpr::Unary(Box::new(super::common::AstUnaryExpr {
                        op: super::common::AstUnaryOpKind::Not,
                        expr: AstExpr::Unary(Box::new(super::common::AstUnaryExpr {
                            op: super::common::AstUnaryOpKind::Not,
                            expr,
                        })),
                    }));
                }
                // 查找 join_block 中对应 dst 的 Phi 值，判断该布尔表达式是否仅在 join_block 内被单次消费
                // （例如 `assert(a == b)`、`local ok = a == b and c == d`）—— 若是则直接压入 pending 栈！
                let join_anchor = self.analysis.cfg.blocks[join_block.index()]
                    .instrs
                    .iter()
                    .next()
                    .or_else(|| cond_anchor_instr(cond, self.analysis))
                    .unwrap_or(InstrRef(0));
                let phi_val = self.analysis.ssa.block_phis[join_block.index()]
                    .iter()
                    .map(|&pid| &self.analysis.ssa.phis[pid.index()])
                    .find(|phi| phi.reg == *dst)
                    .map(|phi| phi.value);
                let can_keep_pending = phi_val.is_some_and(|pv| {
                    if self.analysis.ssa.pinned_values.contains(&pv) {
                        return false;
                    }
                    let uses = &self.analysis.ssa.uses[pv.index()];
                    uses.len() == 1
                        && matches!(
                            uses[0],
                            UseSite::Instr { block: ub, .. }
                                if ub == *join_block
                                    || (self.analysis.graph.dominates(*join_block, ub)
                                        && self.analysis.graph.postdominates(ub, *join_block))
                        )
                        && !self.debug_local_active_after_instr(join_anchor, *dst)
                });
                let effect = if expr_may_have_side_effect(&expr) {
                    crate::analysis::EffectClass::MayObserveOrWrite
                } else {
                    crate::analysis::EffectClass::ReadsState
                };
                self.flush_before_reg_write(join_anchor, *dst, out);
                if can_keep_pending {
                    let order = self.alloc_eval_order();
                    self.pending.push(PendingExpr {
                        reg: *dst,
                        val: phi_val,
                        anchor: join_anchor,
                        expr,
                        effect,
                        order,
                        is_building_table: false,
                        accepts_set_table: false,
                        is_luau_template: false,
                        luau_max_fields: None,
                        luau_force_index_keys: false,
                        is_luajit_indexed: false,
                        is_luajit_template: false,
                        table_sealed_by_setlist: false,
                        array_field_count: 0,
                        field_orders: Vec::new(),
                        open_producer: None,
                        method_lookup: None,
                    });
                } else {
                    let target_slot = self.analysis.ssa.slot_at(join_anchor, *dst);
                    let target_name = if let Some(pv) = phi_val {
                        self.name_for_value(pv, target_slot)
                    } else {
                        self.name_for_slot(target_slot)
                    };
                    self.flush_all_pending(out);
                    out.push(AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![AstLValue::Name(target_name)],
                        values: vec![expr],
                        compound_op: None,
                    })));
                }
            }
            Region::Sequence(items) => {
                for item in items {
                    self.lift_region_into(item, out);
                }
            }
            Region::If {
                cond,
                then_body,
                else_body,
            } => {
                let cond_expr = self.lift_cond_expr(cond, out);
                self.flush_all_pending(out);
                let then_block = self.lift_region(then_body);
                let else_block = else_body.as_deref().map(|b| self.lift_region(b));
                out.push(AstStmt::If(Box::new(AstIf {
                    cond: cond_expr,
                    then_block,
                    else_block,
                })));
            }
            Region::NumericFor {
                init_block,
                init_instr,
                body,
                index,
                limit,
                step,
                binding,
            } => {
                self.lift_block_instrs(*init_block, true, out);
                let mut bounds =
                    self.resolve_reg_sequence(*init_instr, &[*index, *limit, *step], out);
                let step_expr = bounds.pop().unwrap();
                let limit_expr = bounds.pop().unwrap();
                let start = bounds.pop().unwrap();
                self.flush_all_pending(out);

                let binding_slot = self.analysis.ssa.slot_at(*init_instr, *binding);
                let binding_local =
                    if let Some(val) = self.analysis.ssa.instr_def_value(*init_instr, *binding) {
                        self.alloc_local_for_value(val, binding_slot, None)
                    } else {
                        self.alloc_local_for_slot(binding_slot, None)
                    };
                self.for_bindings.insert((*init_instr, *binding), binding_local);

                let body_block = self.lift_region(body);
                out.push(AstStmt::NumericFor(Box::new(AstNumericFor {
                    binding: AstBindingRef::Local(binding_local),
                    start,
                    limit: limit_expr,
                    step: step_expr,
                    body: body_block,
                })));
            }
            Region::GenericFor {
                prep_block,
                header_block,
                call_instr,
                loop_instr,
                body,
                iterator,
                state,
                control,
                bindings,
            } => {
                if let Some(prep) = prep_block {
                    self.lift_block_instrs(*prep, false, out);
                }
                // 发射 header_block 中 GenericForCall 之前的指令（若有）
                let hrange = self.analysis.cfg.blocks[header_block.index()].instrs;
                for iref in hrange.iter() {
                    if iref == *call_instr {
                        break;
                    }
                    self.lift_instr(iref, out);
                }
                // 若存在 `GenericForPrep`（Lua 5.4 / Lua 5.5），必须按其源寄存器 `(iterator, state, control_source[, closing_source])`
                // 在 `prep_iref` 处解析初值（Lua 5.5 会交换 control/closing，且支持第 4 个 `<close>` 迭代返回值）。
                let prep_info = prep_block.and_then(|pb| {
                    self.analysis.cfg.blocks[pb.index()]
                        .instrs
                        .iter()
                        .find_map(|iref| match &self.proto.instrs[iref.index()] {
                            LowInstr::GenericForPrep(gp) => Some((
                                iref,
                                gp.iterator,
                                gp.state,
                                gp.control_source,
                                (gp.closing_source != gp.control_source)
                                    .then_some(gp.closing_source),
                            )),
                            _ => None,
                        })
                });
                let (iter_use_iref, iter_reg, state_reg, ctrl_reg, closing_reg) =
                    if let Some((pi, it, st, ct, cl)) = prep_info {
                        (pi, it, st, ct, cl)
                    } else {
                        (*call_instr, *iterator, *state, *control, None)
                    };
                let mut iter_regs = vec![iter_reg, state_reg, ctrl_reg];
                if let Some(cl) = closing_reg {
                    iter_regs.push(cl);
                }
                let mut iter_seq = self.resolve_reg_sequence(iter_use_iref, &iter_regs, out);
                let closing_expr = closing_reg.map(|_| iter_seq.pop().unwrap());
                let ctrl_expr = iter_seq.pop().unwrap();
                let state_expr = iter_seq.pop().unwrap();
                let iter_expr = iter_seq.pop().unwrap();
                self.flush_all_pending(out);

                // 若紧接在前的赋值语句恰好是多返回值 `iter, state, ctrl[, closing] = pairs(t)`，直接收回进 GenericFor！
                let mut iterator_list = self.absorb_or_build_generic_for_iterators(
                    iter_use_iref,
                    iter_reg,
                    state_reg,
                    ctrl_reg,
                    closing_reg,
                    iter_expr,
                    state_expr,
                    ctrl_expr,
                    closing_expr,
                    out,
                );
                // 匿名函数体直接内联到 `for ... in function(...) ... end` 头位置可读性差，
                // 拆为紧邻前序的 `local function iter(...) ... end` 再传入 `for` 头。
                if matches!(iterator_list.first(), Some(AstExpr::FunctionExpr(_))) {
                    let iter_local = self.alloc_fresh_local(None);
                    let func_expr = std::mem::replace(
                        &mut iterator_list[0],
                        AstExpr::Var(AstNameRef::Local(iter_local)),
                    );
                    out.push(AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![AstLValue::Name(AstNameRef::Local(iter_local))],
                        values: vec![func_expr],
                        compound_op: None,
                    })));
                }

                let mut ast_bindings = Vec::with_capacity(bindings.len.max(1));
                for offset in 0..bindings.len {
                    let r = Reg(bindings.start.index() + offset);
                    let slot = self.analysis.ssa.slot_at(*call_instr, r);
                    let local = if let Some(val) = self
                        .analysis
                        .ssa
                        .instr_def_value(*call_instr, r)
                        .or_else(|| self.analysis.ssa.instr_use_value(*loop_instr, r))
                    {
                        self.alloc_local_for_value(val, slot, None)
                    } else {
                        self.alloc_local_for_slot(slot, None)
                    };
                    self.for_bindings.insert((*loop_instr, r), local);
                    ast_bindings.push(AstBindingRef::Local(local));
                }
                if ast_bindings.is_empty() {
                    let local = self.alloc_fresh_local(None);
                    ast_bindings.push(AstBindingRef::Local(local));
                }

                let body_block = self.lift_region(body);
                out.push(AstStmt::GenericFor(Box::new(AstGenericFor {
                    bindings: ast_bindings,
                    iterator: iterator_list,
                    body: body_block,
                })));
            }
            Region::While { cond, body } => {
                self.flush_all_pending(out);
                let mut cond_setup = Vec::new();
                let cond_expr = self.lift_cond_expr(cond, &mut cond_setup);
                self.flush_all_pending(&mut cond_setup);
                if cond_setup.is_empty() {
                    let body_block = self.lift_region(body);
                    out.push(AstStmt::While(Box::new(AstWhile {
                        cond: cond_expr,
                        body: body_block,
                    })));
                } else {
                    // 条件求值含无法内联的前置语句：降为 `while true do <setup>; if not cond then break end; <body> end`
                    let mut stmts = cond_setup;
                    stmts.push(AstStmt::If(Box::new(AstIf {
                        cond: AstExpr::Unary(Box::new(super::common::AstUnaryExpr {
                            op: super::common::AstUnaryOpKind::Not,
                            expr: cond_expr,
                        })),
                        then_block: AstBlock {
                            stmts: vec![AstStmt::Break],
                        },
                        else_block: None,
                    })));
                    self.lift_region_into(body, &mut stmts);
                    self.flush_all_pending(&mut stmts);
                    out.push(AstStmt::While(Box::new(AstWhile {
                        cond: AstExpr::Boolean(true),
                        body: AstBlock { stmts },
                    })));
                }
            }
            Region::Repeat { body, until_cond } => {
                self.flush_all_pending(out);
                let mut body_block = self.lift_region_with_scope(body, true);
                let mut cond_setup = Vec::new();
                let cond_expr = self.lift_cond_expr(until_cond, &mut cond_setup);
                self.flush_all_pending(&mut cond_setup);
                body_block.stmts.extend(cond_setup);
                out.push(AstStmt::Repeat(Box::new(AstRepeat {
                    body: body_block,
                    cond: cond_expr,
                })));
            }
            Region::Break => {
                self.flush_all_pending(out);
                out.push(AstStmt::Break);
            }
            Region::Continue => {
                self.flush_all_pending(out);
                out.push(AstStmt::Continue);
            }
            Region::Goto(label) => {
                self.flush_all_pending(out);
                out.push(AstStmt::Goto(Box::new(AstGoto {
                    target: AstLabelId(*label),
                })));
            }
            Region::Labeled(label, inner) => {
                self.flush_all_pending(out);
                out.push(AstStmt::Label(Box::new(AstLabel {
                    id: AstLabelId(*label),
                })));
                self.lift_region_into(inner, out);
            }
            Region::StateMachine {
                entry_state,
                states,
            } => {
                self.flush_all_pending(out);
                self.emit_state_machine(*entry_state, states, out);
            }
        }
    }

    fn emit_state_machine(
        &mut self,
        entry_state: usize,
        states: &[StateArm],
        out: &mut Vec<AstStmt>,
    ) {
        let state_var = self.alloc_synthetic_local();
        let state_ref = AstNameRef::SyntheticLocal(state_var);
        let state_expr = || AstExpr::Var(state_ref.clone());
        let set_state = |val: i64| {
            AstStmt::Assign(Box::new(AstAssign {
                targets: vec![AstLValue::Name(state_ref.clone())],
                values: vec![AstExpr::Integer(val)],
                compound_op: None,
            }))
        };

        out.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
            bindings: vec![AstLocalBinding {
                id: AstBindingRef::SyntheticLocal(state_var),
                attr: AstLocalAttr::None,
                is_debug_hinted: false,
            }],
            values: vec![AstExpr::Integer(entry_state as i64)],
        })));

        // 构建 `if _state == 1 then ... elseif _state == 2 then ... end` 链
        let mut chain: Option<AstBlock> = None;
        for arm in states.iter().rev() {
            let mut arm_stmts = Vec::new();
            self.lift_region_into(&arm.body, &mut arm_stmts);
            self.flush_all_pending(&mut arm_stmts);

            match &arm.next {
                StateTransition::Exit => arm_stmts.push(set_state(0)),
                StateTransition::Jump(next) => arm_stmts.push(set_state(*next as i64)),
                StateTransition::Branch {
                    cond,
                    then_state,
                    else_state,
                } => {
                    let c = self.lift_cond_expr(cond, &mut arm_stmts);
                    self.flush_all_pending(&mut arm_stmts);
                    arm_stmts.push(AstStmt::If(Box::new(AstIf {
                        cond: c,
                        then_block: AstBlock {
                            stmts: vec![set_state(then_state.unwrap_or(0) as i64)],
                        },
                        else_block: Some(AstBlock {
                            stmts: vec![set_state(else_state.unwrap_or(0) as i64)],
                        }),
                    })));
                }
                StateTransition::Terminated => {}
            }

            let cmp = AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Eq,
                lhs: state_expr(),
                rhs: AstExpr::Integer(arm.state_id as i64),
            }));
            let if_stmt = AstStmt::If(Box::new(AstIf {
                cond: cmp,
                then_block: AstBlock { stmts: arm_stmts },
                else_block: chain,
            }));
            chain = Some(AstBlock {
                stmts: vec![if_stmt],
            });
        }

        let while_cond = AstExpr::Unary(Box::new(super::common::AstUnaryExpr {
            op: super::common::AstUnaryOpKind::Not,
            expr: AstExpr::Binary(Box::new(AstBinaryExpr {
                op: AstBinaryOpKind::Eq,
                lhs: state_expr(),
                rhs: AstExpr::Integer(0),
            })),
        }));

        out.push(AstStmt::While(Box::new(AstWhile {
            cond: while_cond,
            body: chain.unwrap_or_default(),
        })));
    }

    #[allow(clippy::too_many_arguments)]
    fn absorb_or_build_generic_for_iterators(
        &mut self,
        iter_use_iref: InstrRef,
        iterator: Reg,
        state: Reg,
        control: Reg,
        closing: Option<Reg>,
        iter_expr: AstExpr,
        state_expr: AstExpr,
        ctrl_expr: AstExpr,
        closing_expr: Option<AstExpr>,
        out: &mut Vec<AstStmt>,
    ) -> Vec<AstExpr> {
        // 如果 `out.last()` 恰好是多返回值赋值 `iter, state, ctrl[, closing] = pairs(t)` 且这些内部槽
        // 仅服务于本 GenericFor，直接收回该赋值，生成干净的 `for k, v in pairs(t) do`！
        let iter_name = self.name_for_use_at(iter_use_iref, iterator);
        let state_name = self.name_for_use_at(iter_use_iref, state);
        let ctrl_name = self.name_for_use_at(iter_use_iref, control);
        let closing_name = closing.map(|r| self.name_for_use_at(iter_use_iref, r));
        let matches_last_assign = if let Some(AstStmt::Assign(assign)) = out.last()
            && assign.compound_op.is_none()
            && assign.values.len() == 1
            && assign.targets.len() >= 3
            && assign.targets[0] == AstLValue::Name(iter_name)
            && assign.targets[1] == AstLValue::Name(state_name)
            && assign.targets[2] == AstLValue::Name(ctrl_name)
            && (assign.targets.len() == 3
                || (assign.targets.len() == 4
                    && closing_name
                        .as_ref()
                        .is_some_and(|cn| assign.targets[3] == AstLValue::Name(cn.clone()))))
        {
            // 确认这些 SSA 值仅由本 GenericFor 消费，未逃逸到循环外
            let mut check_regs = vec![iterator, state, control];
            if let Some(cr) = closing
                && assign.targets.len() == 4
            {
                check_regs.push(cr);
            }
            check_regs.into_iter().all(|r| {
                self.analysis
                    .ssa
                    .instr_use_value(iter_use_iref, r)
                    .is_some_and(|v| {
                        self.analysis.ssa.uses[v.index()].iter().all(|u| match *u {
                            UseSite::Instr { instr: ui, .. } => {
                                matches!(
                                    self.proto.instrs[ui.index()],
                                    LowInstr::GenericForPrep(_)
                                        | LowInstr::GenericForCall(_)
                                        | LowInstr::GenericForLoop(_)
                                )
                            }
                            UseSite::Phi { .. } => false,
                        })
                    })
            })
        } else {
            false
        };
        if matches_last_assign && let Some(AstStmt::Assign(assign)) = out.pop() {
            return assign.values;
        }

        // 若三/四元组由单条多返回调用（如 pairs(t) / ipairs(t)）直接内联产出，只保留该调用表达式。
        if let (Some(vi), Some(vs)) = (
            self.analysis.ssa.instr_use_value(iter_use_iref, iterator),
            self.analysis.ssa.instr_use_value(iter_use_iref, state),
        ) && let (
            SsaDef::Instr {
                instr: di,
                result_index: 0,
                ..
            },
            SsaDef::Instr {
                instr: ds,
                result_index: 1,
                ..
            },
        ) = (self.analysis.ssa.def_of(vi), self.analysis.ssa.def_of(vs))
            && di == ds
            && matches!(iter_expr, AstExpr::Call(_) | AstExpr::MethodCall(_))
        {
            return vec![iter_expr];
        }
        let mut list = vec![iter_expr, state_expr, ctrl_expr];
        if let Some(cl) = closing_expr {
            list.push(cl);
        }
        let full_len = list.len();
        while list.len() > 1 && matches!(list.last(), Some(AstExpr::Nil)) {
            list.pop();
        }
        // 只要裁掉了尾部显式 `nil` 槽，新的末项在字节码中仅占单寄存器槽（如 `for k in iter, (state()) do`），
        // 必须补单值括号防止多返回展开侵入后续 `ctrl`/`closing` 槽！
        if list.len() < full_len
            && let Some(last) = list.last_mut()
        {
            let taken = std::mem::replace(last, AstExpr::Nil);
            *last = wrap_single_value_if_needed(taken);
        }
        list
    }

    fn lift_block_instrs(&mut self, block: BlockId, skip_terminator: bool, out: &mut Vec<AstStmt>) {
        let range = self.analysis.cfg.blocks[block.index()].instrs;
        let last = range.last();
        for iref in range.iter() {
            if skip_terminator && Some(iref) == last {
                break;
            }
            self.lift_instr(iref, out);
        }
    }

    /// 提升单条 LowInstr，利用顺序消费栈自动内联临时表达式与表构造器。
    pub(super) fn lift_instr(&mut self, iref: InstrRef, out: &mut Vec<AstStmt>) {
        let instr = &self.proto.instrs[iref.index()];
        // 若上一条 `ErrNil` 留有待配对的 `global name = ...`，而本条并非紧随的 `SetTable`，先落地兜底声明。
        if self.pending_global_init.is_some() && !matches!(instr, LowInstr::SetTable(_)) {
            self.flush_pending_global_init(out);
        }
        match instr {
            LowInstr::Jump(_)
            | LowInstr::Branch(_)
            | LowInstr::NumericForInit(_)
            | LowInstr::NumericForLoop(_)
            | LowInstr::GenericForPrep(_)
            | LowInstr::GenericForCall(_)
            | LowInstr::GenericForLoop(_)
            | LowInstr::Close(crate::transformer::CloseInstr {
                kind: CloseKind::Return(_) | CloseKind::TailCall(_),
                ..
            }) => {}

            LowInstr::Close(close) => {
                // Close 属于控制或声明边界，先冲刷非开放多值的挂起表达式；
                // 绝不把紧接在 `Return(Open)` 前的 `open_producer`（如 LuaJIT UCLO + RETM）提前落盘截断为单值！
                if self
                    .pending
                    .last()
                    .is_some_and(|p| p.open_producer.is_some())
                {
                    let open_item = self.pending.pop().unwrap();
                    self.flush_all_pending(out);
                    self.pending.push(open_item);
                } else {
                    self.flush_all_pending(out);
                }
                if close.kind == CloseKind::Explicit {
                    self.wrap_explicit_close_scope(iref, close.from, out);
                }
            }
            LowInstr::Tbc(tbc) => {
                if self
                    .pending
                    .last()
                    .is_some_and(|p| p.open_producer.is_some())
                {
                    let open_item = self.pending.pop().unwrap();
                    self.flush_all_pending(out);
                    self.pending.push(open_item);
                } else {
                    self.flush_all_pending(out);
                }
                // 若 `<close>` 寄存器的初始化值来自跨分支 Phi（如 `local x <close> = cond and a or b`）
                // 或尚未绑定为 `tbc_locals` 的非 `<close>` 局部/形参，则在 `TBC` 处显式落地
                // `local x <close> = <src>`，既严格保住 `<close>` 关闭协议，又不违反 `<const>` 禁止重赋值规则！
                let slot = self.analysis.ssa.slot_at(iref, tbc.reg);
                let tbc_hint = self.tbc_debug_hint_at(iref, tbc.reg);
                if let Some(tbc_val) = self.analysis.ssa.instr_use_value(iref, tbc.reg) {
                    let web = self
                        .value_web
                        .get(tbc_val.index())
                        .copied()
                        .unwrap_or(tbc_val.index());
                    let already_tbc = self
                        .web_locals
                        .get(&web)
                        .is_some_and(|loc| self.tbc_locals.contains(loc));
                    if !already_tbc {
                        let src_expr = match self.analysis.ssa.defs[tbc_val.index()] {
                            SsaDef::Phi { phi, .. } => self.analysis.ssa.phis[phi.index()]
                                .incomings
                                .iter()
                                .map(|&(_, src)| src)
                                .find(|&src| {
                                    !matches!(self.analysis.ssa.defs[src.index()], SsaDef::Undef { .. })
                                })
                                .map(|src| AstExpr::Var(self.name_for_value(src, slot)))
                                .unwrap_or(AstExpr::Nil),
                            _ => AstExpr::Var(self.name_for_value(tbc_val, slot)),
                        };
                        let is_dbg = tbc_hint.is_some();
                        let tbc_local = if !self.web_locals.contains_key(&web) {
                            self.alloc_local_for_value(tbc_val, slot, tbc_hint)
                        } else {
                            let id = self.alloc_fresh_local(tbc_hint);
                            self.local_slots[id.index()] = Some(slot);
                            self.web_locals.insert(web, id);
                            id
                        };
                        self.tbc_locals.insert(tbc_local);
                        if is_dbg {
                            self.debug_hinted_locals.insert(tbc_local);
                        }
                        out.push(AstStmt::LocalDecl(Box::new(AstLocalDecl {
                            bindings: vec![AstLocalBinding {
                                id: AstBindingRef::Local(tbc_local),
                                attr: AstLocalAttr::Close,
                                is_debug_hinted: is_dbg,
                            }],
                            values: vec![src_expr],
                        })));
                    }
                }
            }
            LowInstr::TypeGuard(tg) => {
                self.flush_all_pending(out);
                let block_idx = self.analysis.cfg.block_of_instr[iref.index()]
                    .map_or(0, BlockId::index);
                out.push(AstStmt::Error(format!(
                    "LuaJIT builtin {:?} type guard at block #{block_idx} has no exact Lua source spelling; guard check omitted",
                    tg.kind
                )));
            }

            LowInstr::Move(m) => {
                let expr = self.resolve_reg_expr(iref, m.src, out);
                self.emit_single_def(iref, m.dst, expr, out);
            }
            LowInstr::LoadNil(ln) => {
                // 检查这批寄存器中是否存在待构造表/调用参数准备的临时槽：
                // 若有，逐个压入 pending（绝不提前 flush 冲刷正在构造的 TableConstructor！）；
                // 仅当全部都需要物化时合并成单条多目标 `a, b = nil`。
                // 若同一块内存在 `Close(Explicit)` 将该 `LoadNil` 区间切分到内外两个不同作用域
                // （如 `local saved = nil; do local value = nil; ... end` 被编译为单条 `LOADNIL r0..r1` + `CLOSE r1`），
                // 必须拆分为逐寄存器独立赋值，使外层 `saved = nil` 留在 `do ... end` 之外并在重编译中立即收敛！
                let split_by_close = ln.dst.len > 1
                    && self.analysis.cfg.block_of_instr[iref.index()].is_some_and(|b| {
                        let range = self.analysis.cfg.blocks[b.index()].instrs;
                        let dst_start = ln.dst.start.index();
                        let dst_end = dst_start + ln.dst.len;
                        ((iref.index() + 1)..range.end()).any(|j| {
                            matches!(
                                &self.proto.instrs[j],
                                LowInstr::Close(c)
                                    if c.kind == CloseKind::Explicit
                                        && c.from.index() > dst_start
                                        && c.from.index() < dst_end
                            )
                        })
                    });
                let all_materialized = ln.dst.len > 1
                    && !split_by_close
                    && (0..ln.dst.len).all(|offset| {
                        let r = Reg(ln.dst.start.index() + offset);
                        self.analysis
                            .ssa
                            .instr_def_value(iref, r)
                            .is_none_or(|v| self.materialized_values.contains(&v))
                    });
                if all_materialized {
                    self.flush_all_pending(out);
                    let mut targets = Vec::with_capacity(ln.dst.len);
                    for offset in 0..ln.dst.len {
                        let r = Reg(ln.dst.start.index() + offset);
                        targets.push(AstLValue::Name(self.name_for_def_at(iref, r)));
                    }
                    out.push(AstStmt::Assign(Box::new(AstAssign {
                        targets,
                        values: vec![AstExpr::Nil],
                        compound_op: None,
                    })));
                } else {
                    for offset in 0..ln.dst.len {
                        let r = Reg(ln.dst.start.index() + offset);
                        self.emit_single_def(iref, r, AstExpr::Nil, out);
                    }
                }
            }
            LowInstr::LoadBool(lb) => {
                self.emit_single_def(iref, lb.dst, AstExpr::Boolean(lb.value), out);
            }
            LowInstr::LoadConst(lc) => {
                let expr = self.const_to_expr(lc.value);
                self.emit_single_def(iref, lc.dst, expr, out);
            }
            LowInstr::LoadInteger(li) => {
                self.emit_single_def(iref, li.dst, AstExpr::Integer(li.value), out);
            }
            LowInstr::LoadNumber(ln) => {
                self.emit_single_def(iref, ln.dst, AstExpr::Number(ln.value), out);
            }
            LowInstr::UnaryOp(u) => {
                let inner = self.resolve_reg_expr(iref, u.src, out);
                let op = match u.op {
                    crate::transformer::UnaryOpKind::Not => super::common::AstUnaryOpKind::Not,
                    crate::transformer::UnaryOpKind::Neg => super::common::AstUnaryOpKind::Neg,
                    crate::transformer::UnaryOpKind::BitNot => {
                        super::common::AstUnaryOpKind::BitNot
                    }
                    crate::transformer::UnaryOpKind::Length => {
                        super::common::AstUnaryOpKind::Length
                    }
                };
                let expr = AstExpr::Unary(Box::new(super::common::AstUnaryExpr {
                    op,
                    expr: inner,
                }));
                self.emit_single_def(iref, u.dst, expr, out);
            }
            LowInstr::BinaryOp(b) => {
                let (lhs, rhs) = self.resolve_binary_operands(iref, b.lhs, b.rhs, out);
                let op = map_binary_op(b.op);
                let expr = AstExpr::Binary(Box::new(AstBinaryExpr { op, lhs, rhs }));
                self.emit_single_def(iref, b.dst, expr, out);
            }
            LowInstr::Concat(c) => {
                let mut operands = Vec::with_capacity(c.src.len);
                let regs: Vec<Reg> = (0..c.src.len)
                    .map(|off| Reg(c.src.start.index() + off))
                    .collect();
                let mut exprs = self.resolve_reg_sequence(iref, &regs, out);
                operands.append(&mut exprs);
                let expr = operands
                    .into_iter()
                    .rev()
                    .reduce(|rhs, lhs| {
                        AstExpr::Binary(Box::new(AstBinaryExpr {
                            op: AstBinaryOpKind::Concat,
                            lhs,
                            rhs,
                        }))
                    })
                    .unwrap_or(AstExpr::String(LuaString::default()));
                self.emit_single_def(iref, c.dst, expr, out);
            }
            LowInstr::GetUpvalue(gu) => {
                let expr = self.upvalue_operand_expr(gu.src);
                self.emit_single_def(iref, gu.dst, expr, out);
            }
            LowInstr::SetUpvalue(su) => {
                let val = self.resolve_value_operand(iref, su.src, out);
                let target_name = self.upvalue_operand_name(su.dst);
                self.flush_all_pending(out);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![AstLValue::Name(target_name)],
                    values: vec![val],
                    compound_op: None,
                })));
            }
            LowInstr::GetTable(gt) => {
                if gt.kind == crate::transformer::GetTableKind::Raw {
                    self.flush_all_pending(out);
                    out.push(AstStmt::Error(
                        "LuaJIT raw table read has no exact Lua source form".to_owned(),
                    ));
                }
                let expr = self.lift_get_table(iref, gt.base, gt.key, gt.kind, out);
                self.emit_single_def(iref, gt.dst, expr, out);
            }
            LowInstr::SetTable(st) => {
                // 配对前一条 Lua 5.5 `ErrNil` + `SetTable(_ENV | local_env | wide _ENV[k], name, val)` → `global name = val`
                if let Some(pgi) = self.pending_global_init.take() {
                    let key_matches_const = matches!(
                        st.key,
                        crate::transformer::AccessKey::Const(c)
                            if self.const_string_utf8(c).as_deref() == Some(pgi.name.as_str())
                    );
                    let base_matches_direct = match pgi.local_env {
                        None => matches!(
                            st.base,
                            crate::transformer::AccessBase::Env
                                | crate::transformer::AccessBase::EnvironmentUpvalue(_)
                        ),
                        Some((env_reg, _)) => {
                            st.base == crate::transformer::AccessBase::Reg(env_reg)
                        }
                    };
                    // 宽常量索引（>255）的 `global name = val` 会被 Lua 5.5 编译成
                    // `GETUPVAL r_env, _ENV; LOADK r_key, "name"; ...; GETTABLE r_chk, r_env[r_key]; ERRNNIL; SETTABLE r_env[r_key] <- val`。
                    let matches_wide_env_store = pgi.local_env.is_none()
                        && matches!(st.base, crate::transformer::AccessBase::Reg(env_reg) if self.is_env_upvalue_reg(iref, env_reg))
                        && matches!(st.key, crate::transformer::AccessKey::Reg(key_reg) if self.is_const_string_reg(iref, key_reg, &pgi.name));
                    if (key_matches_const && base_matches_direct) || matches_wide_env_store {
                        if let Some((_, env_local)) = pgi.local_env {
                            self.lexical_environment_local = Some(env_local);
                        }
                        let val_expr = self.resolve_value_operand(iref, st.value, out);
                        self.flush_all_pending(out);
                        out.push(AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                            bindings: vec![AstGlobalBinding {
                                target: AstGlobalBindingTarget::Name(AstGlobalName {
                                    text: pgi.name,
                                }),
                                attr: AstGlobalAttr::None,
                            }],
                            values: vec![val_expr],
                        })));
                        return;
                    }
                    self.pending_global_init = Some(pgi);
                    self.flush_pending_global_init(out);
                }
                if st.kind == crate::transformer::SetTableKind::Raw {
                    let (lvalue, val_expr) =
                        self.lift_set_table_parts(iref, st.base, st.key, st.value, out);
                    self.flush_all_pending(out);
                    out.push(AstStmt::Error(
                        "LuaJIT raw table write has no exact Lua source form".to_owned(),
                    ));
                    out.push(AstStmt::Assign(Box::new(AstAssign {
                        targets: vec![lvalue],
                        values: vec![val_expr],
                        compound_op: None,
                    })));
                    return;
                }
                // 优先尝试 $O(N)$ 吸收进正在构造的 `TableConstructor`！
                if self.try_absorb_set_table(iref, st.base, st.key, st.value, out) {
                    return;
                }
                let (lvalue, val_expr) =
                    self.lift_set_table_parts(iref, st.base, st.key, st.value, out);
                self.flush_all_pending(out);
                out.push(AstStmt::Assign(Box::new(AstAssign {
                    targets: vec![lvalue],
                    values: vec![val_expr],
                    compound_op: None,
                })));
            }
            LowInstr::NewTable(nt) => {
                let table_expr = self.build_new_table_expr(&nt.allocation);
                let accepts_set_table = table_accepts_set_table(&nt.allocation);
                let is_luau_template = matches!(
                    nt.allocation,
                    crate::transformer::TableAllocation::LuauTemplate(_)
                );
                let (luau_max_fields, luau_force_index_keys) = match &nt.allocation {
                    crate::transformer::TableAllocation::Luau(pre) if pre.hash_capacity > 0 => (
                        Some(pre.array_capacity as usize + pre.hash_capacity as usize),
                        pre.array_capacity == 0,
                    ),
                    _ => (None, false),
                };
                // 仅当 LuaJIT `TNEW` 确实分配了数组部分（`array_capacity > 0`）时才把连续 1..N 键吸收为列表字段；
                // 纯哈希表（如 `{[1]=a, [2]=b, [3]=c}`，`array_capacity == 0`）必须保留显式 `[i] = v` 键以维持 `#t` 行为！
                let is_luajit_indexed = matches!(
                    nt.allocation,
                    crate::transformer::TableAllocation::Indexed {
                        array_capacity,
                        ..
                    } if array_capacity > 0
                );
                let is_luajit_template = matches!(
                    nt.allocation,
                    crate::transformer::TableAllocation::Template(_)
                );
                self.emit_new_table_def(
                    iref,
                    nt.dst,
                    table_expr,
                    accepts_set_table,
                    is_luau_template,
                    luau_max_fields,
                    luau_force_index_keys,
                    is_luajit_indexed,
                    is_luajit_template,
                    out,
                );
            }
            LowInstr::SetList(sl) => {
                self.lift_set_list(iref, sl.base, sl.values, sl.start_index, out);
            }
            LowInstr::Call(call) => {
                self.lift_call(iref, call, out);
            }
            LowInstr::TailCall(tc) => {
                let call_expr = self.lift_tail_call_expr(iref, tc, out);
                self.flush_all_pending(out);
                out.push(AstStmt::Return(Box::new(AstReturn {
                    values: vec![call_expr],
                })));
            }
            LowInstr::VarArg(va) => {
                self.lift_vararg(iref, va.results, out);
            }
            LowInstr::Return(ret) => {
                let values = self.resolve_value_pack(iref, ret.values, out);
                self.flush_all_pending(out);
                self.wrap_tail_debug_closed_scope(iref, &values, out);
                out.push(AstStmt::Return(Box::new(AstReturn { values })));
            }
            LowInstr::Closure(c) => {
                let func_expr = self.lift_closure(iref, c, out);
                if !self.skipped_hoisted_closure_defs.contains(&iref) {
                    self.emit_single_def(iref, c.dst, func_expr, out);
                }
            }
            LowInstr::ErrNil(en) => {
                // Lua 5.5 `global x = expr` 编译为 `GETTABUP/GETTABLE r_chk, _ENV, "x"; ERRNNIL r_chk, "x"; SETTABUP/SETTABLE _ENV, "x", val`：
                // 直接消费掉 `pending` 栈中的探针槽 `en.subject`（绝不冲刷成多余的 `local tmp = x` 读取），
                // 并暂存 `pending_global_init`（含可选的局部 `_ENV` 寄存器身份）以便与紧随的 `SetTable` 合成精确的 `global x = expr`！
                if let Some(pos) = self.pending.iter().rposition(|p| p.reg == en.subject) {
                    self.pending.remove(pos);
                }
                if let Some(name_ref) = en.name
                    && let Some(text) = self.const_string_utf8(name_ref)
                    && self.target.caps.global_decl
                    && self.target.version.is_identifier_name(&text)
                    && text != "_ENV"
                {
                    let local_env = self.detect_local_env_for_err_nil(iref, en.subject);
                    self.pending_global_init = Some(PendingGlobalInit {
                        name: text,
                        local_env,
                    });
                }
            }
        }
    }

    /// 识别 Lua 5.5 词法 `local _ENV = <upvalue|param>` 对应的局部环境寄存器：
    /// 严格满足 `naming/validate/environment.rs` 契约（无根环境 upvalue、直线控制流、无嵌套闭包、
    /// 单次由 upvalue/param 初始化），保证命名阶段 100% 合法通过。
    fn detect_local_env_for_err_nil(
        &self,
        err_iref: InstrRef,
        subject: Reg,
    ) -> Option<(Reg, LocalId)> {
        if !self.proto.environment_upvalues.is_empty()
            || self.analysis.cfg.blocks.len() != 2
            || self
                .proto
                .instrs
                .iter()
                .any(|i| matches!(i, LowInstr::Closure(_)))
        {
            return None;
        }
        let ssa = &self.analysis.ssa;
        let probe_val = ssa.instr_use_value(err_iref, subject)?;
        let SsaDef::Instr {
            instr: probe_iref, ..
        } = ssa.def_of(probe_val)
        else {
            return None;
        };
        let LowInstr::GetTable(gt) = &self.proto.instrs[probe_iref.index()] else {
            return None;
        };
        let crate::transformer::AccessBase::Reg(env_reg) = gt.base else {
            return None;
        };
        let env_val = ssa.instr_use_value(probe_iref, env_reg)?;
        let SsaDef::Instr {
            instr: def_iref, ..
        } = ssa.def_of(env_val)
        else {
            return None;
        };
        let valid_init = match &self.proto.instrs[def_iref.index()] {
            LowInstr::GetUpvalue(_) => true,
            LowInstr::Move(mv) => ssa
                .instr_use_value(def_iref, mv.src)
                .is_some_and(|v| matches!(ssa.def_of(v), SsaDef::Param { .. })),
            _ => false,
        };
        if !valid_init {
            return None;
        }
        let web = self.value_web[env_val.index()];
        let env_local = self.web_locals.get(&web).copied()?;
        if let Some(prev) = self.lexical_environment_local
            && prev != env_local
        {
            return None;
        }
        Some((env_reg, env_local))
    }

    fn is_env_upvalue_reg(&self, use_iref: InstrRef, reg: Reg) -> bool {
        let ssa = &self.analysis.ssa;
        let Some(val) = ssa.instr_use_value(use_iref, reg) else {
            return false;
        };
        let SsaDef::Instr {
            instr: def_iref, ..
        } = ssa.def_of(val)
        else {
            return false;
        };
        matches!(
            &self.proto.instrs[def_iref.index()],
            LowInstr::GetUpvalue(gu)
                if matches!(gu.src, crate::transformer::UpvalueOperand::Env(_)) || matches!(
                    gu.src,
                    crate::transformer::UpvalueOperand::Upvalue(u)
                        if self.proto.environment_upvalues.contains(&u)
                )
        )
    }

    fn is_const_string_reg(&self, use_iref: InstrRef, reg: Reg, expected: &str) -> bool {
        let ssa = &self.analysis.ssa;
        let Some(val) = ssa.instr_use_value(use_iref, reg) else {
            return false;
        };
        let SsaDef::Instr {
            instr: def_iref, ..
        } = ssa.def_of(val)
        else {
            return false;
        };
        matches!(
            &self.proto.instrs[def_iref.index()],
            LowInstr::LoadConst(lc) if self.const_string_utf8(lc.value).as_deref() == Some(expected)
        )
    }

    fn flush_pending_global_init(&mut self, out: &mut Vec<AstStmt>) {
        if let Some(pgi) = self.pending_global_init.take() {
            if let Some((_, env_local)) = pgi.local_env {
                self.lexical_environment_local = Some(env_local);
            }
            self.flush_all_pending(out);
            out.push(AstStmt::GlobalDecl(Box::new(AstGlobalDecl {
                bindings: vec![AstGlobalBinding {
                    target: AstGlobalBindingTarget::Name(AstGlobalName { text: pgi.name }),
                    attr: AstGlobalAttr::None,
                }],
                values: vec![AstExpr::Nil],
            })));
        }
    }

    /// 在 `Close(Explicit { from })` 边界处，将当前块中由该 `Close` 关闭的捕获/`<close>` 局部作用域
    /// 打包进 `AstStmt::DoBlock`，以在所有方言上精确还原关闭时序与 `debug.sethook` / `debug.getlocal` 离域边界。
    fn wrap_explicit_close_scope(&mut self, iref: InstrRef, from: Reg, out: &mut Vec<AstStmt>) {
        if out.is_empty() {
            return;
        }
        let mut closed_locals = BTreeSet::new();
        for (idx, slot_opt) in self.local_slots.iter().enumerate() {
            let Some(slot) = *slot_opt else {
                continue;
            };
            if slot.reg.index() < from.index() {
                continue;
            }
            let close_epoch = self.analysis.ssa.slot_at(iref, slot.reg).epoch;
            if slot.epoch != close_epoch {
                continue;
            }
            let local = LocalId(idx);
            if self.tbc_locals.contains(&local) || self.ref_captured_locals.contains(&local) {
                closed_locals.insert(local);
            }
        }
        if closed_locals.is_empty() {
            return;
        }
        let start_idx = out
            .iter()
            .position(|s| stmt_defines_any_local(s, &closed_locals))
            .or_else(|| {
                out.iter()
                    .position(|s| stmt_references_any_local(s, &closed_locals))
            });
        let Some(start) = start_idx else {
            return;
        };
        // 若 `closed_locals` 的定义已完全位于一个已闭合的 `DoBlock` 且其后无新赋值/声明（如平铺不可规约 SCC 中前一条同槽 `Close` 已收口），
        // 不再重复套娃一层外包 `DoBlock`（防止 `close_04` 重编译产生 `do do ... end ... end` 震荡）。
        if matches!(&out[start], AstStmt::DoBlock(_))
            && !out[start + 1..].iter().any(|s| {
                stmt_references_any_local(s, &closed_locals)
                    || matches!(s, AstStmt::Assign(_) | AstStmt::LocalDecl(_))
            })
        {
            return;
        }
        let labels_in_slice = collect_labels_in_stmts(&out[start..]);
        if !labels_in_slice.is_empty() {
            // 只要切片内任意标签存在位于切片外部（无论在 `out[..start]` 之前，还是尚未提升的后续块中）的 `goto`，
            // 就绝不能提前包裹 `DoBlock`，否则外部 `goto` 会跨作用域不可见（如 Lua 5.5 不可规约 `<close>` 环 `close_04`）。
            let inside_gotos = count_gotos_in_stmts(&out[start..], &labels_in_slice);
            let has_external_goto = labels_in_slice.iter().any(|lbl| {
                let inside = inside_gotos.get(lbl).copied().unwrap_or(0);
                let total = self.total_gotos_by_label.get(&lbl.0).copied().unwrap_or(0);
                inside < total
            }) || out[..start]
                .iter()
                .any(|s| stmt_has_goto_to_any(s, &labels_in_slice));
            if has_external_goto {
                return;
            }
        }
        let stmts: Vec<AstStmt> = out.drain(start..).collect();
        out.push(AstStmt::DoBlock(Box::new(AstBlock { stmts })));
        if let Some(slot) = self.block_last_close_len.last_mut() {
            *slot = Some(out.len());
        }
    }

    /// 在 `Return` 指令处，若保留了源码 `DebugLocal` 信息且当前块中已有局部的 `end_pc <= ret_pc`
    /// （如 LuaJIT `UCLO 0 + RET0` 或 Lua 5.4/5.5 末尾显式 `do local inner = ... end` 在 `return` 前离域），
    /// 且这些局部未被 `Return.values` 引用，则将其作用域包进 `AstStmt::DoBlock` 以保住 `"return"` hook 可观测性。
    fn wrap_tail_debug_closed_scope(
        &mut self,
        ret_iref: InstrRef,
        ret_values: &[AstExpr],
        out: &mut Vec<AstStmt>,
    ) {
        if out.is_empty() || self.proto.debug_locals.is_empty() {
            return;
        }
        let Some(&ret_pc) = self
            .proto
            .lowering_map
            .pc_map()
            .get(ret_iref.index())
            .and_then(|pcs| pcs.iter().min())
        else {
            return;
        };
        let mut closed_locals = BTreeSet::new();
        for (idx, slot_opt) in self.local_slots.iter().enumerate() {
            let Some(slot) = *slot_opt else {
                continue;
            };
            let local = LocalId(idx);
            let name = AstNameRef::Local(local);
            if ret_values.iter().any(|v| expr_mentions_name(v, &name)) {
                continue;
            }
            let ended_before_ret = self.proto.debug_locals.iter().any(|dl| {
                dl.is_source()
                    && dl.reg == slot.reg
                    && dl.start_pc < dl.end_pc
                    && dl.end_pc <= ret_pc
                    && self
                        .local_debug_hints
                        .get(idx)
                        .and_then(Option::as_deref)
                        .is_some_and(|h| h.as_bytes() == dl.name.bytes.as_ref())
            });
            if ended_before_ret {
                closed_locals.insert(local);
            }
        }
        if closed_locals.is_empty() {
            return;
        }
        let Some(start) = out
            .iter()
            .position(|s| stmt_defines_any_local(s, &closed_locals))
        else {
            return;
        };
        let labels_in_slice = collect_labels_in_stmts(&out[start..]);
        if !labels_in_slice.is_empty() {
            // 只要切片内任意标签存在位于切片外部（无论在 `out[..start]` 之前，还是尚未提升的后续块中）的 `goto`，
            // 就绝不能提前包裹 `DoBlock`，否则外部 `goto` 会跨作用域不可见（如 Lua 5.5 不可规约 `<close>` 环 `close_04`）。
            let inside_gotos = count_gotos_in_stmts(&out[start..], &labels_in_slice);
            let has_external_goto = labels_in_slice.iter().any(|lbl| {
                let inside = inside_gotos.get(lbl).copied().unwrap_or(0);
                let total = self.total_gotos_by_label.get(&lbl.0).copied().unwrap_or(0);
                inside < total
            }) || out[..start]
                .iter()
                .any(|s| stmt_has_goto_to_any(s, &labels_in_slice));
            if has_external_goto {
                return;
            }
        }
        let stmts: Vec<AstStmt> = out.drain(start..).collect();
        out.push(AstStmt::DoBlock(Box::new(AstBlock { stmts })));
    }

    fn lift_closure(
        &mut self,
        iref: InstrRef,
        closure: &crate::transformer::ClosureInstr,
        out: &mut Vec<AstStmt>,
    ) -> AstExpr {
        let shared_plan = match closure.creation {
            ClosureCreation::Reusable(slot) => self
                .shared_reusable_closures
                .get(&(closure.proto.index(), slot))
                .cloned()
                .map(|plan| ((closure.proto.index(), slot), plan)),
            ClosureCreation::Fresh => None,
        };

        // 若该共享闭包此前已完成提升构造，直接复用共享变量或调用词法工厂，绝不重复冲刷/声明
        if let Some((key, plan)) = &shared_plan
            && self.hoisted_shared_emitted.contains(key)
        {
            return match plan.kind {
                SharedClosureHoistKind::Direct => AstExpr::Var(AstNameRef::Local(plan.local)),
                SharedClosureHoistKind::FactoryWrapper => AstExpr::Call(Box::new(AstCallExpr {
                    callee: AstExpr::Var(AstNameRef::Local(plan.local)),
                    args: Vec::new(),
                })),
            };
        }

        // 冲刷被按引用或按值捕获的挂起寄存器，保证捕获绑定具有实体变量。
        let mut captures = Vec::with_capacity(closure.captures.len());
        let mut captured_bindings = BTreeSet::new();
        let mut captured_params = BTreeSet::new();
        let mut capture_write_names = BTreeSet::new();
        let mut dep_locals = BTreeSet::new();
        let is_luau_fresh = self.target.version == crate::decompile::DecompileDialect::Luau
            && self.proto_id != ProtoId(0)
            && matches!(closure.creation, ClosureCreation::Fresh);
        let child_lproto_for_writes = self
            .proto
            .children
            .get(closure.proto.index())
            .map(|p| p.as_ref());
        let child_writes_upvalue = |uv_idx: usize| -> bool {
            child_lproto_for_writes.is_some_and(|cp| {
                cp.instrs.iter().any(|ins| {
                    matches!(
                        ins,
                        LowInstr::SetUpvalue(su)
                            if matches!(
                                su.dst,
                                crate::transformer::UpvalueOperand::Upvalue(u)
                                    | crate::transformer::UpvalueOperand::Env(u)
                                    if u.index() == uv_idx
                            )
                    )
                })
            })
        };

        for (cap_idx, cap) in closure.captures.iter().enumerate() {
            // 若该捕获槽位经由已直接提升的共享闭包传导而来，直接捕获其共享 LocalId
            if let Some((_, plan)) = &shared_plan
                && let Some(&dep_local) = plan.hoisted_cap_locals.get(&cap_idx)
            {
                captured_bindings.insert(AstBindingRef::Local(dep_local));
                dep_locals.insert(dep_local);
                captures.push(AstCapture {
                    binding: AstCaptureBinding::Local(dep_local),
                    mode: AstCaptureMode::ByValue,
                });
                continue;
            }
            match cap.source {
                CaptureSource::ByReference(reg) => {
                    let name = if reg == closure.dst {
                        // 自捕获（如 Luau `local function f() ... f() end`）：绑定到本闭包自身的定值槽！
                        self.name_for_def_at(iref, reg)
                    } else {
                        self.flush_pending_for_reg(reg, out);
                        self.name_for_use_at(iref, reg)
                    };
                    let binding = match name {
                        AstNameRef::Param(p) => {
                            captured_params.insert(p);
                            capture_write_names.insert(AstNameRef::Param(p));
                            AstCaptureBinding::Param(p)
                        }
                        AstNameRef::Local(l) => {
                            captured_bindings.insert(AstBindingRef::Local(l));
                            capture_write_names.insert(AstNameRef::Local(l));
                            self.ref_captured_locals.insert(l);
                            dep_locals.insert(l);
                            if is_luau_fresh
                                && !child_writes_upvalue(cap_idx)
                                && self.is_const_literal_use(iref, reg)
                            {
                                self.luau_fresh_const_capture_locals.insert(l);
                            }
                            AstCaptureBinding::Local(l)
                        }
                        AstNameRef::SyntheticLocal(s) => {
                            captured_bindings.insert(AstBindingRef::SyntheticLocal(s));
                            capture_write_names.insert(AstNameRef::SyntheticLocal(s));
                            AstCaptureBinding::SyntheticLocal(s)
                        }
                        _ => continue,
                    };
                    captures.push(AstCapture {
                        binding,
                        mode: AstCaptureMode::ByReference,
                    });
                }
                CaptureSource::ByValue(reg) => {
                    let name = if reg == closure.dst {
                        // Luau `CAPTURE VAL dst` 自捕获：绑定到本闭包自身定值槽，绝不读取指令前旧寄存器值！
                        self.name_for_def_at(iref, reg)
                    } else {
                        self.flush_pending_for_reg(reg, out);
                        self.name_for_use_at(iref, reg)
                    };
                    let binding = match name {
                        AstNameRef::Param(p) => {
                            captured_params.insert(p);
                            AstCaptureBinding::Param(p)
                        }
                        AstNameRef::Local(l) => {
                            captured_bindings.insert(AstBindingRef::Local(l));
                            dep_locals.insert(l);
                            if is_luau_fresh
                                && !child_writes_upvalue(cap_idx)
                                && self.is_const_literal_use(iref, reg)
                            {
                                self.luau_fresh_const_capture_locals.insert(l);
                            }
                            AstCaptureBinding::Local(l)
                        }
                        AstNameRef::SyntheticLocal(s) => {
                            captured_bindings.insert(AstBindingRef::SyntheticLocal(s));
                            AstCaptureBinding::SyntheticLocal(s)
                        }
                        _ => continue,
                    };
                    captures.push(AstCapture {
                        binding,
                        mode: AstCaptureMode::ByValue,
                    });
                }
                CaptureSource::Upvalue(u) => {
                    captures.push(AstCapture {
                        binding: AstCaptureBinding::Upvalue(UpvalueId(u.index())),
                        mode: AstCaptureMode::ByReference,
                    });
                }
            }
        }

        let child_orig_idx = self
            .analysis
            .children
            .get(closure.proto.index())
            .copied()
            .unwrap_or(self.proto_id.index());
        let child_lproto = self
            .proto
            .children
            .get(closure.proto.index())
            .map(|p| p.as_ref());

        let (params, is_vararg) = if let Some(cp) = child_lproto {
            (
                (0..usize::from(cp.signature.num_params))
                    .map(ParamId)
                    .collect(),
                cp.signature.is_vararg,
            )
        } else {
            (Vec::new(), false)
        };

        if let Some((key, plan)) = shared_plan {
            self.hoisted_shared_emitted.insert(key);
            match plan.kind {
                SharedClosureHoistKind::Direct => {
                    let child_id =
                        self.proto_registry
                            .claim_child(child_orig_idx, self.proto_id, captures);
                    let func_expr = AstFunctionExpr {
                        function: child_id,
                        params,
                        is_vararg,
                        named_vararg: None,
                        body: AstBlock::default(),
                        captured_bindings,
                        captured_params,
                        capture_write_names,
                    };
                    self.hoisted_shared_closures.push(HoistedSharedClosure {
                        local: plan.local,
                        func: func_expr,
                        dep_locals,
                    });
                    return AstExpr::Var(AstNameRef::Local(plan.local));
                }
                SharedClosureHoistKind::FactoryWrapper => {
                    let wrapper_func = self.proto_registry.alloc_synthetic_factory(
                        self.proto_id,
                        captures,
                        child_orig_idx,
                        params,
                        is_vararg,
                        captured_bindings,
                        captured_params,
                    );
                    self.hoisted_shared_closures.push(HoistedSharedClosure {
                        local: plan.local,
                        func: wrapper_func,
                        dep_locals,
                    });
                    return AstExpr::Call(Box::new(AstCallExpr {
                        callee: AstExpr::Var(AstNameRef::Local(plan.local)),
                        args: Vec::new(),
                    }));
                }
            }
        }

        let child_id = self
            .proto_registry
            .claim_child(child_orig_idx, self.proto_id, captures);
        let func_expr = AstFunctionExpr {
            function: child_id,
            params,
            is_vararg,
            named_vararg: None,
            body: AstBlock::default(),
            captured_bindings,
            captured_params,
            capture_write_names,
        };

        AstExpr::FunctionExpr(Box::new(func_expr))
    }

    fn is_const_literal_use(&self, iref: InstrRef, reg: Reg) -> bool {
        let Some(val) = self.analysis.ssa.instr_use_value(iref, reg) else {
            return false;
        };
        let SsaDef::Instr { instr: def_iref, .. } = self.analysis.ssa.def_of(val) else {
            return false;
        };
        matches!(
            self.proto.instrs[def_iref.index()],
            LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
                | LowInstr::LoadConst(_)
        )
    }
}

fn stmt_declares_local(stmt: &AstStmt, target: LocalId) -> bool {
    match stmt {
        AstStmt::LocalDecl(d) => d
            .bindings
            .iter()
            .any(|b| b.id == AstBindingRef::Local(target)),
        AstStmt::LocalFunctionDecl(d) => d.name == AstBindingRef::Local(target),
        _ => false,
    }
}

fn insert_hoisted_decl_after_deps(
    block: &mut AstBlock,
    decl: &AstStmt,
    deps: &BTreeSet<LocalId>,
) -> bool {
    if deps.is_empty() {
        block.stmts.insert(0, decl.clone());
        return true;
    }
    let mut found_count = 0usize;
    let mut insert_pos = 0usize;
    for (idx, stmt) in block.stmts.iter().enumerate() {
        for &dep in deps {
            if stmt_declares_local(stmt, dep) {
                found_count += 1;
                insert_pos = insert_pos.max(idx + 1);
            }
        }
    }
    if found_count >= deps.len() {
        block.stmts.insert(insert_pos, decl.clone());
        return true;
    }
    // 否则尝试递归进入子块（例如依赖局部变量声明在某嵌套 `do`/`if` 块内）
    for stmt in &mut block.stmts {
        match stmt {
            AstStmt::DoBlock(b) => {
                if insert_hoisted_decl_after_deps(b, decl, deps) {
                    return true;
                }
            }
            AstStmt::If(i) => {
                if insert_hoisted_decl_after_deps(&mut i.then_block, decl, deps) {
                    return true;
                }
                if let Some(eb) = &mut i.else_block
                    && insert_hoisted_decl_after_deps(eb, decl, deps)
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn collect_assigned_locals_in_block(block: &AstBlock, out: &mut BTreeSet<LocalId>) {
    for stmt in &block.stmts {
        match stmt {
            AstStmt::Assign(a) => {
                for t in &a.targets {
                    if let AstLValue::Name(AstNameRef::Local(l)) = t {
                        out.insert(*l);
                    }
                }
            }
            AstStmt::If(i) => {
                collect_assigned_locals_in_block(&i.then_block, out);
                if let Some(eb) = &i.else_block {
                    collect_assigned_locals_in_block(eb, out);
                }
            }
            AstStmt::While(w) => collect_assigned_locals_in_block(&w.body, out),
            AstStmt::Repeat(r) => collect_assigned_locals_in_block(&r.body, out),
            AstStmt::NumericFor(nf) => collect_assigned_locals_in_block(&nf.body, out),
            AstStmt::GenericFor(gf) => collect_assigned_locals_in_block(&gf.body, out),
            AstStmt::DoBlock(b) => collect_assigned_locals_in_block(b, out),
            _ => {}
        }
    }
}

fn is_pure_const_literal_expr(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Nil
            | AstExpr::Boolean(_)
            | AstExpr::Integer(_)
            | AstExpr::Number(_)
            | AstExpr::String(_)
    )
}

fn inject_luau_fresh_const_guards_in_block(block: &mut AstBlock, targets: &BTreeSet<LocalId>) {
    let mut i = 0usize;
    while i < block.stmts.len() {
        let mut guard_locals = Vec::new();
        match &mut block.stmts[i] {
            AstStmt::LocalDecl(d) => {
                for (bi, b) in d.bindings.iter().enumerate() {
                    if let AstBindingRef::Local(l) = b.id
                        && targets.contains(&l)
                        && d.values
                            .get(bi)
                            .is_none_or(is_pure_const_literal_expr)
                    {
                        guard_locals.push(l);
                    }
                }
            }
            AstStmt::If(if_stmt) => {
                inject_luau_fresh_const_guards_in_block(&mut if_stmt.then_block, targets);
                if let Some(eb) = &mut if_stmt.else_block {
                    inject_luau_fresh_const_guards_in_block(eb, targets);
                }
            }
            AstStmt::While(w) => inject_luau_fresh_const_guards_in_block(&mut w.body, targets),
            AstStmt::Repeat(r) => inject_luau_fresh_const_guards_in_block(&mut r.body, targets),
            AstStmt::NumericFor(nf) => {
                inject_luau_fresh_const_guards_in_block(&mut nf.body, targets)
            }
            AstStmt::GenericFor(gf) => {
                inject_luau_fresh_const_guards_in_block(&mut gf.body, targets)
            }
            AstStmt::DoBlock(b) => inject_luau_fresh_const_guards_in_block(b, targets),
            _ => {}
        }
        i += 1;
        for l in guard_locals {
            block.stmts.insert(
                i,
                AstStmt::If(Box::new(AstIf {
                    cond: AstExpr::Boolean(false),
                    then_block: AstBlock {
                        stmts: vec![AstStmt::Assign(Box::new(AstAssign {
                            targets: vec![AstLValue::Name(AstNameRef::Local(l))],
                            values: vec![AstExpr::Nil],
                            compound_op: None,
                        }))],
                    },
                    else_block: None,
                })),
            );
            i += 1;
        }
    }
}

fn cond_anchor_instr(cond: &CondExpr, analysis: &ProtoAnalysis) -> Option<InstrRef> {
    match cond {
        CondExpr::Atom { block, .. } => analysis.cfg.blocks[block.index()].instrs.last(),
        CondExpr::Not(inner) => cond_anchor_instr(inner, analysis),
        CondExpr::And(a, _) | CondExpr::Or(a, _) => cond_anchor_instr(a, analysis),
        CondExpr::True | CondExpr::False => None,
    }
}

pub(super) fn map_binary_op(op: crate::transformer::BinaryOpKind) -> AstBinaryOpKind {
    use crate::transformer::BinaryOpKind as T;
    match op {
        T::Add => AstBinaryOpKind::Add,
        T::Sub => AstBinaryOpKind::Sub,
        T::Mul => AstBinaryOpKind::Mul,
        T::Div => AstBinaryOpKind::Div,
        T::FloorDiv => AstBinaryOpKind::FloorDiv,
        T::Mod => AstBinaryOpKind::Mod,
        T::Pow => AstBinaryOpKind::Pow,
        T::BitAnd => AstBinaryOpKind::BitAnd,
        T::BitOr => AstBinaryOpKind::BitOr,
        T::BitXor => AstBinaryOpKind::BitXor,
        T::Shl => AstBinaryOpKind::Shl,
        T::Shr => AstBinaryOpKind::Shr,
    }
}

pub(super) fn expr_is_multi_return(expr: &AstExpr) -> bool {
    matches!(
        expr,
        AstExpr::Call(_) | AstExpr::MethodCall(_) | AstExpr::VarArg
    )
}

/// 当单结果调用/变参落在 Lua 多值展开尾位置时，补 `(expr)` 单值截断。
pub(super) fn wrap_single_value_if_needed(expr: AstExpr) -> AstExpr {
    if expr_is_multi_return(&expr) {
        AstExpr::SingleValue(Box::new(expr))
    } else {
        expr
    }
}

/// 检查 `expr` 是否引用了指定寄存器对应的变量名（仅对具名读写生效）。
pub(super) fn expr_mentions_name(expr: &AstExpr, target: &AstNameRef) -> bool {
    use super::visit::{ExprNode, expr_nodes};
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(AstExpr::Var(name)) = node
            && name == target
        {
            return true;
        }
    }
    false
}

/// 检查表达式是否可能产生可观察副作用（含调用、表索引/元方法或算术/比较元方法）。
pub(super) fn expr_may_have_side_effect(expr: &AstExpr) -> bool {
    use super::visit::{ExprNode, expr_nodes};
    for node in expr_nodes(expr) {
        if let ExprNode::Expr(e) = node {
            match e {
                AstExpr::Call(_)
                | AstExpr::MethodCall(_)
                | AstExpr::FieldAccess(_)
                | AstExpr::IndexAccess(_)
                | AstExpr::Binary(_) => return true,
                AstExpr::Unary(u)
                    if !matches!(u.op, super::common::AstUnaryOpKind::Not) =>
                {
                    return true;
                }
                _ => {}
            }
        }
    }
    false
}

/// 判断一个 `NewTable` 预分配形态是否允许把紧随其后的 `SetTable` 吸收进表构造器。
///
/// PUC Lua 5.1~5.5 源码写 `{}` 时预分配 `array_capacity == 0 && hash_capacity == 0`，
/// 写 `{ a = 1 }` 或 `{ [1] = 2 }` 时必有 `hash_capacity > 0`；不向空 `{}` 强塞 `SetTable`
/// 既保留了原表的动态数组扩容历史（影响 `#t` 行为），也避免了把 `local t = {}; t.a = 1` 错误合并。
pub(super) fn table_accepts_set_table(alloc: &crate::transformer::TableAllocation) -> bool {
    match alloc {
        crate::transformer::TableAllocation::PucBatched(cap) => cap.hash_capacity > 0,
        crate::transformer::TableAllocation::Luau(cap) => {
            cap.hash_capacity > 0 || cap.array_capacity > 0
        }
        crate::transformer::TableAllocation::Indexed {
            array_capacity,
            hash_bits,
        } => *array_capacity > 0 || *hash_bits > 0,
        crate::transformer::TableAllocation::LuauTemplate(_)
        | crate::transformer::TableAllocation::Template(_) => true,
    }
}

/// 清理 `return` / `break` 后的不可达死语句（满足 Lua 5.1 块尾终结符语法约束），
/// 但绝不删除后续任何 `AstStmt::Label(_)` 及其后的可达代码（Lua 5.2+/LuaJIT 可由外部 `goto` 跳入！）。
fn truncate_unreachable_after_terminator(stmts: &mut Vec<AstStmt>) {
    let mut i = 0;
    while i < stmts.len() {
        if matches!(stmts[i], AstStmt::Return(_) | AstStmt::Break) {
            let dead_start = i + 1;
            let next_label = stmts[dead_start..]
                .iter()
                .position(|s| matches!(s, AstStmt::Label(_)))
                .map(|off| dead_start + off)
                .unwrap_or(stmts.len());
            if next_label > dead_start {
                stmts.drain(dead_start..next_label);
            }
        }
        i += 1;
    }
}

/// 判断 AST 表达式是否必然求值为严格布尔值（`true`/`false`），用于 `BoolAssign` 避免多余或缺失 `not not`。
fn expr_is_guaranteed_bool(expr: &AstExpr) -> bool {
    match expr {
        AstExpr::Boolean(_) => true,
        AstExpr::Unary(u) => u.op == super::common::AstUnaryOpKind::Not,
        AstExpr::Binary(b) => matches!(
            b.op,
            AstBinaryOpKind::Eq
                | AstBinaryOpKind::Lt
                | AstBinaryOpKind::Le
                | AstBinaryOpKind::Gt
                | AstBinaryOpKind::Ge
        ),
        AstExpr::LogicalAnd(l) | AstExpr::LogicalOr(l) => {
            expr_is_guaranteed_bool(&l.lhs) && expr_is_guaranteed_bool(&l.rhs)
        }
        _ => false,
    }
}

/// 判断语句是否直接向 `locals` 中任一局部写入（用于定位 `Close(Explicit)` 作用域起点）。
fn stmt_defines_any_local(stmt: &AstStmt, locals: &BTreeSet<LocalId>) -> bool {
    match stmt {
        AstStmt::Assign(a) => a
            .targets
            .iter()
            .any(|t| matches!(t, AstLValue::Name(AstNameRef::Local(l)) if locals.contains(l))),
        AstStmt::LocalDecl(d) => d
            .bindings
            .iter()
            .any(|b| matches!(b.id, AstBindingRef::Local(l) if locals.contains(&l))),
        AstStmt::LocalFunctionDecl(d) => {
            matches!(d.name, AstBindingRef::Local(l) if locals.contains(&l))
        }
        _ => false,
    }
}

/// 判断语句是否读取或通过闭包捕获了 `locals` 中任一局部。
fn stmt_references_any_local(stmt: &AstStmt, locals: &BTreeSet<LocalId>) -> bool {
    let mut found = false;
    let check_expr = |e: &AstExpr, found: &mut bool| {
        if *found {
            return;
        }
        for node in super::visit::expr_nodes(e) {
            match node {
                super::visit::ExprNode::Expr(AstExpr::Var(AstNameRef::Local(l)))
                    if locals.contains(l) =>
                {
                    *found = true;
                    break;
                }
                super::visit::ExprNode::Function(f)
                    if f.captured_bindings
                        .iter()
                        .any(|b| matches!(b, AstBindingRef::Local(l) if locals.contains(l))) =>
                {
                    *found = true;
                    break;
                }
                _ => {}
            }
        }
    };
    match stmt {
        AstStmt::Assign(a) => {
            for t in &a.targets {
                if let AstLValue::Name(AstNameRef::Local(l)) = t
                    && locals.contains(l)
                {
                    return true;
                }
            }
            for v in &a.values {
                check_expr(v, &mut found);
            }
        }
        AstStmt::LocalDecl(d) => {
            for v in &d.values {
                check_expr(v, &mut found);
            }
        }
        AstStmt::CallStmt(c) => match &c.call {
            super::common::AstCallKind::Call(call) => {
                check_expr(&call.callee, &mut found);
                for a in &call.args {
                    check_expr(a, &mut found);
                }
            }
            super::common::AstCallKind::MethodCall(m) => {
                check_expr(&m.receiver, &mut found);
                for a in &m.args {
                    check_expr(a, &mut found);
                }
            }
        },
        AstStmt::Return(r) => {
            for v in &r.values {
                check_expr(v, &mut found);
            }
        }
        AstStmt::DoBlock(b) => return b.stmts.iter().any(|s| stmt_references_any_local(s, locals)),
        AstStmt::If(i) => {
            check_expr(&i.cond, &mut found);
            if !found {
                found = i
                    .then_block
                    .stmts
                    .iter()
                    .any(|s| stmt_references_any_local(s, locals))
                    || i.else_block.as_ref().is_some_and(|eb| {
                        eb.stmts.iter().any(|s| stmt_references_any_local(s, locals))
                    });
            }
        }
        AstStmt::FunctionDecl(d) => {
            found = d
                .func
                .captured_bindings
                .iter()
                .any(|b| matches!(b, AstBindingRef::Local(l) if locals.contains(l)));
        }
        AstStmt::LocalFunctionDecl(d) => {
            found = d
                .func
                .captured_bindings
                .iter()
                .any(|b| matches!(b, AstBindingRef::Local(l) if locals.contains(l)));
        }
        _ => {}
    }
    found
}

/// 收集语句切片子树内定义的所有 `AstLabelId`。
fn collect_labels_in_stmts(stmts: &[AstStmt]) -> BTreeSet<AstLabelId> {
    let mut out = BTreeSet::new();
    fn visit(stmt: &AstStmt, out: &mut BTreeSet<AstLabelId>) {
        match stmt {
            AstStmt::Label(l) => {
                out.insert(l.id);
            }
            AstStmt::DoBlock(b) => b.stmts.iter().for_each(|s| visit(s, out)),
            AstStmt::If(i) => {
                i.then_block.stmts.iter().for_each(|s| visit(s, out));
                if let Some(eb) = &i.else_block {
                    eb.stmts.iter().for_each(|s| visit(s, out));
                }
            }
            AstStmt::While(w) => w.body.stmts.iter().for_each(|s| visit(s, out)),
            AstStmt::Repeat(r) => r.body.stmts.iter().for_each(|s| visit(s, out)),
            AstStmt::NumericFor(nf) => nf.body.stmts.iter().for_each(|s| visit(s, out)),
            AstStmt::GenericFor(gf) => gf.body.stmts.iter().for_each(|s| visit(s, out)),
            _ => {}
        }
    }
    for s in stmts {
        visit(s, &mut out);
    }
    out
}

/// 统计控制流 `Region` 树中每个 `Region::Goto(label)` 的出现总次数。
fn count_region_gotos(region: &Region, counts: &mut BTreeMap<usize, usize>) {
    match region {
        Region::Goto(lbl) => {
            *counts.entry(*lbl).or_insert(0) += 1;
        }
        Region::Sequence(items) => {
            for item in items {
                count_region_gotos(item, counts);
            }
        }
        Region::If {
            then_body,
            else_body,
            ..
        } => {
            count_region_gotos(then_body, counts);
            if let Some(eb) = else_body {
                count_region_gotos(eb, counts);
            }
        }
        Region::While { body, .. }
        | Region::Repeat { body, .. }
        | Region::NumericFor { body, .. }
        | Region::GenericFor { body, .. }
        | Region::DoScope(body)
        | Region::Labeled(_, body) => count_region_gotos(body, counts),
        Region::Empty
        | Region::Block(_)
        | Region::BlockPrefix(_)
        | Region::BlockSlice { .. }
        | Region::BoolAssign { .. }
        | Region::Break
        | Region::Continue
        | Region::StateMachine { .. } => {}
    }
}

/// 统计语句切片子树内指向 `targets` 中各标签的 `AstStmt::Goto` 次数。
fn count_gotos_in_stmts(
    stmts: &[AstStmt],
    targets: &BTreeSet<AstLabelId>,
) -> BTreeMap<AstLabelId, usize> {
    let mut counts = BTreeMap::new();
    fn visit(
        stmt: &AstStmt,
        targets: &BTreeSet<AstLabelId>,
        counts: &mut BTreeMap<AstLabelId, usize>,
    ) {
        match stmt {
            AstStmt::Goto(g) if targets.contains(&g.target) => {
                *counts.entry(g.target).or_insert(0) += 1;
            }
            AstStmt::DoBlock(b) => b.stmts.iter().for_each(|s| visit(s, targets, counts)),
            AstStmt::If(i) => {
                i.then_block
                    .stmts
                    .iter()
                    .for_each(|s| visit(s, targets, counts));
                if let Some(eb) = &i.else_block {
                    eb.stmts.iter().for_each(|s| visit(s, targets, counts));
                }
            }
            AstStmt::While(w) => w.body.stmts.iter().for_each(|s| visit(s, targets, counts)),
            AstStmt::Repeat(r) => r.body.stmts.iter().for_each(|s| visit(s, targets, counts)),
            AstStmt::NumericFor(nf) => nf.body.stmts.iter().for_each(|s| visit(s, targets, counts)),
            AstStmt::GenericFor(gf) => gf.body.stmts.iter().for_each(|s| visit(s, targets, counts)),
            _ => {}
        }
    }
    for s in stmts {
        visit(s, targets, &mut counts);
    }
    counts
}

/// 检查语句子树内是否存在跳向 `targets` 中任一标签的 `AstStmt::Goto`。
fn stmt_has_goto_to_any(stmt: &AstStmt, targets: &BTreeSet<AstLabelId>) -> bool {
    match stmt {
        AstStmt::Goto(g) => targets.contains(&g.target),
        AstStmt::DoBlock(b) => b.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)),
        AstStmt::If(i) => {
            i.then_block
                .stmts
                .iter()
                .any(|s| stmt_has_goto_to_any(s, targets))
                || i.else_block
                    .as_ref()
                    .is_some_and(|eb| eb.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)))
        }
        AstStmt::While(w) => w.body.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)),
        AstStmt::Repeat(r) => r.body.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)),
        AstStmt::NumericFor(nf) => nf.body.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)),
        AstStmt::GenericFor(gf) => gf.body.stmts.iter().any(|s| stmt_has_goto_to_any(s, targets)),
        _ => false,
    }
}

/// 计算指令 `instr` 执行完毕后下一条字节码的精确 PC。
///
/// Lua 5.4 / Lua 5.5 的 `NEWTABLE` 等双字指令后紧跟 `EXTRAARG`（占 2 个 PC），
/// 若仅取 `max_pc + 1` 会落在 `EXTRAARG` 槽上而错过 `DebugLocal.start_pc`；
/// 取同块下一条 LIR 指令的首 PC（若更大）即可精准对齐所有方言的 `start_pc`！
fn after_instr_pc(proto: &LoweredProto, analysis: &ProtoAnalysis, instr: InstrRef) -> Option<u32> {
    let pc_map = proto.lowering_map.pc_map();
    let max_pc = pc_map
        .get(instr.index())
        .and_then(|pcs| pcs.iter().max().copied())?;
    let mut next_pc = max_pc.saturating_add(1);
    if let Some(block) = analysis
        .cfg
        .block_of_instr
        .get(instr.index())
        .copied()
        .flatten()
    {
        let range = analysis.cfg.blocks[block.index()].instrs;
        let next_idx = instr.index() + 1;
        if next_idx < range.start.index() + range.len
            && let Some(&next_min) = pc_map.get(next_idx).and_then(|pcs| pcs.iter().min())
            && next_min > next_pc
        {
            next_pc = next_min;
        }
    }
    Some(next_pc)
}

/// 获取 SSA 值对应的物理槽位 `(Reg, epoch)`。
fn ssa_value_slot(ssa: &crate::analysis::SsaForm, val: ValueId) -> Option<SlotKey> {
    match ssa.defs.get(val.index())? {
        SsaDef::Param { reg, .. }
        | SsaDef::VarArgParam { reg }
        | SsaDef::Undef { reg } => Some(SlotKey { reg: *reg, epoch: 0 }),
        SsaDef::Instr { slot, .. } | SsaDef::Phi { slot, .. } => Some(*slot),
    }
}

/// 轻量级 SSA Web 拆分（Union-Find over `ValueId`）。
///
/// 合并必须共享同一源码变量的 SSA 值（Phi 连通、pinned/tbc 槽位、循环控制变量、
/// 同一源码 `DebugLocal` 作用域、单结果就地自更新 `x = x + 1` / `p = p.next`），
/// 使同一物理寄存器上互不重叠的生命周期（尤其是死槽复用与多返回接收槽）获得独立 `LocalId`；
/// 若 Web 数量超过安全阈值（140），自动退回按 `SlotKey` 合并以守住 Lua 200-local 上限。
fn build_ssa_webs(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    materialized_values: &mut BTreeSet<ValueId>,
) -> (Vec<usize>, BTreeMap<usize, String>, Vec<Option<BlockId>>) {
    let ssa = &analysis.ssa;
    let n = ssa.defs.len();
    let mut parent: Vec<usize> = (0..n).collect();

    fn find(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    fn union(parent: &mut [usize], a: usize, b: usize) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            if ra < rb {
                parent[rb] = ra;
            } else {
                parent[ra] = rb;
            }
        }
    }

    // 0. 精确标注所有属于 `NumericFor` / `GenericFor` 循环控制变量的 SSA 值（按所属循环的 `body_entry` 隔离）：
    //    循环头的 `body_entry` 支配整个循环体且绝不支配循环前/后任何块，从而用 O(1) 支配判定即可
    //    彻底隔离循环变量与循环外复用同一物理寄存器的普通局部变量。
    let mut for_binding_owners: Vec<Option<BlockId>> = vec![None; n];
    let mut for_binding_regs: Vec<(BlockId, Reg)> = Vec::new();
    for hint in &analysis.cfg.loop_protocols {
        match hint {
            crate::analysis::LoopProtocolHint::NumericFor {
                init_instr,
                body_entry,
                latch_blocks,
                binding,
                ..
            } => {
                for_binding_regs.push((*body_entry, *binding));
                if let Some(init_v) = ssa.instr_def_value(*init_instr, *binding) {
                    for_binding_owners[init_v.index()] = Some(*body_entry);
                }
                for &lb in latch_blocks {
                    if let Some(last_iref) = analysis.cfg.blocks[lb.index()].instrs.last()
                        && let Some(latch_v) = ssa.instr_def_value(last_iref, *binding)
                    {
                        for_binding_owners[latch_v.index()] = Some(*body_entry);
                    }
                }
            }
            crate::analysis::LoopProtocolHint::GenericFor {
                call_instr,
                loop_instr,
                body_entry,
                bindings,
                ..
            } => {
                for offset in 0..bindings.len {
                    let r = Reg(bindings.start.index() + offset);
                    for_binding_regs.push((*body_entry, r));
                    if let Some(dv) = ssa.instr_def_value(*call_instr, r) {
                        for_binding_owners[dv.index()] = Some(*body_entry);
                    }
                    if let Some(uv) = ssa.instr_use_value(*loop_instr, r) {
                        for_binding_owners[uv.index()] = Some(*body_entry);
                    }
                }
            }
        }
    }
    if !for_binding_regs.is_empty() {
        // 单遍支配树 DFS 传播 `for` 控制变量所属最内层 `body_entry`，将 O(V × L) 降为 O(B + V + L)！
        let block_count = analysis.cfg.blocks.len();
        let mut regs_by_entry: BTreeMap<BlockId, Vec<Reg>> = BTreeMap::new();
        for &(body_entry, breg) in &for_binding_regs {
            regs_by_entry.entry(body_entry).or_default().push(breg);
        }
        let mut defs_by_block: Vec<Vec<(usize, Reg)>> = vec![Vec::new(); block_count];
        for (vi, def) in ssa.defs.iter().enumerate() {
            if for_binding_owners[vi].is_some() {
                continue;
            }
            let (block, reg) = match *def {
                SsaDef::Instr { block, reg, .. } => (block, reg),
                SsaDef::Phi { block, slot, .. } => (block, slot.reg),
                _ => continue,
            };
            defs_by_block[block.index()].push((vi, reg));
        }
        let mut dom_children: Vec<Vec<BlockId>> = vec![Vec::new(); block_count];
        for (b_idx, parent_opt) in analysis.graph.dom.parent.iter().enumerate() {
            if let Some(parent) = *parent_opt
                && parent.index() != b_idx
            {
                dom_children[parent.index()].push(BlockId(b_idx));
            }
        }
        let mut active_owners: BTreeMap<Reg, Vec<BlockId>> = BTreeMap::new();
        // 显式栈遍历支配树（避免深度退化引发栈溢出）
        let mut stack: Vec<(BlockId, bool)> = vec![(analysis.cfg.entry_block, false)];
        while let Some((b, leaving)) = stack.pop() {
            if leaving {
                if let Some(regs) = regs_by_entry.get(&b) {
                    for &reg in regs {
                        if let Some(v) = active_owners.get_mut(&reg) {
                            v.pop();
                        }
                    }
                }
                continue;
            }
            if let Some(regs) = regs_by_entry.get(&b) {
                for &reg in regs {
                    active_owners.entry(reg).or_default().push(b);
                }
            }
            for &(vi, reg) in &defs_by_block[b.index()] {
                if let Some(owner) = active_owners.get(&reg).and_then(|v| v.last().copied()) {
                    for_binding_owners[vi] = Some(owner);
                }
            }
            stack.push((b, true));
            for &child in dom_children[b.index()].iter().rev() {
                stack.push((child, false));
            }
        }
    }

    // 1. 为每个指令定值查找精确覆盖其生效 PC 的源码 DebugLocal 下标（按寄存器预建索引避免 O(V × D) 线性扫描）
    let pc_map = proto.lowering_map.pc_map();
    let mut val_debug_idx: Vec<Option<usize>> = vec![None; n];
    let mut debug_group_rep: BTreeMap<(usize, Option<BlockId>), usize> = BTreeMap::new();
    let mut debug_locals_by_reg: BTreeMap<Reg, Vec<(usize, u32, u32)>> = BTreeMap::new();
    for (di, l) in proto.debug_locals.iter().enumerate() {
        if l.is_source() {
            debug_locals_by_reg
                .entry(l.reg)
                .or_default()
                .push((di, l.start_pc, l.end_pc));
        }
    }
    let find_debug_local = |reg: Reg, probe_pc: u32| -> Option<usize> {
        debug_locals_by_reg.get(&reg)?.iter().find_map(|&(di, s, e)| {
            (s <= probe_pc && probe_pc < e).then_some(di)
        })
    };
    // 块尾/函数尾最后一条语句声明的具名局部变量（如 `local BadConfig = require(...)` 后直接到 `end`）
    // 在 PUC Lua 中会记录零长度范围 `start_pc == end_pc == after_pc`；仅对指令定值精确点位匹配，避免波及后续块 Phi。
    let find_debug_local_at_def = |reg: Reg, after_pc: u32| -> Option<usize> {
        find_debug_local(reg, after_pc).or_else(|| {
            debug_locals_by_reg
                .get(&reg)?
                .iter()
                .find_map(|&(di, s, e)| (s == after_pc && e == after_pc).then_some(di))
        })
    };
    for (vi, def) in ssa.defs.iter().enumerate() {
        let mut dl_idx = match *def {
            SsaDef::Instr {
                instr, block, reg, ..
            } => {
                let Some(after_pc) = after_instr_pc(proto, analysis, instr) else {
                    continue;
                };
                let mut found_idx = find_debug_local(reg, after_pc).or_else(|| {
                    matches!(proto.instrs[instr.index()], LowInstr::Call(_))
                        .then(|| find_debug_local_at_def(reg, after_pc))
                        .flatten()
                });
                // Luau 多变量无初值声明 `local a, b, c` 会发射连续单槽 `LOADNIL`，但把所有变量的
                // `DebugLocal.start_pc` 统一记在最后一条 `LOADNIL` 之后；向前跨过同块连续 `LoadNil` 对齐归属。
                if found_idx.is_none()
                    && matches!(proto.instrs[instr.index()], LowInstr::LoadNil(_))
                {
                    let range = analysis.cfg.blocks[block.index()].instrs;
                    let mut cursor = instr.index() + 1;
                    while cursor < range.end()
                        && matches!(proto.instrs[cursor], LowInstr::LoadNil(_))
                    {
                        if let Some(u_after) = after_instr_pc(proto, analysis, InstrRef(cursor))
                            && let Some(found) = find_debug_local(reg, u_after)
                        {
                            found_idx = Some(found);
                            break;
                        }
                        cursor += 1;
                    }
                }
                // Lua 表构造器 `local t = { 1, 2, 3 }` / `local t = { a = 1 }` 的 DebugLocal.start_pc
                // 通常落在同块最后一条初始化 `SetList`/`SetTable` 之后。
                if found_idx.is_none()
                    && matches!(proto.instrs[instr.index()], LowInstr::NewTable(_))
                {
                    let mut init_after_pc = after_pc;
                    let mut ordered_uses = ssa.uses[vi].clone();
                    ordered_uses.sort_by_key(|u| match *u {
                        UseSite::Instr { instr: ui, .. } => ui.index(),
                        UseSite::Phi { .. } => usize::MAX,
                    });
                    for u in &ordered_uses {
                        let UseSite::Instr {
                            block: ub,
                            instr: ui,
                        } = *u
                        else {
                            break;
                        };
                        if ub != block {
                            break;
                        }
                        let is_ctor_write = matches!(
                            &proto.instrs[ui.index()],
                            LowInstr::SetList(sl) if sl.base == reg
                        ) || matches!(
                            &proto.instrs[ui.index()],
                            LowInstr::SetTable(st)
                                if st.base == crate::transformer::AccessBase::Reg(reg)
                        );
                        if !is_ctor_write {
                            break;
                        }
                        if let Some(u_after) = after_instr_pc(proto, analysis, ui) {
                            init_after_pc = init_after_pc.max(u_after);
                            if let Some(found) = find_debug_local(reg, init_after_pc) {
                                found_idx = Some(found);
                                break;
                            }
                        }
                    }
                }
                found_idx
            }
            // 布尔/条件合流初始化的源码局部（如 `local left = mask % 2 == 1`）：
            // 其 `DebugLocal.start_pc` 落在合流块 `join_block` 首指令 PC 处（Phi 定义点）；
            // 若是多局部声明 `local left, right = expr1, expr2`，`left` 的 `DebugLocal` 在 `expr2` 结束后才生效，
            // 此时检查所有使用点 PC 若一致落在同一 `DebugLocal`（且其 `start_pc >= def_pc`）内，同样精准归属！
            SsaDef::Phi { block, slot, .. } => {
                let def_pc = analysis.cfg.blocks[block.index()]
                    .instrs
                    .iter()
                    .next()
                    .and_then(|ir| pc_map.get(ir.index()))
                    .and_then(|pcs| pcs.iter().min().copied());
                let at_def = def_pc.and_then(|pc| find_debug_local(slot.reg, pc));
                if at_def.is_some() {
                    at_def
                } else if let Some(dpc) = def_pc {
                    let mut common_di: Option<usize> = None;
                    let mut valid = !ssa.uses[vi].is_empty();
                    for u in &ssa.uses[vi] {
                        let UseSite::Instr { instr: ui, .. } = *u else {
                            valid = false;
                            break;
                        };
                        if ssa.instr_use_value(ui, slot.reg) != Some(ValueId(vi)) {
                            valid = false;
                            break;
                        }
                        let Some(upc) = pc_map
                            .get(ui.index())
                            .and_then(|pcs| pcs.iter().min().copied())
                        else {
                            valid = false;
                            break;
                        };
                        let Some(di) = find_debug_local(slot.reg, upc) else {
                            valid = false;
                            break;
                        };
                        if proto.debug_locals[di].start_pc < dpc {
                            valid = false;
                            break;
                        }
                        if let Some(prev) = common_di {
                            if prev != di {
                                valid = false;
                                break;
                            }
                        } else {
                            common_di = Some(di);
                        }
                    }
                    if valid { common_di } else { None }
                } else {
                    None
                }
            }
            _ => continue,
        };
        if let Some(di) = dl_idx.take() {
            val_debug_idx[vi] = Some(di);
            let dkey = (di, for_binding_owners[vi]);
            if let Some(&rep) = debug_group_rep.get(&dkey) {
                union(&mut parent, rep, vi);
            } else {
                debug_group_rep.insert(dkey, vi);
            }
        }
    }

    // 2. Phi 连通性合并（忽略入口 Undef 以免拉入无关未初始化槽；
    //    同时对 Lua 5.5 `GenericFor` 中 `control == bindings.start` 的循环头控制槽 Phi，
    //    不把循环回边上的首循环变量合并进循环前控制初值 Web，避免循环变量与前驱槽冲突！）
    let mut skip_generic_for_backedge_phis: BTreeSet<(BlockId, Reg)> = BTreeSet::new();
    for hint in &analysis.cfg.loop_protocols {
        if let crate::analysis::LoopProtocolHint::GenericFor {
            header_block,
            control,
            bindings,
            ..
        } = hint
            && bindings.len > 0
            && *control == bindings.start
        {
            skip_generic_for_backedge_phis.insert((*header_block, *control));
        }
    }
    for phi in &ssa.phis {
        let pv = phi.value.index();
        let skip_backedge = skip_generic_for_backedge_phis.contains(&(phi.block, phi.reg));
        if ssa.tbc_values.contains(&phi.value) {
            // `<close>` Phi 的分支入边合并到同一个非 `<close>` 临时变量 web，
            // Phi 值本身保留在独立 `<close>` web 中，在 `TBC` 处以 `local x <close> = tmp` 落地。
            let mut first_src: Option<usize> = None;
            for &(edge_id, src) in &phi.incomings {
                let pred = analysis.cfg.edges[edge_id.index()].from;
                if skip_backedge && analysis.graph.dominates(phi.block, pred) {
                    continue;
                }
                if !matches!(ssa.defs[src.index()], SsaDef::Undef { .. }) {
                    if let Some(first) = first_src {
                        union(&mut parent, first, src.index());
                    } else {
                        first_src = Some(src.index());
                    }
                }
            }
            continue;
        }
        for &(edge_id, src) in &phi.incomings {
            let pred = analysis.cfg.edges[edge_id.index()].from;
            if skip_backedge && analysis.graph.dominates(phi.block, pred) {
                continue;
            }
            if !matches!(ssa.defs[src.index()], SsaDef::Undef { .. }) {
                union(&mut parent, pv, src.index());
            }
        }
    }

    // 3. Pinned 值与形参槽位：按同 SlotKey 合并按引用捕获的 `pinned_values` 与形参槽位；
    //    绝不把 `<close>`（`tbc_values`，隐含 `<const>`）的不同定值强行合并进同一变量，
    //    避免跨分支 `<close>` 声明被合并后退化为非法 `local x <close>; if ... then x = ...`！
    let num_params = usize::from(proto.signature.num_params);
    let mut pinned_slot_rep: BTreeMap<(SlotKey, Option<BlockId>), usize> = BTreeMap::new();
    for (vi, &owner) in for_binding_owners.iter().enumerate() {
        if let Some(slot) = ssa_value_slot(ssa, ValueId(vi)) {
            let force_slot_merge = (ssa.pinned_values.contains(&ValueId(vi))
                && !ssa.tbc_values.contains(&ValueId(vi)))
                || (slot.epoch == 0 && slot.reg.index() < num_params);
            if force_slot_merge {
                let pkey = (slot, owner);
                if let Some(&rep) = pinned_slot_rep.get(&pkey) {
                    union(&mut parent, rep, vi);
                } else {
                    pinned_slot_rep.insert(pkey, vi);
                }
            }
        }
    }

    // 4. 显式 NumericFor / GenericFor 控制变量合并
    for hint in &analysis.cfg.loop_protocols {
        match hint {
            crate::analysis::LoopProtocolHint::NumericFor {
                init_instr,
                latch_blocks,
                binding,
                ..
            } => {
                if let Some(init_v) = ssa.instr_def_value(*init_instr, *binding) {
                    for &lb in latch_blocks {
                        if let Some(last_iref) = analysis.cfg.blocks[lb.index()].instrs.last()
                            && let Some(latch_v) = ssa.instr_def_value(last_iref, *binding)
                        {
                            union(&mut parent, init_v.index(), latch_v.index());
                        }
                    }
                }
            }
            crate::analysis::LoopProtocolHint::GenericFor {
                prep_block,
                call_instr,
                loop_instr,
                body_entry,
                bindings,
                ..
            } => {
                // Lua 5.4/5.5 的 GenericForPrep（后常跟 Jump，不一定是块末指令）将 iterator/control/closing
                // 从调用结果槽转交控制槽：必须扫描整块并合并 source -> target Web，否则 control 槽被拆为未初始化 nil！
                if let Some(pb) = prep_block {
                    for prep_iref in analysis.cfg.blocks[pb.index()].instrs.iter() {
                        if let LowInstr::GenericForPrep(gp) = &proto.instrs[prep_iref.index()] {
                            if let (Some(uv), Some(dv)) = (
                                ssa.instr_use_value(prep_iref, gp.control_source),
                                ssa.instr_def_value(prep_iref, gp.control_target),
                            ) {
                                union(&mut parent, uv.index(), dv.index());
                            }
                            if let (Some(uv), Some(dv)) = (
                                ssa.instr_use_value(prep_iref, gp.closing_source),
                                ssa.instr_def_value(prep_iref, gp.closing_target),
                            ) {
                                union(&mut parent, uv.index(), dv.index());
                            }
                        }
                    }
                }
                // Lua 5.1/LuaJIT/5.2+ 的 `for k, v in ...` 控制变量 DebugLocal 从 body_entry 首指令 PC 开始生效
                let body_first_pc = analysis.cfg.blocks[body_entry.index()]
                    .instrs
                    .iter()
                    .next()
                    .and_then(|ir| pc_map.get(ir.index()))
                    .and_then(|pcs| pcs.iter().min().copied());
                for offset in 0..bindings.len {
                    let r = Reg(bindings.start.index() + offset);
                    if let (Some(dv), Some(uv)) = (
                        ssa.instr_def_value(*call_instr, r),
                        ssa.instr_use_value(*loop_instr, r),
                    ) {
                        union(&mut parent, dv.index(), uv.index());
                        if val_debug_idx[dv.index()].is_none()
                            && let Some(bpc) = body_first_pc
                            && let Some(di) = find_debug_local(r, bpc)
                        {
                            val_debug_idx[dv.index()] = Some(di);
                        }
                    }
                }
            }
        }
    }

    // 5. 单结果非调用就地自更新合并（如 `x = x + 1`、`s = s .. "a"`、`p = p.next`）
    for (idx, instr) in proto.instrs.iter().enumerate() {
        let is_in_place_op = matches!(
            instr,
            LowInstr::BinaryOp(_)
                | LowInstr::UnaryOp(_)
                | LowInstr::Concat(_)
                | LowInstr::GetTable(_)
        );
        if !is_in_place_op {
            continue;
        }
        let defs = &ssa.instr_defs[idx];
        if defs.len() != 1 {
            continue;
        }
        let (dst_reg, def_val) = defs[0];
        let Some(use_val) = ssa.instr_use_value(InstrRef(idx), dst_reg) else {
            continue;
        };
        if matches!(
            ssa.defs[use_val.index()],
            SsaDef::Param { .. } | SsaDef::VarArgParam { .. } | SsaDef::Undef { .. }
        ) {
            continue;
        }
        if ssa_value_slot(ssa, def_val) != ssa_value_slot(ssa, use_val)
            || for_binding_owners[use_val.index()] != for_binding_owners[def_val.index()]
            || ssa.tbc_values.contains(&use_val)
            || ssa.tbc_values.contains(&def_val)
        {
            continue;
        }
        // 若两个值各自明确属于不同的源码 DebugLocal，则不强制合并
        if let (Some(d1), Some(d2)) = (val_debug_idx[use_val.index()], val_debug_idx[def_val.index()])
            && d1 != d2
        {
            continue;
        }
        union(&mut parent, use_val.index(), def_val.index());
    }

    // 5b. 单结果自更新调用合并（如 Luau `fn = fn(arg)` / `obj = obj:next(arg)` 经调用帧临时槽写回同寄存器）：
    //     `move r_tmp <- r; call r_tmp(...) -> r_tmp; move r <- r_tmp` 保持 `r` 为同一可变局部，
    //     还原源码自更新语义并避免 Luau `-O2` 将首步误判为不可变局部函数而逐轮展开！
    for (idx, instr) in proto.instrs.iter().enumerate() {
        let LowInstr::Move(mv) = instr else {
            continue;
        };
        let defs = &ssa.instr_defs[idx];
        if defs.len() != 1 {
            continue;
        }
        let (dst_reg, def_val) = defs[0];
        let Some(src_val) = ssa.instr_use_value(InstrRef(idx), mv.src) else {
            continue;
        };
        let SsaDef::Instr {
            instr: call_iref, ..
        } = ssa.defs[src_val.index()]
        else {
            continue;
        };
        let LowInstr::Call(call) = &proto.instrs[call_iref.index()] else {
            continue;
        };
        if ssa.instr_defs[call_iref.index()].len() != 1 {
            continue;
        }
        // 查找该调用的 callee（普通调用）或 receiver（方法调用）是否直接来自同寄存器 `dst_reg`
        let prior_val = match call.kind {
            crate::transformer::CallKind::Method => {
                let recv_reg = Reg(call.callee.index() + 1);
                ssa.instr_use_value(call_iref, recv_reg).and_then(|rv| {
                    if let SsaDef::Instr { instr: mi, .. } = ssa.defs[rv.index()] {
                        match &proto.instrs[mi.index()] {
                            LowInstr::Move(m2) if m2.src == dst_reg => {
                                ssa.instr_use_value(mi, dst_reg)
                            }
                            LowInstr::GetTable(gt)
                                if gt.base == crate::transformer::AccessBase::Reg(dst_reg) =>
                            {
                                ssa.instr_use_value(mi, dst_reg)
                            }
                            _ => None,
                        }
                    } else {
                        None
                    }
                })
            }
            _ => ssa.instr_use_value(call_iref, call.callee).and_then(|cv| {
                if let SsaDef::Instr { instr: mi, .. } = ssa.defs[cv.index()]
                    && let LowInstr::Move(m2) = &proto.instrs[mi.index()]
                    && m2.src == dst_reg
                {
                    ssa.instr_use_value(mi, dst_reg)
                } else {
                    None
                }
            }),
        };
        let Some(use_val) = prior_val else {
            continue;
        };
        if matches!(
            ssa.defs[use_val.index()],
            SsaDef::Param { .. } | SsaDef::VarArgParam { .. } | SsaDef::Undef { .. }
        ) {
            continue;
        }
        if ssa_value_slot(ssa, def_val) != ssa_value_slot(ssa, use_val)
            || for_binding_owners[use_val.index()] != for_binding_owners[def_val.index()]
            || ssa.tbc_values.contains(&use_val)
            || ssa.tbc_values.contains(&def_val)
        {
            continue;
        }
        if let (Some(d1), Some(d2)) = (val_debug_idx[use_val.index()], val_debug_idx[def_val.index()])
            && d1 != d2
        {
            continue;
        }
        union(&mut parent, use_val.index(), def_val.index());
        // 强制物化自更新链两端的 SSA 值，避免中间单用 `Move` 滞留 `pending` 被侧效应冲刷成多个独立临时局部。
        materialized_values.insert(use_val);
        materialized_values.insert(def_val);
    }

    // 6. 检查会泄漏到循环外/顶层作用域的物化 distinct Web 数量：
    //    `for` 循环控制变量与完全封闭在某自然循环体内的局部会由 `vars.rs` 下沉至循环块内部，
    //    不累积占用外层局部槽；仅当顶层/跨循环物化 Web 超过 165 安全阈值时按 `(SlotKey, for_binding_owner)` 合并，
    //    既守住超大平坦函数的 Lua 200-local 上限，又彻底消除大型多循环文件（如 400 行测试脚本）的 140 阈值悬崖！
    let mut loop_body_sets: Vec<BTreeSet<BlockId>> = analysis
        .graph
        .natural_loops
        .iter()
        .map(|nl| nl.blocks.iter().copied().collect())
        .collect();
    for hint in &analysis.cfg.loop_protocols {
        let body_entry = match hint {
            crate::analysis::LoopProtocolHint::NumericFor { body_entry, .. }
            | crate::analysis::LoopProtocolHint::GenericFor { body_entry, .. } => *body_entry,
        };
        let dominated: BTreeSet<BlockId> = (0..analysis.cfg.blocks.len())
            .map(BlockId)
            .filter(|&b| analysis.graph.dominates(body_entry, b))
            .collect();
        if !dominated.is_empty() {
            loop_body_sets.push(dominated);
        }
    }
    let mut web_blocks: BTreeMap<usize, BTreeSet<BlockId>> = BTreeMap::new();
    for (vi, &owner) in for_binding_owners.iter().enumerate() {
        if !materialized_values.contains(&ValueId(vi))
            || owner.is_some()
            || matches!(ssa.defs[vi], SsaDef::Param { .. } | SsaDef::Undef { .. })
        {
            continue;
        }
        let root = find(&mut parent, vi);
        let entry = web_blocks.entry(root).or_default();
        match ssa.defs[vi] {
            SsaDef::Instr { block, .. } | SsaDef::Phi { block, .. } => {
                entry.insert(block);
            }
            _ => {}
        }
        for u in &ssa.uses[vi] {
            match *u {
                UseSite::Instr { block, .. } => {
                    entry.insert(block);
                }
                UseSite::Phi { phi, .. } => {
                    entry.insert(ssa.phis[phi.index()].block);
                }
            }
        }
    }
    let outer_materialized_webs = web_blocks
        .values()
        .filter(|blocks| {
            !blocks.is_empty()
                && !loop_body_sets
                    .iter()
                    .any(|lset| blocks.iter().all(|b| lset.contains(b)))
        })
        .count();
    if outer_materialized_webs > 165 {
        let mut slot_rep: BTreeMap<(SlotKey, Option<BlockId>), usize> = BTreeMap::new();
        for (vi, &owner) in for_binding_owners.iter().enumerate() {
            if let Some(slot) = ssa_value_slot(ssa, ValueId(vi)) {
                let skey = (slot, owner);
                if let Some(&rep) = slot_rep.get(&skey) {
                    union(&mut parent, rep, vi);
                } else {
                    slot_rep.insert(skey, vi);
                }
            }
        }
    }

    // 7. 路径压缩并收集每个 Web 精准的源码 DebugLocal 名字提示
    let mut value_web = vec![0usize; n];
    let mut web_debug_idx: BTreeMap<usize, usize> = BTreeMap::new();
    for vi in 0..n {
        let root = find(&mut parent, vi);
        value_web[vi] = root;
        if let Some(di) = val_debug_idx[vi] {
            web_debug_idx
                .entry(root)
                .and_modify(|cur| *cur = (*cur).min(di))
                .or_insert(di);
        }
    }

    let mut web_debug_hints = BTreeMap::new();
    for (root, di) in web_debug_idx {
        if let Some(dl) = proto.debug_locals.get(di)
            && let Ok(name) = std::str::from_utf8(&dl.name.bytes)
        {
            web_debug_hints.insert(root, name.to_owned());
        }
    }
    // 仅对 Lua 5.5 显式命名变参表（`function(...args)`）补充入口变参槽的 debug 提示，
    // 避免普通匿名 chunk 的 `...` 槽位（Reg(0)）误窃取顶层首个局部变量的 debug 名字导致重编译漂移。
    for (vi, &root) in value_web.iter().enumerate() {
        if web_debug_hints.contains_key(&root) {
            continue;
        }
        if matches!(ssa.defs[vi], SsaDef::VarArgParam { .. })
            && proto.signature.named_vararg_table
            && let Some(slot) = ssa_value_slot(ssa, ValueId(vi))
            && let Some(hint) = analysis.dataflow.debug_slot_hints.get(&slot)
        {
            web_debug_hints.insert(root, hint.clone());
        }
    }

    (value_web, web_debug_hints, for_binding_owners)
}
