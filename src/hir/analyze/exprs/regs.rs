//! 这个子模块负责把寄存器读取解释成 local/temp/entry 值引用。
//!
//! 它依赖 Dataflow 的 `use_values` 和 bindings 层已经分配好的 temp/local 身份，不会在这里
//! 重新做 SSA 合流判定。
//! 例如：某条指令读取 `r0`，若对应唯一 `TempId`，这里会直接降成 `TempRef(t0)`。

use super::*;

pub(crate) fn expr_for_reg_use(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let Some(values) = lowering.dataflow.use_values_at(instr_ref).get(reg) else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value use r{} @{}",
        reg.index(),
        instr_ref.index()
    ))
}

pub(crate) fn expr_for_closure_capture(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    dst: Reg,
    source: crate::transformer::CaptureSource,
) -> HirExpr {
    match source {
        crate::transformer::CaptureSource::Reg(reg) if reg == dst => {
            let self_temp = lowering.bindings.instr_fixed_defs[instr_ref.index()]
                .first()
                .copied()
                .expect("closure writes exactly one fixed target");
            HirExpr::TempRef(self_temp)
        }
        crate::transformer::CaptureSource::Reg(reg) => {
            // 先尝试正常的 SSA use-def 解析
            let expr = expr_for_reg_use(lowering, block, instr_ref, reg);
            // 互递归前向声明模式：Lua upvalue 是引用变量槽而非快照，closure 实际执行
            // 时看到的是寄存器的最终值。需要 forward_def 的场景有两种：
            //  1. Unresolved：寄存器在捕获点没有到达定义（entry-reg），说明没有显式
            //     初始化（如 `local a, b; a = function() b()... end`）。
            //  2. LOADNIL 前缀：三路互递归 `local a, b, c` 编译时先 LOADNIL r2..r4
            //     再依次 CLOSURE，此时 SSA 能看到 LOADNIL 的定义（TempRef），但该
            //     定义只是占位 nil。真正的值是后续 CLOSURE 写入的同一寄存器。
            let should_forward = match &expr {
                HirExpr::Unresolved(_) => true,
                HirExpr::TempRef(_) => is_loadnil_def(lowering, instr_ref, reg),
                _ => false,
            };
            if should_forward
                && let Some(forward_expr) =
                    forward_def_in_block(lowering, block, instr_ref, reg)
            {
                return forward_expr;
            }
            expr
        }
        crate::transformer::CaptureSource::Upvalue(upvalue) => {
            HirExpr::UpvalueRef(UpvalueId(upvalue.index()))
        }
    }
}

/// 检查某条指令读取的寄存器的 SSA 到达定义是否来自 LOADNIL 指令。
///
/// 用于在 closure capture 解析中区分"有意义的非 nil 定义"和"仅仅是 LOADNIL 占位"。
/// 后者在 `local a, b, c` + 三路互递归编译结果中出现：
/// LOADNIL r2..r4 之后紧跟 CLOSURE r2/r3/r4，capture 的 SSA 到达定义
/// 虽然存在（不是 Unresolved）但只是 LOADNIL 的占位 nil。
fn is_loadnil_def(
    lowering: &ProtoLowering<'_>,
    instr_ref: InstrRef,
    reg: Reg,
) -> bool {
    let Some(values) = lowering.dataflow.use_values_at(instr_ref).get(reg) else {
        return false;
    };
    if values.len() != 1 {
        return false;
    }
    let value = values.iter().next().unwrap();
    let SsaValue::Def(def) = value else {
        return false;
    };
    let def_instr = lowering.dataflow.def_instr(def);
    matches!(
        &lowering.proto.instrs[def_instr.index()],
        crate::transformer::LowInstr::LoadNil(_)
    )
}

/// 在当前 block 中查找 `instr_ref` 之后最后一个写入 `reg` 的定义。
///
/// Lua upvalue 引用的是变量槽而非快照，所以 closure 捕获时应指向该寄存器
/// 在此 block 内的最终定义。这个函数查找从 `instr_ref` 之后到 block 末尾
/// 的最后一个 must_def，确保互递归和 LOADNIL+CLOSURE 前向声明模式都能
/// 正确解析到最终绑定。
fn forward_def_in_block(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> Option<HirExpr> {
    let block_range = lowering.cfg.blocks[block.index()].instrs;
    let mut last_def_temp = None;
    for idx in (instr_ref.index() + 1)..block_range.end() {
        for def in &lowering.dataflow.instr_defs[idx] {
            if lowering.dataflow.def_reg(*def) == reg {
                last_def_temp = Some(lowering.bindings.fixed_temps[def.index()]);
            }
        }
    }
    last_def_temp.map(HirExpr::TempRef)
}

/// 某些结构恢复需要读取“进入 block 时这个寄存器代表哪个稳定值”，而不是某条真实 use。
///
/// 例如值短路被恢复成 `if + assign` 后，leaf block 可能根本没有再次显式读取结果寄存器，
/// 但我们仍然需要知道“走到这个 leaf 时 merge 值应该取谁”。
pub(crate) fn expr_for_reg_at_block_entry(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let range = lowering.cfg.blocks[block.index()].instrs;
    if range.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    let Some(values) = lowering.dataflow.reaching_values_at(range.start).get(reg) else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value entry r{} block#{}",
        reg.index(),
        block.index()
    ))
}

/// 某些 `goto + label` 形状需要读取“离开 block 时这个寄存器的稳定值”。
///
/// 这和普通 `expr_for_reg_use` 不同：phi edge copy 不一定对应某条真实 use，
/// 也不能只看 `incoming.defs`，否则像“从 inner loop header 直接跳回 outer header”
/// 这种边会把 block 入口 phi 的稳定值丢掉。
pub(crate) fn expr_for_reg_at_block_exit(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }

    let range = lowering.cfg.blocks[block.index()].instrs;
    let Some(last_instr_ref) = range.last() else {
        return entry_reg_expr(lowering, reg);
    };

    let effect = &lowering.dataflow.instr_effects[last_instr_ref.index()];
    if effect.fixed_must_defs.contains(&reg) {
        let Some(def) = fixed_def_for_reg(lowering, last_instr_ref, reg) else {
            return unresolved_expr(format!(
                "missing block-exit def r{} block#{}",
                reg.index(),
                block.index()
            ));
        };
        return HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]);
    }

    let mut values = lowering
        .dataflow
        .reaching_values_at(last_instr_ref)
        .get(reg)
        .map(|values| values.to_compact_set())
        .unwrap_or_default();
    if effect.fixed_may_defs.contains(&reg) {
        let Some(def) = fixed_def_for_reg(lowering, last_instr_ref, reg) else {
            return unresolved_expr(format!(
                "missing block-exit may-def r{} block#{}",
                reg.index(),
                block.index()
            ));
        };
        values.insert(SsaValue::Def(def));
    }

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()]),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value exit r{} block#{}",
        reg.index(),
        block.index()
    ))
}

/// 当值恢复跨过被整体吸收的 branch 区域时，内部 leaf/node block 可能不会单独物化。
///
/// 这里允许沿着单一 `DefId` 继续下钻，但只展开“可以安全重复求值”的定义。
/// 像 `call/newtable/gettable` 这类一旦重复展开就可能改写求值次数或对象身份的值，
/// 仍然退回已有 temp，避免 HIR 先天带入错误语义。
pub(crate) fn expr_for_reg_use_inline(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let Some(values) = lowering.dataflow.use_values_at(instr_ref).get(reg) else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => expr_for_dup_safe_fixed_def(lowering, def)
                .unwrap_or_else(|| HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()])),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value use r{} @{}",
        reg.index(),
        instr_ref.index()
    ))
}

/// `single-eval` 只承诺“这次求值可以直接表达出来”，并不承诺“可以重复复制很多次”。
///
/// 这条语义专门服务短路节点的单次 test：像 `call(...)` 这种不可复制但可单次出现的值，
/// 在这里应该优先恢复成本体表达式，而不是先掉回 temp。
pub(crate) fn expr_for_reg_use_single_eval(
    lowering: &ProtoLowering<'_>,
    block: BlockRef,
    instr_ref: InstrRef,
    reg: Reg,
) -> HirExpr {
    if let Some(local) = loop_local_for_reg(lowering, block, reg) {
        return HirExpr::LocalRef(local);
    }
    let Some(values) = lowering.dataflow.use_values_at(instr_ref).get(reg) else {
        return entry_reg_expr(lowering, reg);
    };

    if values.is_empty() {
        return entry_reg_expr(lowering, reg);
    }

    if values.len() == 1 {
        let value = values
            .iter()
            .next()
            .expect("len checked above, exactly one SSA-like value exists");
        return match value {
            SsaValue::Def(def) => expr_for_fixed_def(lowering, def)
                .unwrap_or_else(|| HirExpr::TempRef(lowering.bindings.fixed_temps[def.index()])),
            SsaValue::Phi(phi) => HirExpr::TempRef(lowering.bindings.phi_temps[phi.index()]),
        };
    }

    unresolved_expr(format!(
        "multi-value use r{} @{}",
        reg.index(),
        instr_ref.index()
    ))
}
