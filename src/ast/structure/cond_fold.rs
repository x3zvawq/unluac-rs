//! 短路布尔条件折叠器（`a and b`、`a or b`、`not a`）。
//!
//! 在进入分支/循环规约前，将相连的纯条件测试块归约为单个 `CondExpr`，
//! 避免将复合逻辑条件误判为多入口不可规约控制流。

use std::collections::BTreeSet;

use crate::analysis::{BlockId, Cfg, ProtoAnalysis, UseSite};
use crate::transformer::{LowInstr, LoweredProto};

use super::region::CondExpr;

/// 折叠结果：复合条件树 + 最终真假出口 + 已被吸收的后续条件块。
#[derive(Debug, Clone)]
pub(super) struct FoldedCondition {
    pub cond: CondExpr,
    pub then_target: BlockId,
    pub else_target: BlockId,
    pub consumed_blocks: BTreeSet<BlockId>,
}

/// 判断一个后续条件块是否可以安全吸收进复合 `and`/`or` 条件表达式。
///
/// 要求：
/// 1. 块以 `Branch` 结束；
/// 2. 块内前导指令全部为求值表达式（无外部写入：无 `SetTable`/`SetUpvalue`/`Close`/`Tbc`/
///    无结果 `Call`），且定值仅在本块内使用（不泄漏给分支外，防止短路后外部读取未定义值）。
pub(crate) fn is_pure_condition_continuation(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    block: BlockId,
) -> bool {
    let range = analysis.cfg.blocks[block.index()].instrs;
    let Some(last) = range.last() else {
        return false;
    };
    if !matches!(proto.instrs[last.index()], LowInstr::Branch(_)) {
        return false;
    }
    if !analysis.ssa.block_phis[block.index()].is_empty() {
        return false;
    }
    for iref in range.iter() {
        if iref == last {
            break;
        }
        let instr = &proto.instrs[iref.index()];
        let allowed_expr_step = matches!(
            instr,
            LowInstr::Move(_)
                | LowInstr::LoadNil(_)
                | LowInstr::LoadBool(_)
                | LowInstr::LoadConst(_)
                | LowInstr::LoadInteger(_)
                | LowInstr::LoadNumber(_)
                | LowInstr::UnaryOp(_)
                | LowInstr::BinaryOp(_)
                | LowInstr::Concat(_)
                | LowInstr::GetUpvalue(_)
                | LowInstr::GetTable(_)
                | LowInstr::NewTable(_)
                | LowInstr::Call(_)
                | LowInstr::VarArg(_)
                | LowInstr::Closure(_)
        );
        if !allowed_expr_step {
            return false;
        }
        // 如果是无结果或多结果调用/变参，属于独立语句（无法无损内联进 Lua 短路布尔表达式）。
        match instr {
            LowInstr::Call(call) => match call.results {
                crate::transformer::ResultPack::Ignore => return false,
                crate::transformer::ResultPack::Fixed(range) if range.len != 1 => return false,
                _ => {}
            },
            LowInstr::VarArg(va) => match va.results {
                crate::transformer::ResultPack::Ignore => return false,
                crate::transformer::ResultPack::Fixed(range) if range.len != 1 => return false,
                _ => {}
            },
            _ => {}
        }
        let defs = &analysis.ssa.instr_defs[iref.index()];
        if defs.len() > 1 && !matches!(instr, LowInstr::LoadNil(_)) {
            return false;
        }
        // 所有定值必须仅在本块内单次消费（既不泄漏到块外，也不物化为独立语句、不丢弃副作用）。
        // 特例：`SELF` 协议的接收者槽在同块内被 `GetTable(Method)` 和 `Call(Method)` 各读一次，本质仅是一次接收者求值！
        for &(reg, val) in defs {
            if analysis.ssa.pinned_values.contains(&val) {
                return false;
            }
            let uses = &analysis.ssa.uses[val.index()];
            let is_method_self_pair = uses.len() == 2
                && uses.iter().any(|u| {
                    matches!(
                        *u,
                        UseSite::Instr { block: ub, instr: ui }
                            if ub == block
                                && matches!(
                                    &proto.instrs[ui.index()],
                                    LowInstr::GetTable(gt)
                                        if gt.kind == crate::transformer::GetTableKind::Method
                                            && gt.base == crate::transformer::AccessBase::Reg(reg)
                                )
                    )
                })
                && uses.iter().any(|u| {
                    matches!(
                        *u,
                        UseSite::Instr { block: ub, instr: ui }
                            if ub == block
                                && matches!(
                                    &proto.instrs[ui.index()],
                                    LowInstr::Call(c) if c.kind == crate::transformer::CallKind::Method
                                )
                    )
                });
            // 无用副作用指令（0-use）或多用物化值（>=2 uses 且非 method self pair）会产出独立语句，禁止吞进短路右臂
            if uses.len() != 1 && !is_method_self_pair {
                return false;
            }
            let used_outside = uses.iter().any(|u| match *u {
                UseSite::Instr { block: ub, .. } => ub != block,
                UseSite::Phi { .. } => true,
            });
            if used_outside {
                return false;
            }
        }
    }
    true
}

/// 从 `header`（必须以 `Branch` 结束）出发，贪心折叠所有合法的短路 `and` / `or` 链。
///
/// `allowed`: 若指定，只吸收属于该集合内的后续条件块（防止跨出当前循环边界）。
pub(super) fn fold_condition(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    header: BlockId,
    allowed: Option<&BTreeSet<BlockId>>,
) -> Option<FoldedCondition> {
    let cfg = &analysis.cfg;
    let (then_e, else_e) = cfg.branch_edges(header)?;
    let LowInstr::Branch(br) = cfg.terminator(proto, header)? else {
        return None;
    };

    let mut cond = CondExpr::Atom {
        block: header,
        cond: br.cond,
    };
    let mut then_target = cfg.edges[then_e.index()].to;
    let mut else_target = cfg.edges[else_e.index()].to;
    let mut consumed = BTreeSet::new();
    consumed.insert(header);

    // 限制迭代次数避免极端图退化。
    for _ in 0..64 {
        let mut progressed = false;

        // 1) 尝试扩展 `then_target`（左侧为真时继续测试：`cond and rhs` 或 `not(cond) or rhs`）
        if then_target != else_target
            && !consumed.contains(&then_target)
            && can_absorb_next(proto, analysis, cfg, then_target, &consumed, allowed)
            && let Some(rhs) = fold_step(proto, cfg, then_target)
        {
            if rhs.else_target == else_target {
                // A ? (B ? T : F) : F  ==>  (A and B) ? T : F
                consumed.insert(then_target);
                cond = CondExpr::And(Box::new(cond), Box::new(rhs.cond));
                then_target = rhs.then_target;
                progressed = true;
            } else if rhs.then_target == else_target {
                // A ? (B ? F : T) : F  ==>  (A and not B) ? T : F
                consumed.insert(then_target);
                cond = CondExpr::And(Box::new(cond), Box::new(rhs.cond.negate()));
                then_target = rhs.else_target;
                progressed = true;
            }
        }

        // 2) 尝试扩展 `else_target`（左侧为假时继续测试：`cond or rhs`）
        if !progressed
            && then_target != else_target
            && !consumed.contains(&else_target)
            && can_absorb_next(proto, analysis, cfg, else_target, &consumed, allowed)
            && let Some(rhs) = fold_step(proto, cfg, else_target)
        {
            if rhs.then_target == then_target {
                // A ? T : (B ? T : F)  ==>  (A or B) ? T : F
                consumed.insert(else_target);
                cond = CondExpr::Or(Box::new(cond), Box::new(rhs.cond));
                else_target = rhs.else_target;
                progressed = true;
            } else if rhs.else_target == then_target {
                // A ? T : (B ? F : T)  ==>  (A or not B) ? T : F
                consumed.insert(else_target);
                cond = CondExpr::Or(Box::new(cond), Box::new(rhs.cond.negate()));
                else_target = rhs.then_target;
                progressed = true;
            }
        }

        // 3) 尝试递归折叠子链：(a and b) or (c and d) 场景中，else_target 自身是一个子 `and` 链
        if !progressed
            && then_target != else_target
            && !consumed.contains(&else_target)
            && can_absorb_next(proto, analysis, cfg, else_target, &consumed, allowed)
            && let Some(sub) = fold_subchain(proto, analysis, else_target, &consumed, allowed)
        {
            if sub.then_target == then_target {
                consumed.extend(sub.consumed_blocks);
                cond = CondExpr::Or(Box::new(cond), Box::new(sub.cond));
                else_target = sub.else_target;
                progressed = true;
            } else if sub.else_target == then_target {
                consumed.extend(sub.consumed_blocks);
                cond = CondExpr::Or(Box::new(cond), Box::new(sub.cond.negate()));
                else_target = sub.then_target;
                progressed = true;
            }
        }

        if !progressed
            && then_target != else_target
            && !consumed.contains(&then_target)
            && can_absorb_next(proto, analysis, cfg, then_target, &consumed, allowed)
            && let Some(sub) = fold_subchain(proto, analysis, then_target, &consumed, allowed)
        {
            if sub.else_target == else_target {
                consumed.extend(sub.consumed_blocks);
                cond = CondExpr::And(Box::new(cond), Box::new(sub.cond));
                then_target = sub.then_target;
                progressed = true;
            } else if sub.then_target == else_target {
                consumed.extend(sub.consumed_blocks);
                cond = CondExpr::And(Box::new(cond), Box::new(sub.cond.negate()));
                then_target = sub.else_target;
                progressed = true;
            }
        }

        if !progressed {
            break;
        }
    }

    consumed.remove(&header);
    Some(FoldedCondition {
        cond,
        then_target,
        else_target,
        consumed_blocks: consumed,
    })
}

struct SingleCond {
    cond: CondExpr,
    then_target: BlockId,
    else_target: BlockId,
}

fn fold_step(proto: &LoweredProto, cfg: &Cfg, block: BlockId) -> Option<SingleCond> {
    let (then_e, else_e) = cfg.branch_edges(block)?;
    let LowInstr::Branch(br) = cfg.terminator(proto, block)? else {
        return None;
    };
    Some(SingleCond {
        cond: CondExpr::Atom {
            block,
            cond: br.cond,
        },
        then_target: cfg.edges[then_e.index()].to,
        else_target: cfg.edges[else_e.index()].to,
    })
}

fn can_absorb_next(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    cfg: &Cfg,
    block: BlockId,
    already_consumed: &BTreeSet<BlockId>,
    allowed: Option<&BTreeSet<BlockId>>,
) -> bool {
    if block == cfg.entry_block || block == cfg.exit_block {
        return false;
    }
    if let Some(allow) = allowed
        && !allow.contains(&block)
    {
        return false;
    }
    if analysis.graph.loop_by_header(block).is_some() {
        return false;
    }
    if !is_pure_condition_continuation(proto, analysis, block) {
        return false;
    }
    // 所有可达前驱都必须来自已吸收的条件子图（或者该块为纯单指令条件允许小节点安全复制）。
    let all_from_consumed = cfg
        .reachable_preds(block)
        .all(|e| already_consumed.contains(&e.from));
    if all_from_consumed {
        return true;
    }
    // 仅当该块极小（<= 2 条指令，纯测试）才允许在复杂组合条件中虚拟复制。
    cfg.blocks[block.index()].instrs.len <= 2
}

/// 折叠子条件链（用于 `(a and b) or (c and d)` 等嵌套短路）。
fn fold_subchain(
    proto: &LoweredProto,
    analysis: &ProtoAnalysis,
    start: BlockId,
    outer_consumed: &BTreeSet<BlockId>,
    allowed: Option<&BTreeSet<BlockId>>,
) -> Option<FoldedCondition> {
    let cfg = &analysis.cfg;
    let first = fold_step(proto, cfg, start)?;
    let mut cond = first.cond;
    let mut then_target = first.then_target;
    let else_target = first.else_target;
    let mut local_consumed = BTreeSet::new();
    local_consumed.insert(start);

    for _ in 0..16 {
        let mut combined = outer_consumed.clone();
        combined.extend(local_consumed.iter().copied());
        if then_target != else_target
            && !combined.contains(&then_target)
            && can_absorb_next(proto, analysis, cfg, then_target, &combined, allowed)
            && let Some(rhs) = fold_step(proto, cfg, then_target)
        {
            if rhs.else_target == else_target {
                local_consumed.insert(then_target);
                cond = CondExpr::And(Box::new(cond), Box::new(rhs.cond));
                then_target = rhs.then_target;
                continue;
            }
            if rhs.then_target == else_target {
                local_consumed.insert(then_target);
                cond = CondExpr::And(Box::new(cond), Box::new(rhs.cond.negate()));
                then_target = rhs.else_target;
                continue;
            }
        }
        break;
    }

    (local_consumed.len() > 1).then_some(FoldedCondition {
        cond,
        then_target,
        else_target,
        consumed_blocks: local_consumed,
    })
}
