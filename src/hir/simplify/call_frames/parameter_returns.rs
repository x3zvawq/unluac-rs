//! 将只读参数判定树的完整返回帧恢复为短路表达式。
//!
//! Promotion 从原 LIR 证明所有路径只写首个非参数槽、从同槽返回且无观察事件。
//! 此处核对当前 HIR 仍只有参数、常量、互斥分支和叶返回，故每条路径的源码空闲前缀
//! 都恰为参数区；不向一般 COPY 开放内联，也不从无事件 HIR 反推原 VM 写域。
//! 例如 `if b then if c then return "yes" else return "no" end
//! else local v=x; return v end` 可恢复 `return b and (c and "yes" or "no") or x`。
//! 独立的 `local v=x; return v` 仍保留：Luau 直接返回参数会省去原高槽写。
//! 单臂提前返回后的末尾返回准备也是互斥叶；例如 `if c then return "T" end;
//! return "F"` 共用原返回槽时可恢复 `return c and "T" or "F"`。
//! 自底向上移交表达式和真值摘要，不在每个父节点重扫或复制完整子树。

use super::*;
use crate::hir::common::{HirIf, HirLogicalExpr, HirReturn, HirUnaryOpKind};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::simplify::expr_facts::expr_truthiness;

pub(in crate::hir::simplify) fn restore(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    if dialect != DecompileDialect::Luau
        || proto.signature.is_vararg
        || proto.local_debug_hints.iter().any(Option::is_some)
        || proto.local_debug_scopes.iter().any(Option::is_some)
    {
        return false;
    }
    let Some(home) = facts.parameter_return_scratch() else {
        return false;
    };
    if home.slot() != proto.params.len() || !valid_block(&proto.body, facts, home) {
        // 候选拒绝[ProofIncomplete]：当前声明前缀、值身份或分支已超出原参数返回协议。
        return false;
    }
    let mut changed = false;
    let tree = fold(std::mem::take(&mut proto.body), &mut changed);
    proto.body = tree.into_block();
    changed
}

fn plain_value(value: &HirExpr, facts: &ProtoPromotionFacts, home: HomeSlotKey) -> bool {
    match value {
        HirExpr::Nil
        | HirExpr::Boolean(_)
        | HirExpr::Integer(_)
        | HirExpr::Number(_)
        | HirExpr::String(_) => true,
        HirExpr::ParamRef(param) => {
            param.index() < home.slot()
                && facts.trusted_param_home_slot(*param) == Some(HomeSlotKey::new(param.index(), 0))
        }
        HirExpr::LogicalAnd(pair) | HirExpr::LogicalOr(pair) => {
            plain_value(&pair.lhs, facts, home) && plain_value(&pair.rhs, facts, home)
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not => {
            plain_value(&unary.expr, facts, home)
        }
        _ => false,
    }
}

fn valid_return(ret: &HirReturn, facts: &ProtoPromotionFacts, home: HomeSlotKey) -> bool {
    ret.values.tail.is_none()
        && ret.values.fixed.len() == 1
        && facts.native_return_frame(ret).is_some_and(|frame| {
            frame.home == home && matches!(frame.values, ValuePack::Fixed(pack) if pack.len == 1)
        })
}

fn valid_block(block: &HirBlock, facts: &ProtoPromotionFacts, home: HomeSlotKey) -> bool {
    valid_statements(&block.stmts, facts, home)
}

/// 返回体的末尾准备至多为一个声明和 RETURN，不从更长的 fallthrough 重建控制流。
fn return_leaf(stmts: &[HirStmt]) -> bool {
    matches!(
        stmts,
        [HirStmt::Return(_)] | [HirStmt::LocalDecl(_), HirStmt::Return(_)]
    )
}

/// true 表示 then 返回、false 表示 else 返回；另一臂必须完全为空。
fn early_return_arm(branch: &HirIf) -> Option<bool> {
    let then_empty = branch.then_block.stmts.is_empty();
    let else_empty = branch
        .else_block
        .as_ref()
        .is_none_or(|block| block.stmts.is_empty());
    (then_empty != else_empty).then_some(!then_empty)
}

fn valid_statements(stmts: &[HirStmt], facts: &ProtoPromotionFacts, home: HomeSlotKey) -> bool {
    match stmts {
        [HirStmt::If(branch)] => {
            plain_value(&branch.cond, facts, home)
                && valid_block(&branch.then_block, facts, home)
                && branch
                    .else_block
                    .as_ref()
                    .is_some_and(|other| valid_block(other, facts, home))
        }
        [HirStmt::If(branch), tail @ ..] if return_leaf(tail) => {
            let Some(then_returns) = early_return_arm(branch) else {
                return false;
            };
            let returned = if then_returns {
                &branch.then_block
            } else {
                branch.else_block.as_ref().unwrap()
            };
            plain_value(&branch.cond, facts, home)
                && valid_block(returned, facts, home)
                && valid_statements(tail, facts, home)
        }
        [HirStmt::Return(ret)] => {
            valid_return(ret, facts, home) && plain_value(&ret.values.fixed[0], facts, home)
        }
        [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] => {
            let [local] = decl.bindings.as_slice() else {
                return false;
            };
            valid_return(ret, facts, home)
                && ret.values.fixed[0] == HirExpr::LocalRef(*local)
                && facts.trusted_local_home_slot(*local) == Some(home)
                && decl.initializer_merge_transaction.is_none()
                && decl.values.tail.is_none()
                && matches!(decl.values.fixed.as_slice(), [value] if plain_value(value, facts, home))
        }
        _ => false,
    }
}

enum Tree {
    Value {
        // 尚未并入条件表达式的叶 COPY 不能单独删掉。
        original: Option<HirBlock>,
        ret: Box<HirReturn>,
        value: HirExpr,
        truthy: Option<bool>,
    },
    Block(HirBlock),
}

impl Tree {
    fn into_block(self) -> HirBlock {
        match self {
            Self::Block(block)
            | Self::Value {
                original: Some(block),
                ..
            } => block,
            Self::Value {
                original: None,
                mut ret,
                value,
                ..
            } => {
                ret.values.fixed = vec![value];
                HirBlock {
                    stmts: vec![HirStmt::Return(ret)],
                }
            }
        }
    }
}

fn fold(mut block: HirBlock, changed: &mut bool) -> Tree {
    if matches!(block.stmts.first(), Some(HirStmt::If(_))) {
        // valid_statements 已证明尾部只有至多两个叶语句；拆分不反复复制增长的后缀。
        let tail = (block.stmts.len() > 1).then(|| HirBlock {
            stmts: block.stmts.split_off(1),
        });
        let HirStmt::If(branch) = block.stmts.pop().unwrap() else {
            unreachable!()
        };
        let early = tail.as_ref().map(|_| early_return_arm(&branch).unwrap());
        let had_else = branch.else_block.is_some();
        let HirIf {
            cond,
            then_block,
            else_block,
        } = *branch;
        let (then_tree, else_tree) = match (early, tail) {
            (Some(true), Some(tail)) => (fold(then_block, changed), fold(tail, changed)),
            (Some(false), Some(tail)) => (fold(tail, changed), fold(else_block.unwrap(), changed)),
            _ => (
                fold(then_block, changed),
                fold(else_block.unwrap(), changed),
            ),
        };
        // 候选拒绝[ProofIncomplete]：and/or 需要 then 独立恒真及共同返回来源；
        // then 为假值会误选 else，未知真值也不能借参数当前调用的观测放宽。
        let can_merge = matches!((&then_tree, &else_tree),
            (Tree::Value { truthy: Some(true), ret: left, .. }, Tree::Value { ret: right, .. })
                if left.frame_source == right.frame_source);
        if can_merge {
            let Tree::Value {
                ret, value: left, ..
            } = then_tree
            else {
                unreachable!()
            };
            let Tree::Value {
                value: right,
                truthy,
                ..
            } = else_tree
            else {
                unreachable!()
            };
            *changed = true;
            return Tree::Value {
                original: None,
                ret,
                value: HirExpr::LogicalOr(Box::new(HirLogicalExpr {
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        lhs: cond,
                        rhs: left,
                    })),
                    rhs: right,
                })),
                truthy: (truthy == Some(true)).then_some(true),
            };
        }
        if let Some(then_returns) = early {
            // 合并失败时恢复原单臂与末尾叶；不能静默新增 else 或丢弃尚未消费的 Local。
            let (returned, tail) = if then_returns {
                (then_tree, else_tree)
            } else {
                (else_tree, then_tree)
            };
            let returned = returned.into_block();
            let mut stmts = vec![HirStmt::If(Box::new(if then_returns {
                HirIf {
                    cond,
                    then_block: returned,
                    else_block: had_else.then(HirBlock::default),
                }
            } else {
                HirIf {
                    cond,
                    then_block: HirBlock::default(),
                    else_block: Some(returned),
                }
            }))];
            stmts.extend(tail.into_block().stmts);
            return Tree::Block(HirBlock { stmts });
        }
        return Tree::Block(HirBlock {
            stmts: vec![HirStmt::If(Box::new(HirIf {
                cond,
                then_block: then_tree.into_block(),
                else_block: Some(else_tree.into_block()),
            }))],
        });
    }
    let HirStmt::Return(ret) = block.stmts.last().unwrap() else {
        unreachable!()
    };
    let value = match &block.stmts[0] {
        HirStmt::LocalDecl(decl) => decl.values.fixed[0].clone(),
        _ => ret.values.fixed[0].clone(),
    };
    let truthy = expr_truthiness(&value, HirExprSafety::for_dialect(DecompileDialect::Luau));
    Tree::Value {
        ret: ret.clone(),
        original: Some(block),
        value,
        truthy,
    }
}
