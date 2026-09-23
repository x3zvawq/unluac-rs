//! 将共同结果槽上的完整返回判定树恢复为短路表达式。
//!
//! PUC/JIT 调用与比较短路值由共享 FrameBuilder 核对共同结果帧，保留字段查找
//! 对旧根的观察；Luau 只读参数树消费 Promotion 的返回 scratch 证明，函数尾部
//! 的纯值选择另核对当前声明前缀。叶 COPY 只能随整棵返回树消费，debug 身份仍保留。

use super::*;
use crate::hir::common::{HirIf, HirLogicalExpr, HirReturn, HirUnaryOpKind};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::simplify::expr_facts::expr_truthiness;

pub(in crate::hir::simplify) fn restore(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> bool {
    if restore_call_value(proto, facts, dialect).is_some() {
        return true;
    }
    if dialect != DecompileDialect::Luau || proto.signature.is_vararg {
        return false;
    }
    let Some(home) = facts.parameter_return_scratch() else {
        return restore_plain_tail(proto, facts, dialect).is_some();
    };
    if proto.local_debug_hints.iter().any(Option::is_some)
        || proto.local_debug_scopes.iter().any(Option::is_some)
        || home.slot() != proto.params.len()
        || !valid_block(&proto.body, facts, home)
    {
        // 候选拒绝[ProofIncomplete]：当前声明前缀、值身份或分支已超出原参数返回协议。
        return false;
    }
    let mut changed = false;
    let tree = fold(std::mem::take(&mut proto.body), &mut changed);
    proto.body = tree.into_block();
    changed
}

/// 既有低槽 local 后的终端判定树仍可在共同 scratch 写回；不单独删掉叶 COPY。
fn restore_plain_tail(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<()> {
    use super::super::mention::BindingReadCollector;
    use prefix::coordinates::{PointKind, visit};

    let start = proto
        .body
        .stmts
        .iter()
        .rposition(|stmt| matches!(stmt, HirStmt::If(_)))?;
    let candidate = &proto.body.stmts[start];
    let mut count = 0;
    let mut coordinate = None;
    let mut home = None;
    let mut retained_leaf = false;
    visit(&proto.body, &mut count, &mut |index, kind, stmt| {
        if kind != PointKind::Statement {
            return;
        }
        if std::ptr::eq(stmt, candidate) {
            coordinate = Some(index);
        }
        if coordinate.is_some()
            && home.is_none()
            && let HirStmt::Return(ret) = stmt
        {
            home = facts.native_return_frame(ret).map(|frame| frame.home);
        }
        if coordinate.is_some()
            && let HirStmt::LocalDecl(decl) = stmt
        {
            retained_leaf |= decl.bindings.iter().any(|local| {
                proto.local_debug_hints[local.index()].is_some()
                    || proto.local_debug_scopes[local.index()].is_some()
            });
        }
    });
    let home = home?;
    let restrictions = frame_restrictions(proto, facts);
    if retained_leaf
        || restrictions.barred.contains(&home)
        || restrictions.closed.contains(&home)
        || !valid_statements(&proto.body.stmts[start..], facts, home)
    {
        return None;
    }
    let mut required = BTreeSet::new();
    crate::hir::visit::visit_stmts(
        &proto.body.stmts[start..],
        &mut BindingReadCollector(|binding| {
            if let crate::hir::common::HirBinding::Local(local) = binding
                && facts
                    .trusted_local_home_slot(local)
                    .is_some_and(|input| input.slot() < home.slot())
            {
                required.insert(local);
            }
        }),
    );
    // 原 COPY 的结果槽必须紧接仍活跃的声明前缀；只比较两个 RETURN 的槽号不够。
    let preserved = prefix::validate_prefixes(
        proto,
        facts,
        dialect,
        false,
        &vec![false; count],
        &BTreeMap::from([(coordinate?, prefix::PrefixRequest { home, required })]),
        false,
    )
    .ok()?;
    let tail = HirBlock {
        stmts: proto.body.stmts.split_off(start),
    };
    let mut changed = false;
    let tree = fold(tail, &mut changed);
    proto.body.stmts.extend(tree.into_block().stmts);
    if !changed {
        return None;
    }
    for local in preserved {
        proto.inline_dispositions.preserve_local(
            local,
            crate::hir::HirInlineRetentionReason::PhysicalFramePrefix,
        );
    }
    Some(())
}

/// PUC/JIT 的条件 CALL 与终端值共用首个非参数槽时，整个返回表达式原位重发。
/// `not call()` 的分支极性不在进入下一臂前写 Boolean；字段查找仍能观察旧 CALL 根，
/// 因而不能把此证明替换为“覆盖前没有观察”的局部证书。
fn restore_call_value(
    proto: &mut HirProto,
    facts: &ProtoPromotionFacts,
    dialect: DecompileDialect,
) -> Option<()> {
    if dialect == DecompileDialect::Luau
        || proto.signature.is_vararg
        || proto.local_debug_hints.iter().any(Option::is_some)
        || proto.local_debug_scopes.iter().any(Option::is_some)
    {
        return None;
    }
    let [HirStmt::LocalDecl(decl), HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([local], [value], None) = (
        decl.bindings.as_slice(),
        decl.values.fixed.as_slice(),
        &decl.values.tail,
    ) else {
        return None;
    };
    let home = HomeSlotKey::new(proto.params.len(), 0);
    if decl.initializer_merge_transaction.is_some()
        || facts.trusted_local_home_slot(*local) != Some(home)
        || !valid_return(ret, facts, home)
        || ret.values.fixed[0] != HirExpr::LocalRef(*local)
    {
        return None;
    }
    // 简单短路可能已经树化，仍需同一返回帧证明，不能留下机械结果声明。
    // Decision 图归约只生成候选，不替代每个 CALL 及整个返回前缀的验证。
    let candidate = match value {
        HirExpr::Decision(decision) if dialect != DecompileDialect::Luajit => {
            super::super::decision::collapse_value_decision_expr(
                &crate::hir::decision::analyze_decision(decision),
                HirExprSafety::for_dialect(dialect),
                |node| matches!(node.test, HirExpr::Call(_)),
            )?
        }
        HirExpr::LogicalAnd(_) | HirExpr::LogicalOr(_) => value.clone(),
        _ => return None,
    };
    let restrictions = frame_restrictions(proto, facts);
    if restrictions.barred.contains(&home) || restrictions.closed.contains(&home) {
        return None;
    }
    let mut builder = native::frame_builder(
        NativeFrameContext {
            expanded_callees: None,
            proto,
            barred: &restrictions.barred,
            closed: &restrictions.closed,
            callee_aliases: &restrictions.callee_aliases,
            constants_fit_rk: tables::constants_fit_rk(proto),
        },
        &[],
        facts,
        dialect,
        home.slot(),
    )?;
    if !call_decision_value(&candidate, &mut builder, home) {
        // 候选拒绝[ProofIncomplete]：有叶离开共同结果帧或需要额外源码前缀，不能原位恢复。
        return None;
    }
    let mut ret = ret.clone();
    ret.values.fixed = vec![candidate];
    proto.body.stmts = vec![HirStmt::Return(ret)];
    Some(())
}

fn call_decision_value(value: &HirExpr, builder: &mut FrameBuilder<'_>, home: HomeSlotKey) -> bool {
    match value {
        HirExpr::Boolean(_) => true,
        HirExpr::ParamRef(param) => builder
            .facts
            .trusted_param_home_slot(*param)
            .is_some_and(|param| param.slot() < home.slot()),
        HirExpr::Call(call) => builder
            .call(call, 0, home.slot(), false, CallWidth::Single)
            .is_some(),
        HirExpr::Binary(binary)
            if matches!(
                binary.op,
                crate::hir::common::HirBinaryOpKind::Eq
                    | crate::hir::common::HirBinaryOpKind::Lt
                    | crate::hir::common::HirBinaryOpKind::Le
            ) =>
        {
            // 比较叶可直接读取低槽参数，也可包含同一返回区内的 CALL。
            // 共享 builder 核对原操作数布局、调用宽度和次序，不把元方法比较当作纯值。
            builder
                .expr(value, 0, home.slot(), None, false, true, None)
                .is_some()
        }
        HirExpr::Unary(unary) if unary.op == HirUnaryOpKind::Not && unary.source_site.is_none() => {
            call_decision_value(&unary.expr, builder, home)
        }
        HirExpr::LogicalAnd(pair) | HirExpr::LogicalOr(pair) => {
            call_decision_value(&pair.lhs, builder, home)
                && call_decision_value(&pair.rhs, builder, home)
        }
        _ => false,
    }
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
        HirExpr::LocalRef(local) => facts
            .trusted_local_home_slot(*local)
            .is_some_and(|input| input.slot() < home.slot()),
        HirExpr::Binary(binary) if binary.op == crate::hir::common::HirBinaryOpKind::Eq => {
            matches!(
                (&binary.lhs, &binary.rhs),
                (HirExpr::ParamRef(_), HirExpr::Nil | HirExpr::Boolean(_))
                    | (HirExpr::Nil | HirExpr::Boolean(_), HirExpr::ParamRef(_))
            ) && plain_value(&binary.lhs, facts, home)
                && plain_value(&binary.rhs, facts, home)
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
    ret.pending_cleanup_source.is_none()
        && ret.values.tail.is_none()
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
            mut cond,
            then_block,
            else_block,
            preserves_empty_test,
        } = *branch;
        let (mut then_tree, mut else_tree) = match (early, tail) {
            (Some(true), Some(tail)) => (fold(then_block, changed), fold(tail, changed)),
            (Some(false), Some(tail)) => (fold(tail, changed), fold(else_block.unwrap(), changed)),
            _ => (
                fold(then_block, changed),
                fold(else_block.unwrap(), changed),
            ),
        };
        // 常量真值在 else 时反转控制极性，仍保留原检查和两臂写回；
        // 不根据条件路径把未知值宣称为恒真，也不单独消除返回 COPY。
        if matches!((&then_tree, &else_tree),
            (Tree::Value { truthy, ret: left, .. }, Tree::Value { truthy: Some(true), ret: right, .. })
                if *truthy != Some(true) && left.frame_source == right.frame_source)
        {
            std::mem::swap(&mut then_tree, &mut else_tree);
            cond = HirExpr::Unary(Box::new(crate::hir::common::HirUnaryExpr {
                source_site: None,
                op: HirUnaryOpKind::Not,
                expr: cond,
            }));
        }
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
                    preserves_boolean_prewrite: false,
                    lhs: HirExpr::LogicalAnd(Box::new(HirLogicalExpr {
                        preserves_boolean_prewrite: false,
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
                    preserves_empty_test,
                    cond,
                    then_block: returned,
                    else_block: had_else.then(HirBlock::default),
                }
            } else {
                HirIf {
                    preserves_empty_test,
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
                preserves_empty_test,
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
