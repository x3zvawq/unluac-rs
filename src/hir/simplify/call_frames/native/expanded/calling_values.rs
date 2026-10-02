//! 核对短路比较调用及其捕获读取函数的原完整函数体。
//!
//! 函数参数的调用仍是独立操作；只有当前表达式、原输入准备与固定返回同时吻合，才可继续匹配两层展开。

use super::*;
use crate::hir::common::{HirBinaryOpKind, HirOperationSources, ParamId, UpvalueId};
use crate::hir::promotion::value_programs::Literal;

mod anonymous;
mod candidates;
mod draft;
mod folded_pairs;
mod frames;
pub(in crate::hir::simplify::call_frames) use frames::Frames;
mod index;
mod nil_values;
mod observed;
mod pairs;
pub(super) use pairs::scalar_write;
mod prefixes;
mod reading;
mod shared;

pub(super) use draft::{Prepared, prepare};
pub(super) use index::Templates;

impl Prepared {
    pub(super) fn plans(
        &self,
        context: NativeFrameContext<'_>,
        facts: &ProtoPromotionFacts,
    ) -> Vec<Plan> {
        let mut plans = pairs::plans(&self.pairs, context, facts);
        plans.extend(shared::plans(&self.shared, context, facts));
        plans.extend(observed::plans(&self.observed, context, facts));
        plans.extend(anonymous::plans(&self.anonymous, context, facts));
        plans
    }
    pub(super) fn frames<'a>(&'a self, facts: &ProtoPromotionFacts) -> Frames<'a> {
        Frames::new(
            &self.invocations,
            &self.pairs,
            &self.nil,
            &self.shared,
            &self.observed,
            &self.anonymous,
            facts,
        )
    }

    pub(super) fn certified(&self, sites: &BTreeSet<(crate::hir::HirSourceSite, LocalId)>) -> bool {
        self.invocations.iter().all(|invocation| {
            sites.contains(&(invocation.candidate.source, invocation.callee.local))
        }) && self.pairs.iter().all(|invocation| {
            sites.contains(&(invocation.candidate.source, invocation.callee.local))
        }) && self.nil.iter().all(|invocation| {
            sites.contains(&(invocation.candidate.source, invocation.callee.local))
        }) && self.shared.iter().all(|invocation| {
            sites.contains(&(invocation.candidate.source, invocation.callee.local))
        }) && self.observed.iter().all(|invocation| {
            sites.contains(&(invocation.candidate.source, invocation.callee.local))
        }) && self
            .anonymous
            .iter()
            .all(|invocation| sites.contains(&(invocation.source, invocation.callee.local)))
    }
}

impl Templates {
    pub(super) fn key(&self, proto: &HirProto) -> Option<(HirLuauInliningBody, crate::LuaString)> {
        if self.observed[proto.id.index()].is_some() {
            return Some((
                HirLuauInliningBody::CallingObservedValue {
                    template: proto.id.index(),
                },
                "".into(),
            ));
        }
        let body = self.bodies[proto.id.index()].as_ref()?;
        Some((
            match body.kind {
                Kind::Pair => HirLuauInliningBody::CallingReadPair {
                    template: proto.id.index(),
                },
                Kind::Value => HirLuauInliningBody::CallingValue {
                    template: proto.id.index(),
                },
                Kind::Shared => HirLuauInliningBody::CallingSharedValue {
                    template: proto.id.index(),
                },
            },
            "".into(),
        ))
    }
}

#[derive(Debug, Clone)]
pub(super) struct Body {
    pub kind: Kind,
    pub fallback: HirExpr,
    pub selection_hit: Option<Literal>,
    pub read_tag: Option<crate::LuaString>,
    pub names: Vec<Option<String>>,
    pub item: Option<(LocalId, Option<String>)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Kind {
    Value,
    Pair,
    Shared,
}

pub(super) fn body(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<Body> {
    if let Some(body) = shared::body(proto, facts) {
        return Some(body);
    }
    if let Some(body) = pairs::body(proto, facts) {
        return Some(body);
    }
    let fallback = crate::hir::luau_inlining::calling_value_fallback(proto)?;
    if proto.params.as_slice() != [ParamId(0), ParamId(1), ParamId(2)]
        || proto.signature.is_vararg
        || !proto.upvalues.is_empty()
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Return(ret)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirExpr::LogicalAnd(and)], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    let HirExpr::Binary(comparison) = &and.rhs else {
        return None;
    };
    let HirExpr::LogicalOr(or) = &comparison.rhs else {
        return None;
    };
    let HirExpr::Call(call) = &or.lhs else {
        return None;
    };
    Literal::from_expr(&or.rhs)?;
    let frame = facts.native_call_frame(call)?;
    let layout = facts.native_binary_layout(comparison)?;
    let result = facts.fixed_return_input(ret, 0)?;
    if and.lhs != HirExpr::ParamRef(ParamId(0))
        || comparison.op != HirBinaryOpKind::Eq
        || comparison.lhs != HirExpr::ParamRef(ParamId(1))
        || call.callee != HirExpr::ParamRef(ParamId(2))
        || !call.args.is_empty()
        || call.is_method()
        || call.fastcall.is_some()
        || frame.home != HomeSlotKey::new(5, 0)
        || !matches!(frame.results, Some(ResultPack::Fixed(pack)) if pack.start.index() == 5 && pack.len == 1)
        || !matches!(facts.native_return_frame(ret)?.values, ValuePack::Fixed(pack) if pack.start.index() == 3 && pack.len == 1)
        || facts.copy_value_prewrite(result)?.1 != HomeSlotKey::new(3, 0)
        || facts.short_circuit_scalar_homes(call.source_site?, &or.rhs, false)
            != Some((HomeSlotKey::new(5, 0), HomeSlotKey::new(4, 0)))
        || layout.lhs != Some(HomeSlotKey::new(1, 0))
        || layout.rhs != Some(HomeSlotKey::new(4, 0))
    {
        return None;
    }
    // 原三个参数均无写入，成本固定为一次调用、两次短路和一次比较；不使用常量折扣。
    Some(Body {
        kind: Kind::Value,
        fallback: fallback.clone(),
        selection_hit: None,
        read_tag: None,
        names: proto.param_debug_hints.clone(),
        item: None,
    })
}

pub(super) type CapturedRead = crate::hir::luau_inlining::CapturedReadTemplate;

fn returned(block: &HirBlock) -> Option<(&crate::hir::HirReturn, &HirExpr)> {
    let [HirStmt::Return(ret)] = block.stmts.as_slice() else {
        return None;
    };
    let ([value], None) = (ret.values.fixed.as_slice(), &ret.values.tail) else {
        return None;
    };
    ret.pending_cleanup_source.is_none().then_some((ret, value))
}

pub(super) fn captured_read(proto: &HirProto, facts: &ProtoPromotionFacts) -> Option<CapturedRead> {
    let template = crate::hir::luau_inlining::captured_read_template(proto)?;
    if !proto.params.is_empty()
        || proto.signature.is_vararg
        || proto.upvalues.len() != 3
        || !proto.children.is_empty()
        || proto.failure.is_some()
    {
        return None;
    }
    let [HirStmt::Assign(update), HirStmt::If(branch)] = proto.body.stmts.as_slice() else {
        return None;
    };
    let ([HirLValue::Upvalue(counter)], [HirExpr::Binary(add)], None) = (
        update.targets.as_slice(),
        update.values.fixed.as_slice(),
        &update.values.tail,
    ) else {
        return None;
    };
    let (condition, inverted) = synthetic_not_subject(&branch.cond);
    let HirExpr::Binary(comparison) = condition else {
        return None;
    };
    let HirExpr::UpvalueRef(index) = comparison.lhs else {
        return None;
    };
    let then = returned(&branch.then_block)?;
    let otherwise = returned(branch.else_block.as_ref()?)?;
    let ((hit_return, hit), (lookup_return, lookup)) = if inverted % 2 != 0 {
        (otherwise, then)
    } else {
        (then, otherwise)
    };
    let HirExpr::TableAccess(lookup) = lookup else {
        return None;
    };
    let HirExpr::UpvalueRef(table) = lookup.base else {
        return None;
    };
    let HirOperationSources::Single(lookup_source) = lookup.sources else {
        return None;
    };
    Literal::from_expr(hit)?;
    let update_layout = facts.native_binary_layout(add)?;
    let comparison_layout = facts.native_binary_layout(comparison)?;
    let lookup_layout = facts.native_table_read_layout(lookup)?;
    if update.is_phi_transfer
        || update.initializer_merge_transaction.is_some()
        || add.op != HirBinaryOpKind::Add
        || add.lhs != HirExpr::UpvalueRef(*counter)
        || comparison.op != HirBinaryOpKind::Eq
        || branch.predicate_source != comparison.source_site
        || lookup.key != HirExpr::UpvalueRef(index)
        || proto.mutable_upvalues.len() != 1
        || !proto.mutable_upvalues.contains(counter)
        || [*counter, index, table]
            .into_iter()
            .collect::<BTreeSet<_>>()
            .len()
            != 3
        || facts.operation_result_home(add.source_site?) != Some(HomeSlotKey::new(0, 0))
        || facts.upvalue_write_value(update)?.1 != HomeSlotKey::new(0, 0)
        || update_layout.lhs != Some(HomeSlotKey::new(1, 0))
        || update_layout.rhs.is_some()
        || facts
            .operation_input_preparation(add.source_site?, &add.lhs)?
            .1
            != HomeSlotKey::new(1, 0)
        || comparison_layout.lhs != Some(HomeSlotKey::new(0, 0))
        || comparison_layout.rhs.is_some()
        || facts
            .binary_operand_preparation(comparison, 0, &comparison.lhs)?
            .1
            != HomeSlotKey::new(0, 0)
        || facts.table_read_result_home(lookup) != Some(HomeSlotKey::new(0, 0))
        || lookup_layout.base != HomeSlotKey::new(1, 0)
        || lookup_layout.key != Some(HomeSlotKey::new(2, 0))
        || facts
            .operation_input_preparation(lookup_source, &lookup.base)?
            .1
            != HomeSlotKey::new(1, 0)
        || facts.table_key_preparation(lookup) != Some(HomeSlotKey::new(2, 0))
        || [hit_return, lookup_return].iter().any(|ret| {
            !matches!(facts.native_return_frame(ret).map(|frame| frame.values),
                Some(ValuePack::Fixed(pack)) if pack.start.index() == 0 && pack.len == 1)
        })
    {
        return None;
    }
    Some(template)
}
