//! 在共享 HIR 控制流上合并不干扰的同槽 temp carrier。
//!
//! 来源身份由 Promotion 的 exact home 给出，后向活跃性只证明当前 HIR 是否仍需同时保存
//! 不同快照。不能由同槽直接推出可替换，也不能在 AST 按名字猜测原寄存器。
//! 例如不可规约区域的 `a=x; ::L:: b=a+1; a=b; goto L` 可以共用一个 carrier；若后续
//! 同时读取 a、b，或一次并行赋值写入两者，则整个 home 组保留独立身份。
//! debug、物理根、捕获、TBC、for 与显式 Preserve 域不参与此事务；先完成整图证明再
//! 使用 carried-local 的既有 rewrite/provenance 通道一次性提交。

use std::collections::{BTreeMap, BTreeSet};

use crate::hir::common::{HirCallExpr, HirExpr, HirLValue, HirProto, HirStmt, TempId};
use crate::hir::expr_safety::HirExprSafety;
use crate::hir::promotion::{HomeSlotKey, ProtoPromotionFacts};
use crate::hir::visit::{self, HirVisitor};

use super::super::lexical_cfg::{HirFlowGraph, HirFlowNodeKind};
use super::super::temp_touch::collect_temp_reads_in_proto;
use super::super::walk::rewrite_proto;
use super::HandoffIdentityFacts;
use super::binding::{BindingClassRewritePass, CarryBinding};

pub(super) fn coalesce_disjoint_temps(
    proto: &mut HirProto,
    facts: &mut ProtoPromotionFacts,
    identity: &HandoffIdentityFacts,
    safety: HirExprSafety,
) -> bool {
    let mut blocked = BTreeSet::new();
    for binding in identity
        .reference_captured
        .iter()
        .chain(&identity.to_be_closed)
        .chain(&identity.preserved)
    {
        let homes = match *binding {
            CarryBinding::Param(param) => facts.complete_param_home_slots(param),
            CarryBinding::Local(local) => facts.complete_local_home_slots(local),
            CarryBinding::Temp(temp) => facts.complete_temp_home_slots(temp),
        };
        blocked.extend(homes.iter().copied());
    }
    for &local in identity
        .debug
        .iter()
        .chain(&identity.for_bindings)
        .chain(&identity.physical_roots)
    {
        blocked.extend(facts.complete_local_home_slots(local).iter().copied());
    }
    for &temp in &proto.temps {
        if proto.physical_root_temps.contains(&temp)
            || facts.is_scope_end_copy_root_temp(temp)
            || facts.is_copy_root_endpoint(temp)
            || proto
                .temp_debug_locals
                .get(temp.index())
                .is_some_and(Option::is_some)
        {
            blocked.extend(facts.complete_temp_home_slots(temp).iter().copied());
        }
    }
    visit::visit_proto(
        proto,
        &mut ProtocolHomes {
            facts,
            blocked: &mut blocked,
        },
    );
    let mut groups = BTreeMap::<HomeSlotKey, Vec<TempId>>::new();
    // 无读者的写入留给 dead-temps；吸收到活跃 carrier 会使它们失去独立死写身份。
    for temp in collect_temp_reads_in_proto(proto) {
        if let Some(home) = facts.trusted_temp_home_slot(temp)
            && !blocked.contains(&home)
        {
            groups.entry(home).or_default().push(temp);
        }
    }
    groups.retain(|_, temps| temps.len() > 1);
    if groups.is_empty() {
        return false;
    }
    let homes = groups
        .iter()
        .flat_map(|(&home, temps)| temps.iter().map(move |&temp| (temp, home)))
        .collect::<BTreeMap<_, _>>();
    let Ok(graph) = HirFlowGraph::for_proto(&proto.body, safety) else {
        return false;
    };
    let events = graph
        .nodes()
        .iter()
        .map(|node| {
            let mut event = TempEvent::default();
            match node.kind() {
                HirFlowNodeKind::Stmt(stmt) => visit::visit_stmt_header(stmt, &mut event),
                HirFlowNodeKind::GenericForInit(flow) => {
                    visit::visit_stmt_header(flow.stmt(), &mut event)
                }
                HirFlowNodeKind::RepeatCondition(repeat) => {
                    visit::visit_expr(&repeat.cond, &mut event)
                }
                HirFlowNodeKind::UnknownControl => event.reads.extend(homes.keys().copied()),
                HirFlowNodeKind::Exit
                | HirFlowNodeKind::FunctionExit
                | HirFlowNodeKind::NumericForDispatch
                | HirFlowNodeKind::GenericForDispatch(_)
                | HirFlowNodeKind::ForBinding(_) => {}
            }
            event.reads.retain(|temp| homes.contains_key(temp));
            event.writes.retain(|temp| homes.contains_key(temp));
            event
        })
        .collect::<Vec<_>>();
    graph.solve_backward(BTreeSet::new(), union_temps, |id, _, live| {
        let event = &events[id.index()];
        // 定义与其它 live-out 同时存在；并行写入也不能合成重复 lvalue。
        note_interference(
            live.iter().chain(&event.writes).copied(),
            &homes,
            &mut blocked,
        );
        live.retain(|temp| !event.writes.contains(temp));
        live.extend(&event.reads);
        note_interference(live.iter().copied(), &homes, &mut blocked);
    });
    let rewrites = groups
        .into_iter()
        .filter(|(home, _)| !blocked.contains(home))
        .flat_map(|(_, temps)| {
            let target = CarryBinding::Temp(temps[0]);
            temps
                .into_iter()
                .skip(1)
                .map(move |temp| (CarryBinding::Temp(temp), target))
        })
        .collect::<BTreeMap<_, _>>();
    if rewrites.is_empty() {
        return false;
    }
    let merged = rewrites
        .keys()
        .chain(rewrites.values())
        .filter_map(|binding| {
            if let CarryBinding::Temp(temp) = binding {
                Some(*temp)
            } else {
                None
            }
        })
        .collect();
    facts.retire_coalesced_definition_facts(&merged);
    rewrite_proto(
        proto,
        &mut BindingClassRewritePass {
            rewrites,
            promotion_facts: facts,
        },
    )
}

struct ProtocolHomes<'a> {
    facts: &'a ProtoPromotionFacts,
    blocked: &'a mut BTreeSet<HomeSlotKey>,
}

impl ProtocolHomes<'_> {
    fn protect(&mut self, temp: TempId) {
        self.blocked
            .extend(self.facts.complete_temp_home_slots(temp).iter().copied());
    }
}

impl HirVisitor for ProtocolHomes<'_> {
    fn visit_call(&mut self, call: &HirCallExpr) {
        for root in &call.argument_roots {
            self.protect(root.producer);
        }
    }

    fn visit_stmt(&mut self, stmt: &HirStmt) {
        if let HirStmt::GenericFor(for_stmt) = stmt {
            for &temp in &for_stmt.initializer_roots {
                self.protect(temp);
            }
            for result in &for_stmt.dispatch_results {
                self.protect(result.result_def);
            }
        }
        if let HirStmt::Assign(assign) = stmt
            && assign.method_rewrite_transaction.is_some()
        {
            for target in &assign.targets {
                if let HirLValue::Temp(temp) = target {
                    self.protect(*temp);
                }
            }
        }
    }
}

#[derive(Default)]
struct TempEvent {
    reads: BTreeSet<TempId>,
    writes: BTreeSet<TempId>,
}

impl HirVisitor for TempEvent {
    fn visit_expr(&mut self, expr: &HirExpr) {
        if let HirExpr::TempRef(temp) = expr {
            self.reads.insert(*temp);
        }
    }

    fn visit_lvalue(&mut self, target: &HirLValue) {
        if let HirLValue::Temp(temp) = target {
            self.writes.insert(*temp);
        }
    }
}

fn union_temps(current: &mut BTreeSet<TempId>, incoming: &BTreeSet<TempId>) -> bool {
    let before = current.len();
    current.extend(incoming);
    before != current.len()
}

fn note_interference(
    live: impl IntoIterator<Item = TempId>,
    homes: &BTreeMap<TempId, HomeSlotKey>,
    blocked: &mut BTreeSet<HomeSlotKey>,
) {
    let mut seen = BTreeMap::new();
    for temp in live {
        let home = homes[&temp];
        if let Some(previous) = seen.insert(home, temp)
            && previous != temp
        {
            blocked.insert(home);
        }
    }
}
