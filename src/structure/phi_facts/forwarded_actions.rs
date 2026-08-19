//! 沿 forward route 合成 phi copy 批次并解析透明 Move；依赖 SSA 和 route 顺序，不负责决定 owner；例如折叠多跳转发后的最终 incoming 值。

use super::*;

pub(super) struct ForwardedActionComposer {
    route_epoch: usize,
    batch_epoch: usize,
    query_epoch: usize,
    current_route: Option<super::super::plan::ForwardRouteId>,
    def_memo_epoch: Vec<usize>,
    def_memo_value: Vec<SsaValue>,
    def_visiting_epoch: Vec<usize>,
    phi_value_epoch: Vec<usize>,
    phi_values: Vec<SsaValue>,
    phi_resolved_epoch: Vec<usize>,
    phi_resolved_values: Vec<SsaValue>,
    phi_query_epoch: Vec<usize>,
    target_batch_epoch: Vec<usize>,
    touched: Vec<PhiId>,
    def_path: Vec<crate::structure::DefId>,
    phi_path: Vec<PhiId>,
    pending: Vec<(PhiId, SsaValue)>,
}

impl ForwardedActionComposer {
    pub(super) fn new(dataflow: &DataflowFacts) -> Self {
        Self {
            route_epoch: 0,
            batch_epoch: 0,
            query_epoch: 0,
            current_route: None,
            def_memo_epoch: vec![0; dataflow.defs.len()],
            def_memo_value: vec![SsaValue::Entry(Reg(0)); dataflow.defs.len()],
            def_visiting_epoch: vec![0; dataflow.defs.len()],
            phi_value_epoch: vec![0; dataflow.phi_candidates.len()],
            phi_values: vec![SsaValue::Entry(Reg(0)); dataflow.phi_candidates.len()],
            phi_resolved_epoch: vec![0; dataflow.phi_candidates.len()],
            phi_resolved_values: vec![SsaValue::Entry(Reg(0)); dataflow.phi_candidates.len()],
            phi_query_epoch: vec![0; dataflow.phi_candidates.len()],
            target_batch_epoch: vec![0; dataflow.phi_candidates.len()],
            touched: Vec::new(),
            def_path: Vec::new(),
            phi_path: Vec::new(),
            pending: Vec::new(),
        }
    }

    pub(super) fn begin_route(
        &mut self,
        route: Option<super::super::plan::ForwardRouteId>,
    ) -> Result<(), StructureError> {
        self.route_epoch = self
            .route_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action route epoch overflow"))?;
        self.touched.clear();
        self.pending.clear();
        self.current_route = route;
        Ok(())
    }

    pub(super) fn install_entry(&mut self, copies: &[PhiEdgeCopy]) -> Result<(), StructureError> {
        let batch = self.next_batch()?;
        for copy in copies {
            self.record_pending(copy.phi_id, copy.value, batch)?;
        }
        self.commit_pending()
    }

    pub(super) fn apply_forwarded_batch(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        copies: &[PhiEdgeCopy],
        collapse_defs: bool,
    ) -> Result<(), StructureError> {
        let batch = self.next_batch()?;
        for copy in copies {
            let value = self.resolve_forwarded_value(
                cfg,
                dataflow,
                plan,
                copy.value,
                batch,
                collapse_defs,
            )?;
            self.record_pending(copy.phi_id, value, batch)?;
        }
        self.commit_pending()
    }

    pub(super) fn next_batch(&mut self) -> Result<usize, StructureError> {
        self.batch_epoch = self
            .batch_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action batch epoch overflow"))?;
        self.pending.clear();
        Ok(self.batch_epoch)
    }

    pub(super) fn record_pending(
        &mut self,
        target: PhiId,
        value: SsaValue,
        batch: usize,
    ) -> Result<(), StructureError> {
        let seen = self
            .target_batch_epoch
            .get_mut(target.index())
            .ok_or_else(|| {
                StructureError::invalid(format!("forwarded action targets missing {target}"))
            })?;
        if *seen == batch {
            return Err(StructureError::invalid(format!(
                "forwarded action batch writes {target} more than once"
            )));
        }
        *seen = batch;
        self.pending.push((target, value));
        Ok(())
    }

    pub(super) fn commit_pending(&mut self) -> Result<(), StructureError> {
        for (target, value) in self.pending.drain(..) {
            let Some(epoch) = self.phi_value_epoch.get_mut(target.index()) else {
                return Err(StructureError::invalid(format!(
                    "forwarded action targets missing {target}"
                )));
            };
            if *epoch != self.route_epoch {
                self.touched.push(target);
            }
            *epoch = self.route_epoch;
            self.phi_values[target.index()] = value;
        }
        Ok(())
    }

    pub(super) fn resolve_forwarded_value(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        mut value: SsaValue,
        batch: usize,
        collapse_defs: bool,
    ) -> Result<SsaValue, StructureError> {
        self.query_epoch = self
            .query_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forwarded action query epoch overflow"))?;
        self.phi_path.clear();
        let mut cycle = false;
        loop {
            if collapse_defs {
                value = self.collapse_forwarded_defs(cfg, dataflow, plan, value)?;
            }
            let SsaValue::Phi(phi) = value else {
                break;
            };
            let Some(value_epoch) = self.phi_value_epoch.get(phi.index()).copied() else {
                return Err(StructureError::invalid(format!(
                    "forwarded action references missing {phi}"
                )));
            };
            if self.phi_resolved_epoch[phi.index()] == batch {
                value = self.phi_resolved_values[phi.index()];
                break;
            }
            if value_epoch != self.route_epoch {
                break;
            }
            if self.phi_query_epoch[phi.index()] == self.query_epoch {
                cycle = true;
                break;
            }
            self.phi_query_epoch[phi.index()] = self.query_epoch;
            self.phi_path.push(phi);
            value = self.phi_values[phi.index()];
        }
        if !cycle {
            for phi in &self.phi_path {
                self.phi_resolved_epoch[phi.index()] = batch;
                self.phi_resolved_values[phi.index()] = value;
            }
        }
        Ok(value)
    }

    pub(super) fn collapse_forwarded_defs(
        &mut self,
        cfg: &Cfg,
        dataflow: &DataflowFacts,
        plan: &StructurePlan,
        mut value: SsaValue,
    ) -> Result<SsaValue, StructureError> {
        self.def_path.clear();
        while let SsaValue::Def(def) = value {
            let Some(definition) = dataflow.defs.get(def.index()) else {
                return Err(StructureError::invalid(format!(
                    "forwarded action references missing {def}"
                )));
            };
            if self.def_memo_epoch[def.index()] == self.route_epoch {
                value = self.def_memo_value[def.index()];
                break;
            }
            if self.def_visiting_epoch[def.index()] == self.route_epoch {
                // 非法循环别名没有可继续证明的来源；保留重复处的 canonical def。
                break;
            }
            self.def_visiting_epoch[def.index()] = self.route_epoch;
            self.def_path.push(def);
            let Some(route) = self.current_route else {
                break;
            };
            if !cfg
                .succs
                .get(definition.block.index())
                .is_some_and(|edges| {
                    edges
                        .iter()
                        .any(|edge| plan.forward_route_contains_edge(route, *edge))
                })
            {
                break;
            }
            let uses = dataflow
                .use_values
                .get(definition.instr.index())
                .ok_or_else(|| {
                    StructureError::invalid(format!("{def} has no canonical use-value summary"))
                })?;
            let mut sources = uses.fixed.values();
            let Some(source) = sources.next() else {
                break;
            };
            if sources.next().is_some() {
                break;
            }
            value = source;
        }
        for def in &self.def_path {
            self.def_memo_epoch[def.index()] = self.route_epoch;
            self.def_memo_value[def.index()] = value;
        }
        Ok(value)
    }

    pub(super) fn finish(&self) -> Result<Vec<PhiEdgeCopy>, StructureError> {
        self.touched
            .iter()
            .map(|phi_id| {
                if self.phi_value_epoch.get(phi_id.index()).copied() != Some(self.route_epoch) {
                    return Err(StructureError::invalid(format!(
                        "forwarded action lost the final value for {phi_id}"
                    )));
                }
                Ok(PhiEdgeCopy {
                    phi_id: *phi_id,
                    value: self.phi_values[phi_id.index()],
                })
            })
            .collect()
    }
}
