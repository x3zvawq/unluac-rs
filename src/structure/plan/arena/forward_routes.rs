//! 透明 forwarding route 的构建、绑定与冻结。输入连续 CFG edge 路径和语义 owner，输出共享 route arena 与每条入口的稳定引用；不负责推断 break/continue。例如多个入口共享 jump 后缀时只保存一次物理 next 链。

use super::*;

pub(super) struct ForwardRouteBuilder {
    routes: Vec<ForwardRoutePlan>,
    next: Vec<Option<EdgeRef>>,
    next_assigned: Vec<bool>,
    remaining_len: Vec<usize>,
    last_by_edge: Vec<Option<EdgeRef>>,
    route_by_first: Vec<Option<ForwardRouteId>>,
    pub(super) owner_by_edge: Vec<Option<RegionId>>,
    pub(super) kind_by_edge: Vec<Option<ForwardRouteKind>>,
    pub(super) edges_by_owner: Vec<Vec<EdgeRef>>,
    binding_by_entry: Vec<Option<ForwardRouteId>>,
    visit_epoch: Vec<usize>,
    next_epoch: usize,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct FunctionalForwardPath {
    pub(super) first: EdgeRef,
    pub(super) last: EdgeRef,
    pub(super) len: usize,
}

pub(super) struct FunctionalForwardPathEdges<'a> {
    cfg: &'a Cfg,
    next: Option<EdgeRef>,
    remaining: usize,
}

impl<'a> FunctionalForwardPathEdges<'a> {
    fn new(cfg: &'a Cfg, path: FunctionalForwardPath) -> Self {
        Self {
            cfg,
            next: Some(path.first),
            remaining: path.len,
        }
    }
}

impl Iterator for FunctionalForwardPathEdges<'_> {
    type Item = EdgeRef;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let edge = self.next?;
        self.remaining -= 1;
        self.next = if self.remaining == 0 {
            None
        } else {
            let target = self.cfg.edges[edge.index()].to;
            let [next] = self.cfg.succs[target.index()].as_slice() else {
                self.next = None;
                return Some(edge);
            };
            Some(*next)
        };
        Some(edge)
    }
}

impl ForwardRouteBuilder {
    pub(super) fn new(edge_count: usize, region_count: usize) -> Self {
        Self {
            routes: Vec::new(),
            next: vec![None; edge_count],
            next_assigned: vec![false; edge_count],
            remaining_len: vec![0; edge_count],
            last_by_edge: vec![None; edge_count],
            route_by_first: vec![None; edge_count],
            owner_by_edge: vec![None; edge_count],
            kind_by_edge: vec![None; edge_count],
            edges_by_owner: vec![Vec::new(); region_count],
            binding_by_entry: vec![None; edge_count],
            visit_epoch: vec![0; edge_count],
            next_epoch: 0,
        }
    }

    fn binding(&self, entry: EdgeRef) -> Option<ForwardRouteId> {
        self.binding_by_entry.get(entry.index()).copied().flatten()
    }

    pub(super) fn contains_edge(&self, edge: EdgeRef) -> bool {
        self.next_assigned
            .get(edge.index())
            .copied()
            .unwrap_or(false)
    }

    pub(super) fn binding_for_transfer(
        &self,
        entry: EdgeRef,
        transfer: EdgeTransfer,
    ) -> Option<ForwardRouteId> {
        let route = self.binding(entry)?;
        let kind = self.routes.get(route.index())?.kind;
        matches!(
            (transfer, kind),
            (EdgeTransfer::Break(_), ForwardRouteKind::ExclusiveBreak)
                | (
                    EdgeTransfer::Continue(_),
                    ForwardRouteKind::ContinueToTarget
                )
                | (EdgeTransfer::Continue(_), ForwardRouteKind::ContinueLatch)
                | (
                    EdgeTransfer::Continue(_),
                    ForwardRouteKind::RepeatConditionArc(_)
                )
        )
        .then_some(route)
    }

    pub(super) fn remap_conditions(
        &mut self,
        condition_map: &[Option<super::super::ConditionPlanId>],
    ) -> Result<(), StructureError> {
        let remap = |kind: ForwardRouteKind| -> Result<ForwardRouteKind, StructureError> {
            let ForwardRouteKind::RepeatConditionArc(mut arc) = kind else {
                return Ok(kind);
            };
            arc.condition = condition_map
                .get(arc.condition.index())
                .copied()
                .flatten()
                .ok_or_else(|| {
                    StructureError::invalid(
                        "repeat forward route condition was not selected into the final plan",
                    )
                })?;
            Ok(ForwardRouteKind::RepeatConditionArc(arc))
        };
        for route in &mut self.routes {
            route.kind = remap(route.kind)?;
        }
        for kind in self.kind_by_edge.iter_mut().flatten() {
            *kind = remap(*kind)?;
        }
        Ok(())
    }

    pub(super) fn bind(
        &mut self,
        entry: EdgeRef,
        route: ForwardRouteId,
    ) -> Result<(), StructureError> {
        let slot = self
            .binding_by_entry
            .get_mut(entry.index())
            .ok_or_else(|| StructureError::invalid("forward route entry is outside the CFG"))?;
        if slot.replace(route).is_some_and(|old| old != route) {
            return Err(StructureError::invalid(format!(
                "{entry} is bound to conflicting forwarding routes"
            )));
        }
        Ok(())
    }

    pub(super) fn install(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        edges: &[EdgeRef],
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        let Some((&first, &last)) = edges.first().zip(edges.last()) else {
            return Ok(None);
        };
        self.install_iter(
            cfg,
            kind,
            loop_region,
            FunctionalForwardPath {
                first,
                last,
                len: edges.len(),
            },
            edges.iter().copied(),
        )
    }

    pub(super) fn install_functional(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        path: FunctionalForwardPath,
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        self.install_iter(
            cfg,
            kind,
            loop_region,
            path,
            FunctionalForwardPathEdges::new(cfg, path),
        )
    }

    pub(super) fn install_functional_composed(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        prefix: FunctionalForwardPath,
        suffix: &[EdgeRef],
    ) -> Result<Option<ForwardRouteId>, StructureError> {
        let len = prefix
            .len
            .checked_add(suffix.len())
            .ok_or_else(|| StructureError::invalid("forward route length overflow"))?;
        let last = suffix.last().copied().unwrap_or(prefix.last);
        self.install_iter(
            cfg,
            kind,
            loop_region,
            FunctionalForwardPath {
                first: prefix.first,
                last,
                len,
            },
            FunctionalForwardPathEdges::new(cfg, prefix).chain(suffix.iter().copied()),
        )
    }

    fn install_iter<I>(
        &mut self,
        cfg: &Cfg,
        kind: ForwardRouteKind,
        loop_region: RegionId,
        path: FunctionalForwardPath,
        edges: I,
    ) -> Result<Option<ForwardRouteId>, StructureError>
    where
        I: Iterator<Item = EdgeRef>,
    {
        let FunctionalForwardPath { first, last, len } = path;
        let first_cfg = cfg.edges.get(first.index()).ok_or_else(|| {
            StructureError::invalid(format!("forward route references missing {first}"))
        })?;
        let last_cfg = cfg.edges.get(last.index()).ok_or_else(|| {
            StructureError::invalid(format!("forward route references missing {last}"))
        })?;
        let candidate = ForwardRoutePlan {
            kind,
            loop_region,
            first,
            last,
            start: first_cfg.from,
            target: last_cfg.to,
            len,
        };
        if let Some(existing) = self.route_by_first.get(first.index()).copied().flatten() {
            if self.routes.get(existing.index()) == Some(&candidate) {
                return Ok(Some(existing));
            }
            return Err(StructureError::invalid(format!(
                "{first} starts conflicting forwarding routes: existing={:?}, candidate={candidate:?}",
                self.routes[existing.index()],
            )));
        }
        self.next_epoch = self
            .next_epoch
            .checked_add(1)
            .ok_or_else(|| StructureError::invalid("forward route epoch overflow"))?;

        let mut edges = edges.peekable();
        let mut position = 0usize;
        let mut reused_suffix = false;
        while let Some(edge) = edges.next() {
            let cfg_edge = cfg.edges.get(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            let expected_next = edges.peek().copied();
            if let Some(next) = expected_next {
                let next_cfg = cfg.edges.get(next.index()).ok_or_else(|| {
                    StructureError::invalid(format!("forward route references missing {next}"))
                })?;
                if cfg_edge.to != next_cfg.from {
                    return Err(StructureError::invalid(format!(
                        "forward route is not contiguous between {edge} and {next}"
                    )));
                }
            }
            let visit = self.visit_epoch.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if std::mem::replace(visit, self.next_epoch) == self.next_epoch {
                return Err(StructureError::invalid(format!(
                    "forward route contains a cycle at {edge}"
                )));
            }
            let expected_remaining = len.checked_sub(position).ok_or_else(|| {
                StructureError::invalid("forward route contains more edges than its frozen length")
            })?;
            let next_slot = self.next.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            let assigned = self.next_assigned.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if *assigned {
                if *next_slot != expected_next
                    || self.remaining_len[edge.index()] != expected_remaining
                    || self.last_by_edge[edge.index()] != Some(last)
                    || self.owner_by_edge[edge.index()] != Some(loop_region)
                    || self.kind_by_edge[edge.index()] != Some(kind)
                {
                    return Err(StructureError::invalid(format!(
                        "{edge} has a conflicting forwarding suffix"
                    )));
                }
                // `next` is functional. Matching the first shared edge, its next edge,
                // remaining length and terminal proves that the already frozen suffix
                // is the same route, so shared pads are never walked again.
                reused_suffix = true;
                break;
            }
            *next_slot = expected_next;
            *assigned = true;
            self.remaining_len[edge.index()] = expected_remaining;
            self.last_by_edge[edge.index()] = Some(last);
            let owner = self.owner_by_edge.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if owner.is_some_and(|owner| owner != loop_region) {
                return Err(StructureError::invalid(format!(
                    "{edge} is shared by forwarding routes from different loops"
                )));
            }
            *owner = Some(loop_region);
            let edge_kind = self.kind_by_edge.get_mut(edge.index()).ok_or_else(|| {
                StructureError::invalid(format!("forward route references missing {edge}"))
            })?;
            if edge_kind.is_some_and(|edge_kind| edge_kind != kind) {
                return Err(StructureError::invalid(format!(
                    "{edge} is shared by forwarding routes with different semantics"
                )));
            }
            *edge_kind = Some(kind);
            self.edges_by_owner
                .get_mut(loop_region.index())
                .ok_or_else(|| {
                    StructureError::invalid("forward route owner is outside the region arena")
                })?
                .push(edge);
            position += 1;
        }
        if !reused_suffix && position != len {
            return Err(StructureError::invalid(
                "forward route ended before its frozen length",
            ));
        }
        let id = ForwardRouteId(self.routes.len());
        self.route_by_first[first.index()] = Some(id);
        self.routes.push(candidate);
        Ok(Some(id))
    }

    pub(super) fn freeze(
        mut self,
        edge_plans: &mut [EdgePlan],
    ) -> Result<ForwardRouteArena, StructureError> {
        let mut used = vec![false; self.routes.len()];
        for edge in edge_plans.iter() {
            if let Some(route) = edge.forward_route {
                let slot = used.get_mut(route.index()).ok_or_else(|| {
                    StructureError::invalid("forward route entry references a missing route")
                })?;
                *slot = true;
            }
        }
        let mut remap = vec![None; self.routes.len()];
        let mut routes = Vec::new();
        for (index, route) in self.routes.iter().copied().enumerate() {
            if used[index] {
                let id = ForwardRouteId(routes.len());
                remap[index] = Some(id);
                routes.push(route);
            }
        }
        for edge in edge_plans.iter_mut() {
            if let Some(route) = edge.forward_route {
                edge.forward_route = remap.get(route.index()).copied().flatten();
            }
        }

        let mut retained = vec![0usize; self.next.len()];
        for (index, route) in self.routes.iter().enumerate() {
            if used[index] {
                retained[route.first.index()] = retained[route.first.index()]
                    .checked_add(1)
                    .ok_or_else(|| {
                        StructureError::invalid("forward route retain count overflow")
                    })?;
            }
        }
        let mut full_children = vec![Vec::<usize>::new(); self.next.len()];
        let mut full_roots = Vec::new();
        for (index, assigned) in self.next_assigned.iter().copied().enumerate() {
            if !assigned {
                continue;
            }
            if let Some(next) = self.next[index] {
                full_children[next.index()].push(index);
            } else {
                full_roots.push(index);
            }
        }
        let mut full_order = Vec::new();
        let mut full_seen = vec![false; self.next.len()];
        let mut full_stack = full_roots;
        while let Some(index) = full_stack.pop() {
            if std::mem::replace(&mut full_seen[index], true) {
                return Err(StructureError::invalid(
                    "forward route graph contains a cycle or duplicate parent",
                ));
            }
            full_order.push(index);
            full_stack.extend(full_children[index].iter().copied());
        }
        if self
            .next_assigned
            .iter()
            .enumerate()
            .any(|(index, assigned)| *assigned && !full_seen[index])
        {
            return Err(StructureError::invalid(
                "forward route graph contains a cycle",
            ));
        }
        for index in full_order.into_iter().rev() {
            if retained[index] == 0 {
                continue;
            }
            if let Some(next) = self.next[index] {
                retained[next.index()] = retained[next.index()]
                    .checked_add(retained[index])
                    .ok_or_else(|| {
                        StructureError::invalid("forward route retain count overflow")
                    })?;
            }
        }
        for (index, retained) in retained.iter().copied().enumerate() {
            if retained == 0 {
                self.next[index] = None;
                self.next_assigned[index] = false;
                self.owner_by_edge[index] = None;
                self.kind_by_edge[index] = None;
            }
        }

        let mut children = vec![Vec::<EdgeRef>::new(); self.next.len()];
        let mut roots = Vec::new();
        for (index, assigned) in self.next_assigned.iter().copied().enumerate() {
            if !assigned {
                continue;
            }
            let edge = EdgeRef(index);
            if let Some(next) = self.next[index] {
                let slot = children.get_mut(next.index()).ok_or_else(|| {
                    StructureError::invalid(format!("{edge} has a missing forward successor"))
                })?;
                slot.push(edge);
            } else {
                roots.push(edge);
            }
        }
        let mut preorder = vec![usize::MAX; self.next.len()];
        let mut subtree_end = vec![usize::MAX; self.next.len()];
        let mut depth = vec![usize::MAX; self.next.len()];
        let mut clock = 0usize;
        let mut stack = Vec::new();
        for root in roots {
            depth[root.index()] = 0;
            stack.push((root, false));
            while let Some((edge, exiting)) = stack.pop() {
                if exiting {
                    subtree_end[edge.index()] = clock;
                    continue;
                }
                if preorder[edge.index()] != usize::MAX {
                    return Err(StructureError::invalid(format!(
                        "forward route graph contains a cycle or duplicate parent at {edge}"
                    )));
                }
                preorder[edge.index()] = clock;
                clock = clock
                    .checked_add(1)
                    .ok_or_else(|| StructureError::invalid("forward route rank overflow"))?;
                stack.push((edge, true));
                for child in children[edge.index()].iter().rev().copied() {
                    depth[child.index()] = depth[edge.index()]
                        .checked_add(1)
                        .ok_or_else(|| StructureError::invalid("forward route depth overflow"))?;
                    stack.push((child, false));
                }
            }
        }
        if let Some(index) = self
            .next_assigned
            .iter()
            .enumerate()
            .find_map(|(index, assigned)| {
                (*assigned && preorder[index] == usize::MAX).then_some(index)
            })
        {
            return Err(StructureError::invalid(format!(
                "forward route graph contains a cycle at edge #{index}"
            )));
        }
        Ok(ForwardRouteArena {
            routes,
            next: self.next,
            preorder,
            subtree_end,
            depth,
            owner_by_edge: self.owner_by_edge,
            kind_by_edge: self.kind_by_edge,
        })
    }
}

pub(super) struct ForwardRouteArena {
    pub(super) routes: Vec<ForwardRoutePlan>,
    pub(super) next: Vec<Option<EdgeRef>>,
    pub(super) preorder: Vec<usize>,
    pub(super) subtree_end: Vec<usize>,
    pub(super) depth: Vec<usize>,
    pub(super) owner_by_edge: Vec<Option<RegionId>>,
    pub(super) kind_by_edge: Vec<Option<ForwardRouteKind>>,
}
