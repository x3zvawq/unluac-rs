//! canonical phi 图的分量、传播顺序与递归身份。
//!
//! SSA 完成 compact/remap 和 use 索引后一次冻结；这里不依赖区域或循环语法。
//! 例如 p 依赖 q、q 依赖 p 时两者同属递归分量；单独的 p = phi(p, def)
//! 也递归，不能因 consumer 索引省略直接自边而丢掉该事实。

use super::{PhiCandidate, PhiId, SsaValue};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PhiGraphFacts {
    components: Vec<Vec<PhiId>>,
    component_by_phi: Vec<usize>,
    recursive: Vec<bool>,
}

impl PhiGraphFacts {
    pub(crate) fn build(phis: &[PhiCandidate], consumers: &[Vec<PhiId>]) -> Self {
        let mut visited = vec![false; phis.len()];
        let mut postorder = Vec::with_capacity(phis.len());
        for root in 0..phis.len() {
            if visited[root] {
                continue;
            }
            let mut pending = vec![(PhiId(root), false)];
            while let Some((phi, leaving)) = pending.pop() {
                if leaving {
                    postorder.push(phi);
                    continue;
                }
                if std::mem::replace(&mut visited[phi.index()], true) {
                    continue;
                }
                pending.push((phi, true));
                pending.extend(consumers[phi.index()].iter().rev().map(|phi| (*phi, false)));
            }
        }
        let components = crate::graph::strongly_connected_components(
            phis.len(),
            &postorder,
            PhiId::index,
            |phi| {
                phis[phi.index()]
                    .incoming
                    .iter()
                    .filter_map(move |incoming| match incoming.value {
                        SsaValue::Phi(source) if source != phi => Some(source),
                        _ => None,
                    })
            },
        );
        let mut component_by_phi = vec![0; phis.len()];
        let mut recursive = Vec::with_capacity(components.len());
        for (index, members) in components.iter().enumerate() {
            for phi in members {
                component_by_phi[phi.index()] = index;
            }
            recursive.push(
                members.len() > 1
                    || phis[members[0].index()]
                        .incoming
                        .iter()
                        .any(|incoming| incoming.value == SsaValue::Phi(members[0])),
            );
        }
        Self {
            components,
            component_by_phi,
            recursive,
        }
    }

    /// 顺序只对当前 canonical phi 图有效；跨分量 use 边由较小编号指向较大编号。
    pub(crate) fn components(&self) -> &[Vec<PhiId>] {
        &self.components
    }

    pub(crate) fn component_index(&self, phi: PhiId) -> usize {
        self.component_by_phi[phi.index()]
    }

    pub(crate) fn is_recursive(&self, phi: PhiId) -> bool {
        self.recursive[self.component_index(phi)]
    }
}
