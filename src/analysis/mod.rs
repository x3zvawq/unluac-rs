//! Analysis 阶段：为每个 proto 构建规范化 CFG、图论事实、Pruned SSA 与数据流摘要。

pub mod cfg;
pub mod dataflow;
#[cfg(feature = "decompile-debug")]
mod debug;
mod error;
mod graph;
pub mod graph_facts;
pub mod ssa;

pub use cfg::{
    BasicBlock, BlockId, BlockKind, BoolLoadBlock, Cfg, CfgGraph, Edge, EdgeId, EdgeKind,
    InstrRange, LoopProtocolHint,
};
pub use dataflow::{DataflowFacts, EffectClass, OpenPackLink, classify_effect};
#[cfg(feature = "decompile-debug")]
pub use debug::dump_analysis;
#[cfg(not(feature = "decompile-debug"))]
mod debug {
    crate::debug::define_unavailable_stage_dump!(dump_analysis);
}
#[cfg(not(feature = "decompile-debug"))]
pub use debug::dump_analysis;
pub use error::AnalysisError;
pub use graph_facts::{GraphFacts, NaturalLoop, SccInfo};
pub use ssa::{PhiId, PhiNode, SlotKey, SsaDef, SsaForm, UseSite, ValueId};

use crate::decompile::{DecompileContext, DecompileError, DecompileState};
use crate::transformer::{LoweredChunk, LoweredProto};

/// 单个 proto 的完整分析产物（按 DFS 先序编号）。
pub struct ProtoAnalysis {
    pub proto_id: usize,
    pub parent: Option<usize>,
    pub children: Vec<usize>,
    pub cfg: Cfg,
    pub graph: GraphFacts,
    pub ssa: SsaForm,
    pub dataflow: DataflowFacts,
}

/// 整个 chunk 的 Analysis 阶段产物。
pub struct AnalysisChunk {
    /// DFS 先序平铺的 proto 分析表（索引 0 为入口主函数）。
    pub protos: Vec<ProtoAnalysis>,
    /// 保留树形 CfgGraph，供 WASM/Web 前端直接投影。
    pub cfg_graph: CfgGraph,
}

impl std::fmt::Debug for ProtoAnalysis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ProtoAnalysis")
            .field("proto_id", &self.proto_id)
            .field("blocks", &self.cfg.blocks.len())
            .field("loops", &self.graph.natural_loops.len())
            .field("phis", &self.ssa.phis.len())
            .finish()
    }
}

impl std::fmt::Debug for AnalysisChunk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnalysisChunk")
            .field("protos", &self.protos.len())
            .finish()
    }
}

/// 主流水线 Analysis 阶段入口。
pub(crate) fn analyze_stage(
    state: &mut DecompileState,
    context: &DecompileContext<'_>,
) -> Result<(), DecompileError> {
    let lowered = state.require_lowered()?;
    let chunk = {
        let _timing = context.timings.scope("cfg-ssa-dataflow");
        analyze_chunk(lowered)?
    };
    state.analysis = Some(chunk);
    Ok(())
}

/// 分析整个 `LoweredChunk`（显式迭代 DFS 先序，避免深层函数嵌套爆栈）。
pub fn analyze_chunk(chunk: &LoweredChunk) -> Result<AnalysisChunk, AnalysisError> {
    struct Frame<'a> {
        proto: &'a LoweredProto,
        proto_id: usize,
        parent: Option<usize>,
        next_child: usize,
        child_ids: Vec<usize>,
        child_cfgs: Vec<CfgGraph>,
    }

    let mut protos: Vec<Option<ProtoAnalysis>> = Vec::new();
    let mut stack = vec![Frame {
        proto: &chunk.main,
        proto_id: 0,
        parent: None,
        next_child: 0,
        child_ids: Vec::with_capacity(chunk.main.children.len()),
        child_cfgs: Vec::with_capacity(chunk.main.children.len()),
    }];
    protos.push(None);

    let mut root_cfg_graph = None;

    while let Some(frame) = stack.last_mut() {
        if frame.next_child < frame.proto.children.len() {
            let child_idx = frame.next_child;
            frame.next_child += 1;
            let parent_id = frame.proto_id;
            let child_id = protos.len();
            frame.child_ids.push(child_id);
            protos.push(None);
            let child_proto = frame.proto.children[child_idx].as_ref();
            stack.push(Frame {
                proto: child_proto,
                proto_id: child_id,
                parent: Some(parent_id),
                next_child: 0,
                child_ids: Vec::with_capacity(child_proto.children.len()),
                child_cfgs: Vec::with_capacity(child_proto.children.len()),
            });
            continue;
        }

        let frame = stack.pop().expect("frame stack is non-empty");
        let cfg = cfg::build_cfg(frame.proto_id, frame.proto)?;
        let graph = graph_facts::compute_graph_facts(frame.proto_id, &cfg)?;
        let (open_by_prod, open_by_cons) = dataflow::compute_open_pack_links(frame.proto, &cfg);
        let ssa = ssa::build_ssa(frame.proto, &cfg, &graph, &open_by_cons);
        let dataflow = dataflow::compute_dataflow(
            frame.proto,
            &cfg,
            &ssa,
            open_by_prod,
            open_by_cons,
        );
        let cfg_node = CfgGraph {
            cfg: cfg.clone(),
            children: frame.child_cfgs,
        };
        protos[frame.proto_id] = Some(ProtoAnalysis {
            proto_id: frame.proto_id,
            parent: frame.parent,
            children: frame.child_ids,
            cfg,
            graph,
            ssa,
            dataflow,
        });
        if let Some(parent) = stack.last_mut() {
            parent.child_cfgs.push(cfg_node);
        } else {
            root_cfg_graph = Some(cfg_node);
        }
    }

    let protos = protos
        .into_iter()
        .map(|p| p.expect("every proto slot filled"))
        .collect();
    let cfg_graph = root_cfg_graph.expect("root CFG graph built");
    Ok(AnalysisChunk { protos, cfg_graph })
}
