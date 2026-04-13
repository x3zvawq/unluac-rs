//! `decompile_rich` 的结构化返回类型。
//!
//! 这些 DTO 是 WASM 桥接层专用的投影类型，从 `DecompileState` 中提取前端
//! 可视化所需的数据子集并序列化为 JSON。核心库类型不带 `Serialize`，因此
//! 在这一层做转换可以保持核心库零 serde 依赖。
//!
//! 主要暴露：
//! - proto 树元数据（名称、行号、参数、upvalue 数等）
//! - 每个 proto 的 CFG（block + edge + 人类可读指令文本）
//! - 反编译生成的源码和警告
//!
//! 输入：`DecompileResult`
//! 输出：`WasmRichResult` → JSON

use serde::Serialize;

use unluac::cfg::{BlockKind, CfgGraph, EdgeKind};
use unluac::decompile::DecompileResult;
use unluac::parser::{RawLiteralConst, RawProto, RawString, format_raw_instr};
use unluac::transformer::{format_low_instr, LoweredProto, RawInstrRef};

// ── 顶层结果 ──────────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmRichResult {
    /// 反编译生成的完整 Lua 源码
    pub source: String,
    /// 生成阶段的警告
    pub warnings: Vec<String>,
    /// proto 元数据（DFS 序展平）
    pub protos: Vec<WasmProtoMeta>,
    /// 每个 proto 的 CFG（与 protos 平行数组，index 一致）
    pub cfgs: Vec<WasmProtoCfg>,
}

// ── Proto 元数据 ──────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmProtoMeta {
    /// DFS 遍历序号（0 = 主 proto）
    pub id: usize,
    /// 源文件名（debug info）
    pub name: Option<String>,
    pub line_start: u32,
    pub line_end: u32,
    pub num_params: u8,
    pub is_vararg: bool,
    pub num_upvalues: usize,
    pub num_constants: usize,
    pub num_instructions: usize,
    /// 常量池的字面量列表（人类可读形式）
    pub constants: Vec<WasmConstant>,
    /// 子 proto 的 DFS ID 列表
    pub children: Vec<usize>,
}

/// 单个常量的可序列化投影。
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmConstant {
    /// 常量在池中的索引（0-based）
    pub index: usize,
    /// 类型标签：nil / boolean / integer / number / string / int64 / uint64 / complex
    #[serde(rename = "type")]
    pub ty: &'static str,
    /// 人类可读的值表示
    pub display: String,
}

// ── CFG ──────────────────────────────────────────────────

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmProtoCfg {
    pub proto_id: usize,
    pub blocks: Vec<WasmCfgBlock>,
    pub edges: Vec<WasmCfgEdge>,
    pub entry_block: usize,
    pub exit_block: usize,
    /// 拓扑序 block ID 列表
    pub block_order: Vec<usize>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmCfgBlock {
    pub id: usize,
    pub kind: &'static str,
    /// 人类可读的 Low-IR 指令行
    pub instructions: Vec<String>,
    /// 对应的原始字节码指令行（通过 LoweringMap 映射）
    pub raw_instructions: Vec<String>,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WasmCfgEdge {
    pub from: usize,
    pub to: usize,
    pub kind: &'static str,
}

// ── 投影逻辑 ────────────────────────────────────────────

/// 从 `DecompileResult` 提取前端所需的结构化数据。
pub fn project_rich_result(result: &DecompileResult) -> WasmRichResult {
    let (source, warnings) = result
        .state
        .generated
        .as_ref()
        .map(|g| (g.source.clone(), g.warnings.clone()))
        .unwrap_or_default();

    let mut protos = Vec::new();
    let mut cfgs = Vec::new();

    // 从 raw_chunk 提取 proto 元数据（DFS 序）
    if let Some(raw_chunk) = &result.state.raw_chunk {
        collect_proto_meta(&raw_chunk.main, &mut protos, &mut 0);
    }

    // 从 lowered + cfg + raw_chunk 提取 CFG 数据
    if let (Some(lowered), Some(cfg_graph)) = (&result.state.lowered, &result.state.cfg) {
        let raw_main = result.state.raw_chunk.as_ref().map(|c| &c.main);
        collect_cfgs(&lowered.main, raw_main, cfg_graph, &mut cfgs, &mut 0);
    }

    WasmRichResult {
        source,
        warnings,
        protos,
        cfgs,
    }
}

/// DFS 收集 proto 元数据，`counter` 跟踪全局 ID 分配。
fn collect_proto_meta(proto: &RawProto, out: &mut Vec<WasmProtoMeta>, counter: &mut usize) {
    let my_id = *counter;
    *counter += 1;

    let child_start_id = *counter;
    let num_children = proto.common.children.len();

    // 先预留位置，后面填充 children
    out.push(WasmProtoMeta {
        id: my_id,
        name: proto.common.source.as_ref().map(raw_string_to_string),
        line_start: proto.common.line_range.defined_start,
        line_end: proto.common.line_range.defined_end,
        num_params: proto.common.signature.num_params,
        is_vararg: proto.common.signature.is_vararg,
        num_upvalues: proto.common.upvalues.common.count as usize,
        num_constants: proto.common.constants.common.literals.len(),
        num_instructions: proto.common.instructions.len(),
        constants: proto
            .common
            .constants
            .common
            .literals
            .iter()
            .enumerate()
            .map(|(i, lit)| project_constant(i, lit))
            .collect(),
        children: Vec::with_capacity(num_children),
    });

    // 递归收集子 proto
    for child in &proto.common.children {
        let child_id = *counter;
        out[my_id].children.push(child_id);
        collect_proto_meta(child, out, counter);
    }

    // 断言子序列连续
    debug_assert_eq!(
        out[my_id].children.first().copied(),
        if num_children > 0 {
            Some(child_start_id)
        } else {
            None
        }
    );
}

/// DFS 收集每个 proto 的 CFG。
///
/// `raw_proto` 为 `Some` 时会通过 `LoweringMap` 将每条 Low-IR 指令
/// 映射回原始字节码并格式化为 `raw_instructions`；否则留空。
fn collect_cfgs(
    lowered: &LoweredProto,
    raw_proto: Option<&RawProto>,
    cfg_graph: &CfgGraph,
    out: &mut Vec<WasmProtoCfg>,
    counter: &mut usize,
) {
    let proto_id = *counter;
    *counter += 1;

    let raw_instrs = raw_proto.map(|p| &p.common.instructions);

    let cfg = &cfg_graph.cfg;
    let blocks: Vec<WasmCfgBlock> = cfg
        .blocks
        .iter()
        .enumerate()
        .map(|(i, block)| {
            let mut instructions = Vec::new();
            let mut raw_instructions = Vec::new();

            for offset in 0..block.instrs.len {
                let idx = block.instrs.start.index() + offset;
                if let Some(low_instr) = lowered.instrs.get(idx) {
                    instructions.push(format_low_instr(low_instr));

                    // 通过 lowering_map 找到对应的原始指令
                    if let Some(raw_vec) = raw_instrs {
                        let raw_refs = lowered.lowering_map.low_to_raw.get(idx);
                        let raw_text: Vec<String> = raw_refs
                            .map(|refs| {
                                refs.iter()
                                    .filter_map(|RawInstrRef(raw_idx)| {
                                        raw_vec.get(*raw_idx).map(format_raw_instr)
                                    })
                                    .collect()
                            })
                            .unwrap_or_default();
                        raw_instructions.push(raw_text.join("; "));
                    }
                }
            }

            WasmCfgBlock {
                id: i,
                kind: block_kind_str(block.kind),
                instructions,
                raw_instructions,
            }
        })
        .collect();

    let edges: Vec<WasmCfgEdge> = cfg
        .edges
        .iter()
        .map(|edge| WasmCfgEdge {
            from: edge.from.index(),
            to: edge.to.index(),
            kind: edge_kind_str(edge.kind),
        })
        .collect();

    out.push(WasmProtoCfg {
        proto_id,
        blocks,
        edges,
        entry_block: cfg.entry_block.index(),
        exit_block: cfg.exit_block.index(),
        block_order: cfg.block_order.iter().map(|b| b.index()).collect(),
    });

    // 递归子 proto
    let raw_children: Vec<Option<&RawProto>> = raw_proto
        .map(|p| p.common.children.iter().map(Some).collect())
        .unwrap_or_else(|| vec![None; lowered.children.len()]);

    for ((child_lowered, child_cfg), child_raw) in lowered
        .children
        .iter()
        .zip(cfg_graph.children.iter())
        .zip(raw_children)
    {
        collect_cfgs(child_lowered, child_raw, child_cfg, out, counter);
    }
}

fn block_kind_str(kind: BlockKind) -> &'static str {
    match kind {
        BlockKind::Normal => "normal",
        BlockKind::SyntheticExit => "synthetic-exit",
    }
}

fn edge_kind_str(kind: EdgeKind) -> &'static str {
    match kind {
        EdgeKind::Fallthrough => "fallthrough",
        EdgeKind::Jump => "jump",
        EdgeKind::BranchTrue => "branch-true",
        EdgeKind::BranchFalse => "branch-false",
        EdgeKind::LoopBody => "loop-body",
        EdgeKind::LoopExit => "loop-exit",
        EdgeKind::Return => "return",
        EdgeKind::TailCall => "tail-call",
    }
}

fn raw_string_to_string(s: &RawString) -> String {
    // 优先使用已解码文本，否则 lossy UTF-8
    if let Some(decoded) = &s.text {
        decoded.value.clone()
    } else {
        String::from_utf8_lossy(&s.bytes).into_owned()
    }
}

fn project_constant(index: usize, lit: &RawLiteralConst) -> WasmConstant {
    let (ty, display) = match lit {
        RawLiteralConst::Nil => ("nil", "nil".to_owned()),
        RawLiteralConst::Boolean(b) => ("boolean", b.to_string()),
        RawLiteralConst::Integer(n) => ("integer", n.to_string()),
        RawLiteralConst::Number(n) => ("number", format!("{n}")),
        RawLiteralConst::String(s) => ("string", format!("\"{}\"", raw_string_to_string(s))),
        RawLiteralConst::Int64(n) => ("int64", format!("{n}LL")),
        RawLiteralConst::UInt64(n) => ("uint64", format!("{n}ULL")),
        RawLiteralConst::Complex { real, imag } => ("complex", format!("{real}+{imag}i")),
    };
    WasmConstant {
        index,
        ty,
        display,
    }
}
