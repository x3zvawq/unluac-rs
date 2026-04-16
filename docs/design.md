# 维护地图

这组文档是仓库的代码导航地图。每章按 **入口 → 模块布局 → 数据流 → pass 清单 → 排错指引** 组织，
目的是让维护者最快地定位「某个问题出在哪一层、该看哪个文件、该 dump 什么」。

## Pipeline 总览

```text
bytes ──→ Parser ──→ Transformer ──→ CFG ──→ GraphFacts ──→ Dataflow
                                                                │
Generate ←── Naming ←── Readability ←── AST ←── HIR ←── StructureFacts
```

| 关键文件 | 作用 |
|---|---|
| `src/decompile/pipeline.rs` | 主入口 `decompile(bytes, options)`，线性推进各阶段 |
| `src/decompile/state.rs` | 阶段枚举 `DecompileStage` + 状态容器 `DecompileState` |
| `src/decompile/contracts.rs` | 层间稳定类型别名（`CfgGraph`、`HirChunk` 等） |
| `src/decompile/options.rs` | 顶层选项 `DecompileOptions`，统一默认值补齐 |
| `src/decompile/debug.rs` | `define_stage_dump!` 宏 + `collect_stage_dump` 调度 |
| `src/scheduler.rs` | HIR Simplify 与 AST Readability 共用的 invalidation-driven 调度器 |

## 分层文档

| # | 层 | 文档 | 关键入口函数 |
|---|---|---|---|
| 0 | 总览 | [0.introduce.md](./design/0.introduce.md) | — |
| 1 | Parser | [1.parser.md](./design/1.parser.md) | `parse_chunk` |
| 2 | Transformer | [2.transformer.md](./design/2.transformer.md) | `lower_chunk` |
| 3 | CFG / GraphFacts / Dataflow | [3.cfg-dataflow.md](./design/3.cfg-dataflow.md) | `build_cfg_proto` / `analyze_graph_facts` / `analyze_dataflow` |
| 4 | StructureFacts | [4.structure.md](./design/4.structure.md) | `analyze_structure` |
| 5 | HIR | [5.hir.md](./design/5.hir.md) | `analyze_hir` |
| 6 | AST | [6.ast.md](./design/6.ast.md) | `lower_ast` |
| 7 | Readability | [7.readability.md](./design/7.readability.md) | `make_readable` |
| 8 | Naming | [8.naming.md](./design/8.naming.md) | `assign_names_with_evidence` |
| 9 | Generate | [9.generate.md](./design/9.generate.md) | `generate_chunk` |
| 10 | Debugging | [10.debugging.md](./design/10.debugging.md) | `collect_stage_dump` / `--dump-pass` |
| 11 | Test | [11.test.md](./design/11.test.md) | `cargo unit-test` |

## 推荐阅读顺序

1. 先读 [0.introduce.md](./design/0.introduce.md) 了解全局边界与共享设施。
2. 改某一层时，读对应层文档 + 它的前一层文档。
3. 改跨层问题时，从最早可能持有该事实的层开始看，不要从报错位置开始补丁式修复。

## 核心维护原则

- **单向依赖**：后层只消费前层事实，不反向侵入。
- **单一事实源**：某事实在前层显式保存后，后层只通过 query/accessor 消费。
- **结构优先**：不用特判 / fallback / 后层兜底掩盖前层事实缺失。
- **共享优先**：先复用已有 helper / macro / walker / visitor，再考虑新增。
- **输出层纯粹**：Readability、Naming、Generate 不承担前层恢复失败的补救职责。
