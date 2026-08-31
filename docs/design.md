# 维护地图

这组文档是仓库的代码导航地图。每章按 **入口 → 模块布局 → 数据流 → pass 清单 → 排错指引** 组织，
目的是让维护者最快地定位「某个问题出在哪一层、该看哪个文件、该 dump 什么」。

## Pipeline 总览

```text
bytes ──→ Parser ──→ Transformer ──→ Structure ──→ HIR ──→ AST ──→ Generate
```

| 关键文件 | 作用 |
| --- | --- |
| `src/decompile/pipeline.rs` | 主入口 `decompile(bytes, options)`，创建一次调用的状态、上下文与结果收尾 |
| `src/decompile/stages.rs` | 固定外层阶段调度表，统一处理阶段执行、timing、debug dump 与 target-stage 停止点 |
| `src/decompile/state.rs` | 阶段枚举 `DecompileStage` + 状态容器 `DecompileState` |
| `src/decompile/contracts.rs` | 层间稳定类型别名（`CfgGraph`、`HirChunk` 等） |
| `src/decompile/options.rs` | 顶层选项 `DecompileOptions` 与 `DebugOptions`，统一默认值补齐 |
| `src/debug.rs` | 跨层 debug 公共类型、聚焦工具与 `define_stage_dump!` 宏 |
| `src/scheduler.rs` | HIR Simplify 与 AST Readability 共用的 invalidation-driven 调度器 |
| `src/recovery.rs` | Structure/HIR proto 级失败事实与最后完成产物合同 |

## 分层文档

| # | 层 | 文档 | 关键入口函数 |
| --- | --- | --- | --- |
| 0 | 总览 | [0.introduce.md](./design/0.introduce.md) | — |
| 1 | Parser | [1.parser.md](./design/1.parser.md) | `parse_input(state, context)` / `parse_chunk_with_dialect` |
| 2 | Transformer | [2.transformer.md](./design/2.transformer.md) | `lower_chunk(state, context)` |
| 3 | Structure | [3.structure.md](./design/3.structure.md) | `analyze_structure_stage` |
| 5 | HIR | [5.hir.md](./design/5.hir.md) | `analyze_hir` |
| 6 | AST | [6.ast.md](./design/6.ast.md) | `analyze_ast_stage` |
| 9 | Generate | [9.generate.md](./design/9.generate.md) | `generate_chunk(state, context)` |
| 10 | Debugging | [10.debugging.md](./design/10.debugging.md) | `dump_*` / `--dump-pass` |
| 11 | Test | [11.test.md](./design/11.test.md) | `cargo unit-test` |

AST 的两个子主题仍保留单独导航，方便按 pass 排错：
[AST readability](./design/7.readability.md) / [AST naming](./design/8.naming.md)。

## 推荐阅读顺序

1. 先读 [0.introduce.md](./design/0.introduce.md) 了解全局边界与共享设施。
2. 改某一层时，读对应层文档 + 它的前一层文档；AST readability / naming 只算 AST 子主题。
3. 改跨层问题时，从最早可能持有该事实的层开始看，不要从报错位置开始补丁式修复。

## 核心维护原则

- **单一事实源**：某事实在前层显式保存后，后层只通过 query/accessor 消费。
- **结构优先**：不用特判 / fallback / 后层兜底掩盖前层事实缺失。
- **共享优先**：先复用已有 helper / macro / walker / visitor，再考虑新增。
- **输出层纯粹**：Readability、Naming、Generate 不承担前层恢复失败的补救职责。

## Pass guard 合同

HIR simplify 与 AST readability pass 的目标不只是“不生成错误源码”，还要尽可能消除
bytecode lowering 留下的机械形状。候选一旦形成，拒绝改写就会直接留下可读性缺口；因此
每个拒绝 guard 都必须在原地用一行 `候选拒绝[...]` 注释说明原因，不能只写“保守处理”。

| 分类 | 含义 | 长期处理 |
| --- | --- | --- |
| `SemanticBarrier:<subtype>` | 已有具体输入能证明改写前后运行语义不等价 | 可以保留，但注释必须指向最小反例或回归 case |
| `ProofIncomplete` | 候选可能等价，但当前 IR 事实或分析不足以证明 | 必须写明缺失事实，并继续增强前层事实或本 pass 证明 |
| `ResourceLimit` | 因扫描长度、搜索空间、候选数或复杂度上限放弃 | 必须写明受限算法，并继续优化索引、窗口或搜索方法 |
| `PolicyBoundary` | 用户或项目明确选择的源码展示密度 | 可以保留，但不得描述成语义安全要求 |
| `TargetConstraint` | 目标 Lua 方言、语法或编译器硬限制 | 可以保留，并说明对应目标约束 |
| `LayerBoundary` | 候选明确属于另一个层或 pass，且 owner 已确定 | 可以保留，但必须指出负责消费它的 owner |
| `ConvergenceGuard` | fixed-point 不收敛或内部不变量保护 | 属于实现正确性错误，不是候选不等价证明 |

拒绝 guard 之外还必须审计候选的接受证明。若 pass 会提交改写，但所依赖的语义模型、
provenance 或 plan/apply 不变量已知不成立，必须在提交点前写一行 `证明缺陷[...]`，不能把它
记成 `ProofIncomplete`（后者表示拒绝了尚未证明的候选）：

| 分类 | 含义 | 长期处理 |
| --- | --- | --- |
| `PotentialUnsoundness:<subtype>` | 已有最小反例或明确的错误模型，表明当前接受路径可能生成运行语义不等价源码 | 优先修复或收紧接受条件，并补回归 case；修复前不得宣称该 pass 已精确证明 |
| `PotentialPolicyViolation` | 接受路径会删除 debug/source identity 等项目明确保留的证据，但尚无运行语义反例 | 补齐 origin/identity gate 或明确修改项目策略 |
| `InvariantMismatch` | candidate plan 与 apply/rewrite 阶段的形状假设可能漂移，失败时仍提交部分删除 | 改为校验失败不提交，或用 assert/fail-fast 固化内部不变量 |

`SemanticBarrier` 的 subtype 应说明可观察差异，例如 `EvalOrder`、`ValueArity`、
`ControlFlow`、`Scope`、`Capture`、`Lifetime`、`Metamethod`。有效注释需要同时说明哪次
求值、哪个值宽度或哪段生命周期发生变化，并绑定能够观察差异的 case；仅凭形状更复杂、
存在 capture/debug 信息或“理论上可能有副作用”不能升级为语义屏障。无法给出反例时，
应标为 `ProofIncomplete`。

普通形状不属于该 pass 时是 `NotApplicable`，不需要标记。候选尚未逐项形成但整项分析
被停用时写 `分析停用[...]`；搜索空间被截断但已有候选仍可改写时写
`候选搜索裁剪[...]`。这些名字用于区分真实拒绝点，避免把所有 `None` / `false` 都误报为
可读性缺口。

审计按 pass 串行完成。每次先确定候选形成点和职责边界，再沿完整调用链检查其后的所有
early return、循环跳过、helper 失败出口以及最终接受/提交点；为每个 `SemanticBarrier` 和
`PotentialUnsoundness` 构造最小不等价反例，为其余缺口确定优化方向并补正常路径与边界测试。
分类结论只写在对应源码 guard 或提交点，不在设计文档维护 pass 账本。

以下检索是全仓库存量清单的唯一生成方式；设计文档不复制检索结果：

```sh
rg -n 'name: "' src/hir/simplify/mod.rs src/ast/readability/mod.rs
rg -n '候选拒绝\[|分析停用\[|候选搜索裁剪\[|证明缺陷\[' \
  src/hir/simplify src/ast/readability
rg --no-filename -o '候选拒绝\[[^]]+\]|分析停用\[[^]]+\]|候选搜索裁剪\[[^]]+\]|证明缺陷\[[^]]+\]' \
  src/hir/simplify src/ast/readability | sort | uniq -c
```

文本检索只负责列出标记，不能证明审计完整。只有该 pass 及其专用 helper 的拒绝出口、接受
证明与提交阶段都已沿调用链核对并验证，才能宣称审计完成。
