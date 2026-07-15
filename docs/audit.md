# 审计问题与交接清单

> 更新时间：2026-07-15  
> 基线：`2a84dfe` 及其之前的本轮提交  
> 本文只记录已经取证的问题、明确风险和已确认的设计决定。完成项保留在末尾，避免后续重复排查。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 优先级总览

| 优先级 | 状态 | 问题 | 建议主题 |
|---|---|---|---|
| P0 | 已复现 | 任一不可规约边会触发整 proto 的 label/goto fallback，丢弃已经识别出的结构候选 | `refactor(hir): 以mixed lowering替换整proto fallback` |
| P0 | 已复现 | AST `branch-pretty` 仍在从 goto/label 壳恢复控制语义，层次 owner 错误 | `refactor(hir): 将branch control folding迁回HIR` |
| P1 | 已确认越层 | AST `prettify_truthy_ternary` 重新证明真值并重组短路表达式 | `refactor(hir): 统一truthy逻辑规范化owner` |
| P1 | 风险，未构造最小复现 | AST goto fold 的词法屏障未包含 Lua 5.5 `GlobalDecl` | 随 branch control folding 迁移一并消除 |
| P2 | 算法已确认 | AST goto fold 反复全块扫描和重建，最坏为 O(n²) | 在 HIR 迁移中改为一次索引、由内向外改写 |

## P0：整 proto structured/fallback 二选一

### 现象与证据

稳定复现是 `tests/unit-case/lua52_02_goto.lua` 的 `proto#4`：

```bash
cargo unluac \
  -s tests/unit-case/lua52_02_goto.lua \
  -D lua5.2 \
  --dump structure --dump hir --dump ast \
  --dump-pass branch-pretty \
  --proto 4 --proto-depth 0 \
  --stop-after ast --detail verbose --color never
```

当前 Structure 已得到：

- 3 个 `BranchCandidate`；
- 只有 2 条 `GotoRequirement`，原因均为 `irreducible-flow`；
- `#2/#4` 构成不可规约区域，其他区域仍可结构化；
- `#4` 同时出现在 branch region 和 irreducible region，说明当前 `RegionFact` 只是重叠的调试事实，还不是可直接执行的唯一 owner plan。

但 `build_structured_body` 在看到任一不支持的 goto requirement 时直接返回 `None`：

- `src/hir/analyze/structure/body/mod.rs::build_structured_body`
- `src/hir/analyze/lower.rs::build_proto_body`
- `src/hir/analyze/lower.rs::lower_label_goto_body`

结果是整个函数退化成线性 label/goto HIR，已经识别出的局部分支也被丢弃。随后 AST 又把：

```lua
if t0 == 0 then goto L2 end
goto L4
::L2::
```

重新折成：

```lua
if t0 ~= 0 then goto L4 end
::L2::
```

这证明当前 fallback 粒度过粗，也证明 AST 正在重新消费前层已经拥有的控制事实。

### 根因

HIR lowering 只有两个互斥入口：整 proto structured lowering，或整 proto `lower_label_goto_body`。它缺少“可结构化区域正常降低、不可规约区域局部保留 goto”的 mixed lowering。

### 目标不变量

1. 每个 reachable block 恰好归一个 canonical owner：structured candidate 或 unstructured region。
2. 每条 CFG edge 恰好被结构吸收一次，或作为 `GotoRequirement` 显式输出一次。
3. phi copy 继续归 edge owner；跨 structured/unstructured 边界也不能丢失、重复或改序。
4. irreducible region 只保留真正必要的 goto；区域外和区域内仍可证明的局部分支继续消费 `BranchCandidate`。
5. 冲突消解后的 canonical block/region owner 应进入 `StructurePlan`；不要直接把重叠的 `RegionFact` 当执行计划。
6. mixed lowerer 稳定后删除整 proto 的 `lower_label_goto_body` 备用路径，不保留双轨 lowering。

### 推荐实施顺序

1. 先在 `StructurePlan` 建立唯一 block/region owner 和 edge owner，并对覆盖、重复消费、遗漏 edge 做 fail-fast 校验。
2. 让 structured lowerer 能进入局部 unstructured region emitter；region emitter 只输出该区域必要的 label/goto 和 edge copies。
3. 删除 proto 级“任一 goto 即返回 None”的门槛。
4. 删除整 proto fallback，保留真正不可规约区域的局部诊断伪源码。

### 验证重点

- 上述 `lua52_02_goto.lua` 的可结构化分支必须在 HIR 阶段已恢复，AST 不再参与控制恢复。
- Lua 5.1 / 无 goto 方言：可规约部分不得因同 proto 的不可规约区域一起退化；确实不可表达的边继续走宽松诊断伪源码。
- 覆盖 nested branch/loop、phi edge copy、close scope、跨 region live-out 和真正不可规约 CFG。
- 每次实现后运行精确 clippy 与全量 `cargo unit-test --jobs 8`。

## P0：`branch-pretty` 越层恢复控制流

### 已确认越层的逻辑

`src/ast/readability/branch_pretty.rs` 中以下逻辑会消费 goto/label 控制边，而不是单纯改善排版：

- `fold_guard_goto_labels`
- `fold_terminal_goto_else`
- `remove_nop_goto_labels`

全量 unit/regress × 7 方言的本轮扫描中，`lua52_02_goto.lua` 是稳定出现“`branch-pretty` before/after 都含 goto，且 pass 改变控制壳”的现有 case。

### 建议边界

1. 在 HIR simplify 建立独立的 branch-control owner，与只处理“同一 lvalue 选值”的 `branch_value_folding` 分开。
2. HIR pass 只消费已经显式存在的 `HirStmt::If/Goto/Label`，不重新解释 CFG；mixed lowering 仍是更前层根治方案。
3. AST 只保留展示型变换：`not` 交换 then/else、空臂规范化、已结构化 nested guard 合并、终止分支展示拉平。
4. 迁移完成后删除 AST 中对应实现、label 引用统计和控制流 invalidation 依赖，不保留两层 owner。

### 性能边界

当前两个 goto fold 都在 `while` 中重复：

- 构造 label index；
- 扫描整个 block 找候选；
- `mem::take` 后重建整个 `Vec`。

多个 guard 指向同一 label 时最坏 O(n²)。迁移时应一次构造 label 位置和引用计数，按不交叉区间从内向外重写；区间交叉时保守拒绝。不要先原样搬到 HIR，再新增第二轮性能重构。

### Lua 5.5 词法风险

`can_fold_guard_goto_body` 只排除了 `Label`、`LocalDecl` 和 `LocalFunctionDecl`，没有排除 `GlobalDecl`。如果 Lua 5.5 global declaration 在 AST 中具有块级声明范围，把线性尾部搬进新 `if` block 会改变声明范围。

这个风险尚无最小源码复现，不应写成已复现 bug；但也不建议在 AST 再补方言特判。控制 fold 迁到 HIR 后，AST 方言声明节点不再参与该判断，风险会随错误 owner 一起消失。

## P1：truthy ternary 仍在 AST 重组短路语义

`src/ast/readability/branch_pretty.rs::prettify_truthy_ternary` 调用 `is_always_truthy_expr`，并把：

```text
not a and x or y
```

重组为：

```text
a and y or x
```

这依赖 Lua 真值语义和求值顺序证明，与 `docs/design/7.readability.md` 的“AST 不重新综合短路语义”约束冲突。

建议迁到 HIR `logical_simplify` / decision owner：

- 在 HIR 上证明两个分支值恒 truthy；
- 保持调用、表访问和 metamethod 可观察顺序；
- 增加能在 HIR pass dump 中观察 before/after 的源码 case；
- 删除 AST helper 及不再使用的 truthiness import。

## P2：性能扫描结论

目前唯一有明确复杂度证据的热点是上面的 AST goto fold O(n²)。本轮也看到 `decision/eliminate_materialize.rs` 对固定三个元素执行 `remove(0)`，但长度有严格常数上界，不是大文件退化点，不应为它单独重构。

后续性能工作仍应先提供可扩展输入、复杂度证明或 profile，再动实现；不要把普通 `BTreeSet::contains` 或小集合线性操作一概当热点。

## 本轮已完成，不要重复处理

| 提交 | 已解决内容 |
|---|---|
| `489111b` | 在 Agent 约束中明确允许高价值架构替换 |
| `47c49ef` | 以显式 `HirValuePack/HirPackTail` 统一多返回值 owner，修复 TBC/close 与 generic-for source pack |
| `f309f01` | 区分 Source/DiagnosticPseudocode；保留宽松输出和 error 注释；移除 stderr goto 警告；恢复多回边 sibling-latch 循环 |
| `c0c6634` | Lua 5.5 generic-for 同时识别 `Close+Jump` 与非空 `Close-only+fallthrough` 的共同 live-out 出口 |
| `2a84dfe` | 删除 value-pack tail 的裸可变根 API，typed Call 重建从类型边界保持 Call/VarArg 不变量 |

当前基线验证：

- `cargo clippy --workspace --all-targets --all-features --locked -- -D warnings`
- `cargo unit-test --jobs 8`：569/569 entries、1126/1126 protos
- `regress_174_explicit_value_pack`：7/7 entries、56/56 protos
- `regress_175_lua54_close_value_pack`：2/2 entries、8/8 protos
- `regress_153`、`regress_154`、`regress_177` 邻近 Lua 5.5 generic-for/close 回归：3/3

