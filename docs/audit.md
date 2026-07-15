# 审计问题与交接清单

> 更新时间：2026-07-15  
> 基线：当前 `dev`
> 本文只记录尚未解决且已经取证的问题、明确风险和已确认的设计决定；完成项立即删除。

## 不应回退的决定

1. **宽松生成必须保留**：结构恢复不完整时，用户仍应看到尽可能多的逻辑。宽松模式允许保留必要的 `goto` / `label` 和 `unluac error` 占位；严格模式才要求目标方言可重新编译。
2. **诊断写入输出，不写 stderr**：诊断伪源码由首行 `unluac error` 注释和 `GeneratedChunkKind::DiagnosticPseudocode` 标识，不再额外打印“目标方言不支持 goto/label”的 stderr 警告。
3. **错误注释不能删除**：它既保留其余可读逻辑，也让用户能定位并反馈反编译器缺口。
4. **允许高价值大改**：涉及层次职责、核心数据模型和跨 pass owner 时，直接替换错误架构，不保留兼容层、双轨事实或后层 fallback。

## 优先级总览

| 优先级 | 状态 | 问题 | 建议主题 |
|---|---|---|---|
| P0 | 部分解决 | plain branch/loop island 已能局部降低并保留外层 for 与词法 cleanup；island 自身含 numeric/generic-for 协议或显式 cleanup 时仍会整 proto fallback | `refactor(hir): 完成mixed lowering并删除整proto fallback` |
| P1 | 语料缺口 | Luau conformance 仅 16/49 完成严格反编译与二次编译，另有 unresolved、不收敛和非法 label | 按最小 proto 继续拆分 |

## P0：mixed lowering 尚未覆盖 island for 协议 / 显式 cleanup

### 现象与证据

`tests/unit-case/lua52_02_goto.lua` 的 `proto#4` 已证明 plain branch island 可以局部降低：

```bash
cargo unluac \
  -s tests/unit-case/lua52_02_goto.lua \
  -D lua5.2 \
  --dump hir \
  --proto 4 --proto-depth 0 \
  --stop-after hir --detail verbose --color never
```

当前 HIR 保留 island 外已恢复的 branch，只在 `#2/#4` 不可规约区域输出必要的 label/goto；`regress_182_numeric_for_before_irreducible_goto.lua` 进一步证明 island 之前的 numeric-for 不再随整个 proto 退化。实现已经：

- 将 proto 级门槛收窄为：只有显式边目标属于局部不可规约 island 时才进入 mixed lowering；
- 按 `StructurePlan` 直接 owner 降低 plain Branch/Linear block，membership 不覆盖 Branch owner；
- 每条显式边按精确 `EdgeRef` 物化 phi copy，只对同层真实下一块省略 goto；
- 在真正生成非 fallthrough 边时补齐 label；continuation 有外部 predecessor 时仅在无 live phi 的条件下接回 structured walker；
- 将 active loop 的 post-loop/downstream 出口降成 `break`，并透明跨过唯一 owner 为 `LexicalScope` 的 `Close` pad；
- 在 `StructurePlan` 为每条 `Close/Tbc` 建立唯一 `CleanupDisposition`，HIR 不再从 scope 并集重跑显式 TBC 数据流；
- 沿后支配链选择第一个 island 外 continuation，透明穿过版本相关的单前驱入口 jump pad，并按真实 CFG 边降低 island 内 plain loop owner；
- `regress_183_mixed_irreducible_explicit_close.lua` 证明 island 外显式 `<close>` 不再因缺 label 生成非法源码；
- `regress_184_mixed_irreducible_generic_close.lua` 证明包含 island 的 Lua 5.4/5.5 generic-for 仍保留结构化 `for`。

仍未解决的是不受支持的 island 最终会落回 `lower_label_goto_body`，所以 lowering 依然保留整 proto 双轨。审计还确认：

- raw numeric-for lowering 会漏掉循环边 phi copy，并用 unresolved 多目标赋值代替真实循环状态；mixed emitter 不能复用它；

cleanup owner 的前层唯一化已经完成，但下列缺口仍在：

- island 自身含 numeric/generic-for 协议、显式 TBC 或显式 TBC boundary 时仍拒绝 mixed lowering；
- `terminal_exit_block_is_clone_safe` 同时承担 branch/loop 边界选择与真实 clone eligibility，而 clone API 又没有 predecessor `EdgeRef`；含 cleanup 的合法 clone 确实存在，blanket 禁止会破坏 `regress_181_generic_for_branch_phi.lua`，必须先唯一化共享尾的 phi/cleanup owner；
- 整 proto 的 `lower_label_goto_body` 仍绕过 `CleanupDisposition`，保留双轨 lowering；
- phi incoming 还没有像 edge/cleanup 一样进入唯一 disposition。

因此下一步不是放宽 raw emitter，而是先唯一化 terminal/shared-tail clone 与 phi incoming，再支持 island 内 Loop/显式 cleanup owner；全部形状由 mixed walker 接管后删除 `lower_label_goto_body`。

### 目标不变量

1. 每个 reachable block 恰好归一个直接 executable owner；unstructured membership 仅作为正交区域事实。
2. 每条 CFG edge 恰好被结构吸收一次，或作为 `GotoRequirement` 显式输出一次。
3. phi copy 继续归 edge owner；跨 structured/unstructured 边界也不能丢失、重复或改序。
4. irreducible region 只保留真正必要的 goto；区域外和区域内仍可证明的局部分支继续消费 `BranchCandidate`。
5. 冲突消解后的 block/edge/phi/cleanup owner 应进入 `StructurePlan`；不要直接把重叠候选或集合并集当执行计划。
6. mixed lowerer 稳定后删除整 proto 的 `lower_label_goto_body` 备用路径，不保留双轨 lowering。
7. 每个 Phi incoming 与 Close/TBC 都有唯一 disposition；edge copy、structured merge 与 cleanup owner 互斥且只消费一次。

### 推荐实施顺序

1. 审核 terminal/shared-tail clone，在不破坏 `regress_181_generic_for_branch_phi.lua` 的前提下唯一化共享尾的 phi/cleanup owner。
2. 支持 island 内 numeric/generic-for owner 与显式 cleanup；for 协议继续走结构候选，不能 raw 展开 terminator。
3. 为 phi incoming 建立唯一 disposition，并删除整 proto fallback；无法以目标方言表示的局部边只在 island 内生成诊断伪源码。

最终同时删除自行从 raw candidates 重建的 `branch_by_header/loops_by_header` owner map；所有 block、edge、phi copy 与 close disposition 只消费 `StructurePlan`。

### 验证重点

- `lua52_02_goto.lua` 的可结构化分支必须继续在 HIR 阶段恢复，AST 不参与控制恢复。
- `regress_182_numeric_for_before_irreducible_goto.lua` 的 numeric-for 必须保持结构化，island 只覆盖后续不可规约流。
- `regress_183_mixed_irreducible_explicit_close.lua` 在 Lua 5.4/5.5 必须重新编译通过，且显式 `<close>` 仍由原词法 owner 消费。
- `regress_184_mixed_irreducible_generic_close.lua` 在 Lua 5.4/5.5 必须保留 generic-for，不得整 proto 退回 raw label/goto。
- `regress_187_irreducible_plain_loop_owner.lua` 必须只在 island 内保留必要 goto，plain loop header 的 phi copy 不能丢失。
- Lua 5.1 / 无 goto 方言：可规约部分不得因同 proto 的不可规约区域一起退化；确实不可表达的边继续走宽松诊断伪源码。
- 覆盖 nested branch/loop、phi edge copy、close scope、跨 region live-out 和真正不可规约 CFG。
- 每次实现后运行精确 clippy 与全量 `cargo unit-test --jobs 8`。

## P1：Luau 官方语料仍有系统性缺口

当前默认编译选项扫描 49 个官方 conformance 源码，仅 16 个完成严格反编译和生成源码二次编译；约 21 个 residual unresolved、10 个 fixed-point 不收敛、2 个生成非法 label。该扫描没有逐个运行对拍，不能把 16 个记为语义通过。后续按最小 proto/源码片段拆根因，不把 33 个文件混成一个修复。

## P2：性能扫描结论

当前没有尚未解决且已有复杂度证据的热点。本轮看到 `decision/eliminate_materialize.rs` 对固定三个元素执行 `remove(0)`，但长度有严格常数上界，不是大文件退化点，不应为它单独重构。

后续性能工作仍应先提供可扩展输入、复杂度证明或 profile，再动实现；不要把普通 `BTreeSet::contains` 或小集合线性操作一概当热点。
