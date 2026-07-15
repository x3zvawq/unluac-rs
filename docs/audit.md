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
| P0 | 已复现 | Luau `events` 的 closure 可写 local、`math` 的 loop live-out 被拆成不同 binding，生成源码可编译但执行错误 | 先缩到最小 proto，再统一可写 local 身份 owner |
| P0 | 部分解决 | plain branch/loop island 已能局部降低并保留外层 for 与词法 cleanup；island 自身含 numeric/generic-for 协议或显式 cleanup 时仍会整 proto fallback | `refactor(hir): 完成mixed lowering并删除整proto fallback` |
| P1 | 语料缺口 | Luau conformance 当前 48/49 完成严格反编译与二次编译；仅剩 AST 超时 | 先完成 P2 热点定位 |
| P2 | 已复现 | `native_integer_spills.luau` 的 AST 阶段在 4327 条 low-IR 上单核运行超过 2 分 51 秒 | 定位 readability 热点并建立可扩展基准 |

## P0：Luau 可写 local 身份在 closure / loop 边界被拆分

官方 `events.luau` 与 `math.luau` 当前都能严格反编译并重新编译，但运行对拍失败：

```bash
cargo unluac -s lua/sources/luau/tests/conformance/events.luau -D luau -g strict -o /tmp/events.luau
lua/build/luau/luau lua/sources/luau/tests/conformance/events.luau
lua/build/luau/luau /tmp/events.luau

cargo unluac -s lua/sources/luau/tests/conformance/math.luau -D luau -g strict -o /tmp/math.luau
lua/build/luau/luau lua/sources/luau/tests/conformance/math.luau
lua/build/luau/luau /tmp/math.luau
```

- `events` 源码的 `foi` 被 `__newindex` closure 写入后应由连续 reset/assert 读取；生成源码
  中 closure 写 `r0_47`，reset/assert 却依次使用 `r0_56`、`r0_58`、`r0_60` 等新 local，
  第一次需要观察 closure 写入的断言失败。
- `math` 源码的 `Max` / `Min` 在 repeat 中更新并在退出后读取；生成源码循环更新
  `r0_201` / `r0_202`，退出断言却读取从未赋值的 `r0_203` / `r0_204`，报
  `attempt to compare number <= nil`。

两者都不是 local 作用域分组造成的语句重写，而是更早的可写 local / carried identity
已经分裂。下一步先锁定最小 proto，对比 HIR 的 `LocalId`、loop carried 与 child capture
映射，不能在 AST 或 Generate 把同名变量猜回去。

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

当前默认编译选项重新扫描 49 个官方 conformance 源码，48 个完成严格反编译和生成源码
二次编译；该扫描没有逐个运行对拍，不能把 48 个记为语义通过，已运行发现的两项语义
错误单列为上面的 P0。剩余未完成项只有：

- `native_integer_spills.luau` 在 AST 阶段触发已记录的性能问题，本轮在 2 分 51 秒后终止，尚未进入生成分类。

后续按最小 proto/源码片段拆根因，不把剩余文件混成一个修复；修复一个类别后重新扫描并更新准确数量。

## P2：`native_integer_spills.luau` 暴露 AST 超线性热点

当前官方输入只有 445 行，最大 proto 为 4327 条 low-IR；`--stop-after hir` 实测 2.17 秒，而完整严格反编译进入 AST 后单核持续 100%，运行 2 分 51 秒仍未结束，已人工终止。这说明热点位于 AST build/readability，而不是 parser/transformer/CFG/HIR，也不是无证据的容器选择猜测。

下一步先用 pass 级 changed/timing 把耗时缩到具体 readability owner，再从该输入裁出可扩展基准并证明复杂度；在证据完成前不凭普通 `BTreeSet::contains` 或小集合线性操作猜热点。
