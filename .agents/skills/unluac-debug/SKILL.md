---
name: unluac-debug
description: 在 unluac-rs 中复现并定位反编译语义错误、可读性缺口或 HIR/AST pass 证明问题，形成最小 Lua 回归与验证结果。适用于失败 case、错误生成源码、内联或生命周期问题；普通文档、构建配置和发布任务不触发。
---

# unluac 诊断与修复

目标是解释首次偏差的来源，并在用户要求修复时完成对应修改和验证。只读审计交付带证据的发现；
一个 case 的修复不自动扩大为整个 pass 或全仓审计。

## 入口与证据

- 项目约定见 [AGENTS.md](../../../AGENTS.md)。先复用现有源码 case、manifest variant 与调试能力；不要为同一输入形状另造 runner 或平行 pass。
- 从用户提供的失败条件确定源码或 chunk、方言、选项及观察到的差异。涉及命名或 debug 身份时才扩展到相应 debug 模式；不能把原本 stripped 的问题改为保留 debug 后宣称修复。
- 命令见 [调试手册](../../../docs/debug.md)，owner 导航见 [维护地图](../../../docs/design.md)。从最早可能出错的层选择 dump，用 proto 和 pass 过滤缩小输出，无需每次遍历所有阶段。

以下示例在仓库根目录运行；替换 case、方言和 pass 为当前复现条件：

```powershell
cargo unluac -s tests/case_calls/roots_01_non_tail_callable_root.lua -D lua5.4 --dump-pass temp-inline,inline-exprs --detail verbose
cargo case-test --case-filter non_tail_callable_root --output verbose
```

第一条用于观察生成过程，第二条才走编译、运行比较与断言的测试链。参数解析和默认值有疑问时
检查当前 CLI / runner；不能用一次成功生成或磁盘上的旧产物代替运行等价证据。

## 选择修复位置

- 比较输入、阶段产物和相关 pass 的前后结果，确认事实缺失、错误消费或候选改写中的首次偏差。在事实的自然 owner 修复，并复用它已有的分析与查询。
- 原 VM 的 home、root 生命周期和协议事实在 HIR 之前或 HIR 中证明；AST 证明候选 Lua 源码改写的合法性。具体约束按需读 [HIR](../../../docs/design/5.hir.md) 和 [AST readability](../../../docs/design/7.readability.md)，不从 AST 调用位置反推物理根存活。
- 删除、移动或合并表达式时，证明该候选涉及的求值次数与顺序、值快照、多返回宽度、metamethod 和生命周期。涉及弱引用或 GC 时用能观察差异的最小探针验证受影响方言；某一 VM 的结果不能外推为跨方言证明。
- 拒绝原因与接受证明按 [Pass guard 合同](../../../docs/design.md#pass-guard-合同) 记录。不能证明等价时保留原形状并指出缺失事实；有具体不等价反例时修复或收紧接受路径，不用更短源码作为放宽条件的理由。

## 验证与完成

- 修复使用最小可编译 Lua 源码回归，在 `packages/unluac-test-support/src/case_manifest.rs` 所路由的相应模块注册；优先扩展同主题 case 或 variant。涉及展示合同时补 `unluac:` 断言，运行比较仍需保留。
- 按 [测试体系](../../../docs/design/11.test.md#按改动选择验证) 完成定向验证与交付检查。记录实际执行范围、差异及未验证条件；无法复现时如实说明证据缺口，不把推测写成根因。
- 仅在用户要求 pass 审计时，沿候选形成、helper、拒绝出口和提交点检查完整调用链；检索标记只是导航。完成所请求的范围后交付，不继续追逐无关 guard。
