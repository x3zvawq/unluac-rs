---
name: unluac-debug
description: 在 unluac-rs 中复现并定位反编译语义错误、控制流退化或表达式可读性问题，形成最小 Lua 回归与验证结果。适用于失败 case、错误生成源码、多余中转变量或非法语法回退；普通文档、构建配置和发布任务不触发。
---

# unluac-rs 诊断与修复

定位问题首次出现的流水线阶段，在自然 owner 修复通用算法，并以最小 Lua 回归验证。

## 1. 复现与定位

- 先查阅 [AGENTS.md](../../../AGENTS.md)、[维护地图](../../../docs/design.md) 与 [调试手册](../../../docs/debug.md)。
- 明确输入源码/chunk、目标方言、是否 strip debug 及实际差异（编译失败、运行输出不一致、非法 `goto`/状态机退化或多余中转变量）。不要把原本 stripped 的问题改成保留 debug 后宣称修复。
- 按五阶段顺序缩小首次偏差：`parser` → `transformer` → `analysis` → `ast` → `generate`，大文件先用 `--list-protos` + `--proto <id>` 聚焦目标函数。

```bash
cargo unluac -s tests/case_control_flow/example.lua -D lua5.1 --dump analysis --proto 0
cargo case-test --case-filter example --output verbose
```

## 2. 按层根因修复

- **Parser / Transformer 异常**：核对原始 opcode、常量、多值包与 debug 坐标，在协议层修复。
- **CFG / SSA / 数据流异常**：读 [Analysis 设计](../../../docs/design/3.analysis.md)，检查跳板折叠、支配/循环、Close-Epoch 切分、Def-Use 或副作用屏障。
- **控制流错误、Lua 5.1 退化或多余 `goto`**：读 [Structure 设计](../../../docs/design/4.structure.md)，补强通用条件折叠、迭代区域规约、安全尾复制或单遍围栏，不堆砌只命中单个样例的特判。
- **多余中转变量或语义错乱**：读 [AST Lift 设计](../../../docs/design/5.ast-lift.md)，核对表达式顺序消费栈、多值截断 `(expr)`、`a and b or c` falsy 边界、NaN 比较取反与 upvalue 捕获，绝不为死栈槽 GC 残值或重编译指令数锁死正常内联。
- **命名或排版错误**：读 [Naming 与 Generate 设计](../../../docs/design/6.naming-and-generate.md)。

## 3. 回归与验证

- 为已确认问题补充最小可编译 Lua 回归，验证编译、反编译、再编译与实际运行输出一致；涉及结构退化时附带简洁的 `-- unluac:` 断言。
- 按 [测试体系](../../../docs/design/7.debugging-and-test.md) 运行定向回归与 `cargo clippy --workspace --all-targets --all-features --locked -- -D warnings`，如实报告已验证范围与未覆盖部分。
