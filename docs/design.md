# unluac-rs 维护地图

本目录定义 unluac-rs 的五阶段反编译流水线分层、模块职责与层间数据契约。

## Pipeline 总览

```text
bytes ──→ 1. Parser ──→ 2. Transformer ──→ 3. Analysis ──→ 4. Ast ──→ 5. Generate
            (RawChunk)    (LoweredChunk)     (Cfg + SSA)    (Ast + Names)  (Lua Source)
```

| # | 阶段 | 核心产出 | 主要职责 | 设计文档 |
| --- | --- | --- | --- | --- |
| 0 | 总览 | 语义合同 / 失败策略 | 明确“保什么、不保什么”、方言能力与降级策略 | [0.overview.md](./design/0.overview.md) |
| 1 | Parser | `RawChunk` | 按方言保真解码字节码、常量池、proto 树与 debug 段 | [1.parser.md](./design/1.parser.md) |
| 2 | Transformer | `LoweredChunk` | 将 7 种方言 opcode 降为统一 `LowInstr` 与标准协议 | [2.transformer.md](./design/2.transformer.md) |
| 3 | Analysis | `AnalysisChunk` | 构建并规范化 CFG、图事实、标准 SSA、活性、副作用与捕获分析 | [3.analysis.md](./design/3.analysis.md) |
| 4 | Ast | `AstModule` + `NameMap` | 迭代控制流结构化 → 表达式/声明提升 → 轻量语法糖 → 命名 | [4.structure.md](./design/4.structure.md) / [5.ast-lift.md](./design/5.ast-lift.md) |
| 5 | Generate | `GeneratedChunk` | 将稳定 AST 与 `NameMap` 排版渲染为目标方言源码 | [6.naming-and-generate.md](./design/6.naming-and-generate.md) |
| 6 | 调试与测试 | Dump / 回归矩阵 | 5 阶段调试视图、CLI 用法与分层测试协议 | [7.debugging-and-test.md](./design/7.debugging-and-test.md) |

补充专项文档：
- 命令行排错速查：[debug.md](./debug.md)
- 表格对齐布局说明：[table-alignment.md](./table-alignment.md)

## 设计原则

1. **五层边界清晰，不叠床架屋**：流水线固定为 `Parser -> Transformer -> Analysis -> Ast -> Generate`。`Analysis` 专注图与数据流，`Ast` 内部用轻量的 `RegionTree` 衔接控制流结构化与表达式提升，`Generate` 纯粹负责排版输出。
2. **数据只向下游流动**：前层计算的协议、SSA、支配、捕获等事实通过只读结构提供给后层；后层不回扫字节码猜测前层语义。
3. **语义精准但不过度偏执**：死守语言级可观察语义（求值顺序、元方法、多值宽度、捕获、`<close>`、NaN 比较），剥离 VM 物理栈槽、弱表 GC 残值与编译器 `-O2` 内联指令数等非源码契约。
4. **先稳健、再美观**：任何合法字节码都必须优先产出一个**目标方言 100% 合法可编译**的源码，绝不因局部可读性优化失败而导致整函数反编译崩溃，也绝不向 Lua 5.1 输出非法 `goto`。
5. **面向真实大型脚本**：数据结构默认使用紧凑数组索引（`Vec` + typed ID）与线性/近线性算法，针对数千指令函数与大型配置表保持低内存、低耗时与小 WASM 体积。

## 阅读与排错路径

- 首次上手架构：读 [0.overview.md](./design/0.overview.md) → [3.analysis.md](./design/3.analysis.md) → [4.structure.md](./design/4.structure.md) → [5.ast-lift.md](./design/5.ast-lift.md)。
- 排查问题时，按阶段依次用 `--dump parser / transformer / analysis / ast` 定位首次出现异常的层，在对应 owner 修复，不在后层打补丁。
