# 调试手册

> 本文只回答“怎么调”。调试设施的实现位置见 `docs/design/10.debugging.md`，测试体系见 `docs/design/11.test.md`。

## 适用范围

- 用 `cargo unluac -- ...` 复现问题、观察中间层结果、缩小根因范围。
- 不在这里解释调试代码如何实现，也不记录测试命令与测试规范。

## 常用入口

```bash
# 直接反编译
cargo unluac -- -i /path/to/chunk.out -D lua5.1

# 从源码编译后再反编译
cargo unluac -- -s tests/lua_cases/lua5.1/01_setfenv.lua -D lua5.1

# 查看某一层的 dump
cargo unluac -- -i /path/to/chunk.out -D lua5.4 --dump hir --detail verbose

# 停在某一层并聚焦某个 proto
cargo unluac -- -i /path/to/chunk.out -D lua5.4 --stop-after readability --proto 3 --proto-depth 1

# 查看某个 pass 的前后变化
cargo unluac -- -i /path/to/chunk.out -D lua5.4 --dump-pass temp-inline --proto 2
```

## 调试参数速查

| 参数 | 作用 |
| --- | --- |
| `-i/--input` | 输入已编译 chunk |
| `-s/--source` | 输入 Lua 源码并自动编译 |
| `-D/--dialect` | 指定方言 |
| `-d/--debug` | 使用仓库默认 debug dump 预设 |
| `--dump` | 指定要打印的阶段，可重复传入 |
| `--stop-after` | 在指定阶段后停止 pipeline |
| `--detail` | 控制 dump 详略 |
| `--proto` | 只看某个 proto |
| `--proto-depth` | 控制焦点 proto 向下展开的层数 |
| `--dump-pass` | 看 pass 的 before/after 快照 |
| `--list-protos` | 先列出 proto，便于决定 `--proto` |
| `-t/--timing` | 输出阶段耗时 |

## 使用约定

- `--stop-after` 决定 pipeline 跑到哪一层，`--dump` 只能打印已到达的层。
- `--proto` / `--proto-depth` 适合在 parse、HIR、AST、readability 之间来回比对同一子函数。
- `--dump-pass` 只在 pass 实际改动内容时输出快照；未变化时不会刷屏。
- `-o/--output` 面向最终源码输出，不适合与调试输出混用。

## 推荐排错流程

1. 先用 `--list-protos` 确认目标函数，避免在大 chunk 里盲看全量输出。
2. 从 `--dump parse` 或 `--stop-after parse` 开始，逐层向后推进，找到第一层“不对”的结果。
3. 若问题只出现在某个子函数，立刻加 `--proto N --proto-depth 1` 缩小范围。
4. 若怀疑某个 pass 改坏了结果，用 `--dump-pass pass-name` 看它的 before/after。
5. 锁定层次后，再去看对应设计文档，而不是在后层堆特判。

## 跳转

- 调试设施 code-map：`docs/design/10.debugging.md`
- 测试命令与测试规范：`docs/design/11.test.md`
- 各层设计入口：`docs/design.md`
