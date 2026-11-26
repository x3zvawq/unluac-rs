# 调试与 CLI 排错手册

> 本文介绍如何用 `cargo unluac`（或编译好的 `unluac-cli`）快速定位反编译问题、按函数拆解大脚本以及查看各阶段中间产物。完整架构与测试协议见 [7.debugging-and-test.md](./design/7.debugging-and-test.md)。

## 常用命令

```bash
# 直接反编译字节码（位置参数或 -i 均可）
cargo unluac /path/to/chunk.out
cargo unluac -i /path/to/chunk.out -D lua5.1

# 批量递归反编译整个目录，输出 JSON 汇总
cargo unluac ./scripts_bin -o ./scripts_src -j 8 --format json

# 使用场景预设（readable / exact / ai）
cargo unluac /path/to/chunk.out --preset readable
cargo unluac /path/to/chunk.out --preset exact

# 大脚本定位：先看所有 proto 行号、指令数与字符串常量摘要，再单独导出指定函数源码
cargo unluac /path/to/big.out --list-protos --format json
cargo unluac /path/to/big.out --proto 17

# 从 Lua 源码自动编译并反编译（默认 strip debug；加 --strip false 保留 debug）
cargo unluac -s tests/case_control_flow/if_01_basic.lua -D lua5.1
cargo unluac -s tests/case_control_flow/if_01_basic.lua -D lua5.1 --strip false

# 解析并校验 debug 段，但不让 debug 信息参与恢复与命名
cargo unluac -s tests/case_control_flow/if_01_basic.lua -D lua5.1 --strip false --ignore-debug

# 查看指定阶段中间产物（parser / transformer / analysis / ast / generate）
cargo unluac /path/to/chunk.out --dump analysis --detail verbose

# 停在指定阶段并聚焦某个 proto
cargo unluac /path/to/chunk.out --stop-after ast --proto 3 --proto-depth 1

# 输出各阶段耗时
cargo unluac /path/to/chunk.out --timing

# 严格模式：遇不支持结构或单函数失败时直接报错退出（exit 1）
cargo unluac /path/to/chunk.out --generate-mode strict
```

## 常用参数速查

| 参数 | 作用 |
| --- | --- |
| `<INPUT>` / `-i/--input` | 输入字节码文件、`-`（标准输入）或目录（需配合 `-o`） |
| `-o/--output` | 输出源码文件路径（目录模式下为输出根目录） |
| `-j/--jobs` | 目录批量模式并发线程数（默认 CPU 核数） |
| `-s/--source` | 输入 Lua 源码并调用本地工具链编译后反编译 |
| `-D/--dialect` | 指定方言（`auto`/`lua5.1`..`lua5.5`/`luajit`/`luau`） |
| `--preset` | 场景预设：`readable` / `exact` / `ai`（显式参数优先级更高） |
| `--format` | 输出格式：`text`（默认）或 `json`（支持单文件、`--list-protos`、批量汇总） |
| `--comment` | 注释详略：`minimal`（默认）/ `full` / `none`（兼容 `true`/`false`） |
| `-n/--naming-mode` | 命名策略：`heuristic`（默认）/ `simple` / `debug-like` |
| `--strip` | 源码编译时是否剥离 debug 信息（默认 `true`） |
| `--ignore-debug` | 校验 debug 段但不让它参与变量恢复与命名（默认 `false`） |
| `--list-protos` | 列出 chunk 中所有 proto 概览（`--format json` 附带字符串常量摘要） |
| `--proto` | 仅导出或聚焦指定编号的 proto（不加 `--dump`/`--debug` 时直接输出干净源码） |
| `--proto-depth` | 焦点 proto 向下展开的子函数层数 |
| `-d/--debug` | 启用调试 dump 预设 |
| `--dump` | 打印指定阶段（`parser`/`transformer`/`analysis`/`ast`/`generate`），可重复 |
| `--stop-after` | 执行完指定阶段后立即停止 |
| `--detail` | 控制 dump 详略（`summary` / `normal` / `verbose`） |
| `-t/--timing` | 输出各阶段耗时统计 |
| `-g/--generate-mode` | `permissive`（默认，单函数失败降级为诊断注释，退出码 `2`）；`strict`（遇错即停，退出码 `1`） |

## 推荐排错步骤

1. 先运行 `--list-protos`（或 `--list-protos --format json`）锁定出问题的函数编号，再通过 `--proto N --proto-depth 1` 缩小范围。
2. 按流水线顺序依次查看 `--dump parser` → `--dump transformer` → `--dump analysis` → `--dump ast`，找到第一层出现异常的阶段。
3. 确认根因属于哪一层后，查阅 [维护地图](./design.md) 进入对应设计文档和模块修复，不在下游打特判补丁。
