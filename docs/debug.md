# Debug 使用说明

## 1. `cargo unluac`

CLI 调试入口，等价于 `cargo run -p unluac-cli -- ...`。

默认直接输出源码，传 `-d` 启用 debug dump，传 `-t` 看 timing。

常用命令：

```bash
cargo unluac -- -i /path/to/chunk.out -D lua5.1
cargo unluac -- -s tests/lua_cases/lua5.1/01_setfenv.lua -D lua5.1
cargo unluac -- -i /path/to/chunk.out -D lua5.1 -o /tmp/case.lua
cargo unluac -- -s tests/lua_cases/luajit/09_ull_table_rotation.lua -D luajit -d
cargo unluac -- -i /path/to/chunk.out -t
cargo run -p unluac-cli -- -i /path/to/chunk.out --dump=parse --detail=verbose
```

实用参数：

| 参数 | 说明 |
|------|------|
| `-i/--input` | 已编译 chunk 路径 |
| `-s/--source` | Lua 源码路径（自动编译） |
| `-o/--output` | 源码输出路径 |
| `-D/--dialect` | `lua5.1\|lua5.2\|lua5.3\|lua5.4\|lua5.5\|luajit\|luau` |
| `-d/--debug` | 启用 repo debug preset dump |
| `-e/--encoding` | `utf8\|gbk` |
| `-p/--parse-mode` | `strict\|permissive` |
| `-g/--generate-mode` | `strict\|best-effort\|permissive` |
| `--dump` | 指定 dump 阶段（可多次） |
| `--stop-after` | pipeline 停在哪一层 |
| `--detail` | `summary\|normal\|verbose` |
| `-t/--timing` | 输出 timing report |
| `--proto` | 按 proto id 过滤 |
| `-n/--naming-mode` | `debug-like\|simple\|heuristic` |
| `-c/--color` | `auto\|always\|never` |

约定：`--stop-after` 决定 pipeline 跑到哪层，`--dump` 只打印已到达层；`-o` 只支持纯源码输出，与 debug/timing 冲突时报错。

## 2. `cargo unit-test`

全量健康检查：原始源码 → 编译 → 反编译 → 重编译执行 → 语义等价校验。

```bash
cargo unit-test                                        # 全量
cargo unit-test --suite decompile-pipeline-health      # 只跑反编译 pipeline
cargo unit-test --dialect lua5.4 --case-filter generic_for
cargo unit-test --jobs 4
UNLUAC_TEST_OUTPUT=verbose cargo unit-test              # 查看失败细节
```

两个 suite：`case-health`（源码可编译执行）、`decompile-pipeline-health`（反编译语义等价）。

## 3. `cargo test --test regression`

防回归测试，锁定已修复 bug 和语义决策。测试在 `tests/regression/` 下按 dialect 组织。

```bash
cargo test --test regression                           # 全量
cargo test --test regression -- degenerate_guard       # 按名称过滤
```

## 分工

- `cargo unluac` — 高频排错
- `cargo unit-test` — 全量健康检查
- `cargo test --test regression` — 防回归
