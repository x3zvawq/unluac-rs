# Debug 使用说明

这份文档说明当前仓库里几种调试入口分别做什么，以及遇到问题时该怎么用它们定位。

## 四种入口

### 1. `cargo run`

这是当前的轻量 CLI 入口。

默认行为：

- 运行 [src/main.rs](/Users/x3zvawq/workspace/unluac-rs/src/main.rs)
- 转到 [src/cli.rs](/Users/x3zvawq/workspace/unluac-rs/src/cli.rs)
- 如果没有传 `--input`，会先把默认 Lua 源码编译成 chunk
- 然后调用库层 `decompile()` 并打印对应阶段的 dump

最常用的命令：

```bash
cargo run -- --dialect=lua5.1
cargo run -- --dialect=lua5.1 --detail=verbose
cargo run -- --dialect=lua5.1 --source tests/lua_cases/lua5.1/01_setfenv.lua
cargo run -- --dialect=lua5.1 --input /absolute/path/to/chunk.out
```

当前支持的一些实用参数：

- `--dialect=lua5.1`
- `--source=<lua 源码路径>`
- `--input=<已编译 chunk 路径>`
- `--encoding=utf8|gbk`
- `--decode-mode=strict|lossy`
- `--parse-mode=strict|permissive`
- `--dump=parse`
- 多次写 `--dump` 可以同时查看多个阶段
- `--stop-after=parse`
- `--detail=summary|normal|verbose`
- `--proto=<id>`

这里有一个当前约定：

- `--stop-after` 决定 pipeline 实际跑到哪一层
- `--dump` 只决定“已经跑到的层里哪些需要打印”

也就是说，如果你写了更后的 `--dump`，但 `--stop-after` 停得更早，那么未到达的层不会输出，也不会因此强行继续执行。

## 2. `cargo run --example debug`

这是开发期推荐的“实时看输出”入口。

它的目标不是替代 CLI，而是让维护者可以直接改代码里的常量，然后立刻重跑。

入口文件是 [examples/debug.rs](/Users/x3zvawq/workspace/unluac-rs/examples/debug.rs)。

最常改的常量在文件顶部：

- `DIALECT`
- `SOURCE`
- `STRING_ENCODING`
- `TARGET_STAGE`
- `DEBUG_DETAIL`

运行方式：

```bash
cargo run --example debug
```

这个 example 会优先使用仓库内的：

```text
lua/build/<dialect>/luac
```

也就是说，如果你把 `DIALECT` 改成 `lua5.1`，它会去找：

```text
lua/build/lua5.1/luac
```

然后动态把 `SOURCE` 指向的 Lua 源码编译成 chunk，再喂给库层 pipeline。

适合的场景：

- 反复调整同一个 case
- 临时切换编码为 `gbk`
- 持续观察 parser dump 形状
- 后续扩到 transformer/cfg 后持续看某一层输出

## 3. `cargo unit-test`

这是当前单元测试入口。

运行方式：

```bash
cargo unit-test
```

等价入口：

```bash
cargo lua test-unit
```

最常用的命令：

```bash
cargo unit-test --suite case-health
cargo unit-test --suite decompile-pipeline-health
cargo unit-test --dialect lua5.4
cargo unit-test --case-filter generic_for
cargo unit-test --case-filter control_flow --case-filter generic_for
cargo unit-test --jobs 4
UNLUAC_TEST_OUTPUT=verbose cargo unit-test
```

它的职责是对每一个被纳入支持范围的 `(case, dialect)` 做健康检查，重点确认：

- 原始源码在对应 dialect 下可解释、可编译、可执行
- 编译后的 chunk 可以成功反编译到最终源码
- 反编译结果可以重新编译并执行
- 反编译结果的 `(exit status, stdout, stderr)` 与原始源码一致

当前支持的参数：

- `--suite <all|case-health|decompile-pipeline-health>`
- `--dialect <all|lua5.1|lua5.2|lua5.3|lua5.4|lua5.5>`
- `--case-filter <substring>`，可重复传入，多次传入时按“任一匹配”处理
- `--output <simple|verbose>`
- `--timeout-seconds <n>`
- `--progress <auto|on|off>`
- `--color <auto|always|never>`
- `--jobs <n>`

当前支持的环境变量：

- `UNLUAC_TEST_OUTPUT=simple|verbose`
- `UNLUAC_TEST_PROGRESS=auto|on|off`
- `UNLUAC_TEST_COLOR=auto|always|never`

当前默认值：

- `suite=all`
- `dialect=all`
- `output=simple`
- `timeout-seconds=10`
- `progress=auto`
- `color=auto`
- `jobs=1`

当前实现里，单元测试内部有两个 suite：

- `case-health`
  只检查原始 case 在对应 dialect 下是否可解释、可编译、可执行，且源码直跑与编译后执行结果一致
- `decompile-pipeline-health`
  在 `case-health` 基线上继续检查反编译主流程能否生成可重新编译、可重新执行且语义等价的源码

这个入口适合的场景：

- 看当前支持范围内哪些 case 真正跑通了
- 只跑某一个健康检查 suite
- 用 `--case-filter` 聚焦某一组 case
- 用 `--jobs` 并行跑大量 case
- 用 `UNLUAC_TEST_OUTPUT=verbose` 查看失败细节

## 4. `cargo test --test regression`

这是当前回归测试入口。

运行方式：

```bash
cargo test --test regression
```

回归测试主要放在 [tests/regression](/Users/x3zvawq/workspace/unluac-rs/tests/regression) 下，例如 [tests/regression/lua51/pipeline.rs](/Users/x3zvawq/workspace/unluac-rs/tests/regression/lua51/pipeline.rs)。

它的职责是锁定已经修好的 bug、优化结果或语义决策，防止后续修改回退。这里允许断言中间层形状、特定 case 的结构恢复结果或某个明确错误语义。

所以：

- `cargo unit-test` 负责“全量健康检查”
- `cargo test --test regression` 负责“防回归”
- `cargo run --example debug` 负责“高频排错”
