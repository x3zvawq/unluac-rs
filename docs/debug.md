# Debug 使用说明

这份文档说明当前仓库里几种调试入口分别做什么，以及遇到问题时该怎么用它们定位。

## 三种入口

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

## 3. `cargo test`

这是回归测试入口，不是开发期实时查看 dump 的入口。

当前测试目录约定：

- unit 测试放在 [tests/unit/lua51/parser.rs](/Users/x3zvawq/workspace/unluac-rs/tests/unit/lua51/parser.rs) 和 [tests/unit/lua51/transformer.rs](/Users/x3zvawq/workspace/unluac-rs/tests/unit/lua51/transformer.rs) 这类路径下
- regression 测试放在 [tests/regression/lua51/pipeline.rs](/Users/x3zvawq/workspace/unluac-rs/tests/regression/lua51/pipeline.rs) 这类路径下

像 [tests/regression/lua51/pipeline.rs](/Users/x3zvawq/workspace/unluac-rs/tests/regression/lua51/pipeline.rs) 这样的测试，职责是锁定：

- 主 pipeline 的最小契约
- 当前 parser / transformer dump 的基本形状
- 未实现阶段是否明确报错

这里故意保留固定 chunk fixture，而不是动态调用 `luac`，原因是：

- 测试应该尽量稳定、自包含
- 不希望因为外部工具链、二进制缺失或本地构建状态导致测试漂移
- 开发期动态调试已经由 `examples/debug.rs` 负责

所以：

- `cargo test` 负责“防回归”
- `cargo run --example debug` 负责“高频排错”
