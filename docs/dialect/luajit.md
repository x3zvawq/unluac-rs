# LuaJIT Dialect 接入设计与实现状态

## 背景

当前仓库已经支持两条 bytecode family:

- PUC-Lua 5.1-5.5
- Luau

这两条线已经说明一个事实:

- “源码语义接近” 不代表 “bytecode 协议可以复用”
- parser / raw model / transformer 的 family 边界，必须按真实 bytecode 格式划分

LuaJIT 就属于第三条 family。

虽然 LuaJIT 的源码语义整体更接近 Lua 5.1，但它的 bytecode dump:

- header 不是 `\x1bLua`
- proto 序列化协议不是 PUC-Lua 的 `lundump`
- 常量池里包含 `I64/U64/COMPLEX/TAB/CHILD` 这类 LuaJIT 专属项
- dump header 还带有 `FFI/FR2/STRIP` 等兼容 flag

因此，LuaJIT 接入不能走“把它伪装成 Lua 5.1，再在 parser/transformer 里补特判”的路线。
这会把公共模型重新拉回错误抽象，后面很容易重复 Luau 接入前的那些结构性问题。

## 目标

第一阶段 LuaJIT 接入的目标是:

- 能解析 LuaJIT bytecode dump
- 能走完现有 decompile pipeline
- 能输出 LuaJIT 可以重新执行的源码
- 生成结果优先面向 `LuaJIT 2.1` 源码语法

换句话说，第一阶段目标仍然是:

- 可执行
- 可复编译
- 结构正确

而不是:

- 高保真恢复原始源码写法
- 一次性兼容 LuaJIT 2.0 和 2.1 的所有 dump 变体

## 非目标

第一阶段明确不做以下事情:

- 不承诺同时完整支持 LuaJIT 2.0 和 2.1
- 不恢复原始 `ffi.cdef` 文本排版
- 不保证恢复原始 cdata 字面量写法
- 不为了兼容 LuaJIT 而污染 PUC-Lua 5.1 parser family
- 不把 `luajit20` / `luajit21` 暴露为新的公开 dialect 名字

## 核心约束

### 1. LuaJIT 必须被视为独立 dialect family

在 parser / raw model 层，LuaJIT 与 PUC-Lua 5.1 不共享协议。

这意味着:

- `Dialect` 需要新增 `LuaJit`
- `ChunkLayout` 需要新增 `LuaJit` payload
- constant pool / opcode / debug payload 都需要 LuaJIT 专属 extra

源码层和 Lua 5.1 接近，不等于 bytecode 层可以复用 `lua51` parser。

### 2. 对外只保留单一 `luajit` 入口

当前决策是:

- 对外公开接口只保留一个 `luajit` dialect
- 第一阶段只明确支持 `LuaJIT 2.1`
- 内部按 dump version 与 header flags 分支

这样做的原因是:

- 用户侧接口保持简洁
- 2.0/2.1 的差异可以在 family 内部建模
- 避免 CLI、tests、文档和实现矩阵过早膨胀

### 3. 第一阶段优先兼容 LuaJIT 2.1

这是当前的推荐路线。

原因:

- LuaJIT 2.1 dump header revision 已经不同于 2.0
- 2.1 多了 `BCDUMP_F_FR2`
- 仓库现有 `tests/lua_cases/luajit` 样例也更偏向 2.1 源码特性

因此第一阶段应明确写成:

- 支持 `BCDUMP_VERSION = 2`
- 正确解析 `BCDUMP_F_STRIP` / `BCDUMP_F_FFI` / `BCDUMP_F_FR2`
- 生成目标以 `LuaJIT 2.1` 源码能力为准

### 4. 避免 downstream fallback

和 Luau 一样，LuaJIT 接入优先做结构性建模:

- raw model 对齐真实 dump 结构
- transformer 对齐真实 VM 语义
- AST / generate 对齐真实目标语法能力

不要在 AST / generate 后层为 parser / transformer 的缺口做静默兜底。

## 版本策略

### 公开策略

公开接口继续只有一个:

- `luajit`

不新增:

- `luajit20`
- `luajit21`

### 内部策略

内部需要显式记录:

- dump version
- dump flags

推荐的内部布局类似:

- `LuaJitChunkLayout { dump_version, flags }`

并从 flags 再派生 capability:

- `strip_debug`
- `uses_ffi`
- `fr2`

### 为什么不公开拆版本

LuaJIT 2.0 和 2.1 确实不是同一套 dump header revision:

- 2.0: `BCDUMP_VERSION = 1`
- 2.1: `BCDUMP_VERSION = 2`

同时 2.1 还引入了:

- `BCDUMP_F_FR2`

但这些差异更适合在同一个 `LuaJIT` family 内部处理，而不是变成两个公开 dialect。

原因:

- 用户不会因为 CLI 参数多一个 `luajit21` 而得到更多价值
- 真正需要维护的是 parser/transformer 内部 capability，而不是公开名字
- 先公开拆版本，后面很难收回

### 第一阶段承诺边界

第一阶段建议明确承诺:

- 支持 LuaJIT 2.1 dump format
- 即 `BCDUMP_VERSION = 2`

第一阶段不承诺:

- LuaJIT 2.0 dump format
- 任何未验证的旧 dump 变体

LuaJIT 2.0 可以作为后续 Phase 单独补齐，但不应拖住 2.1 主线。

## 现状评估

### parser

当前 parser family 只有:

- `PucLua`
- `Luau`

还没有:

- `LuaJit`

因此 LuaJIT parser 的工作不是“接到现有 lua51 parser 上”，而是:

- 扩展公共 raw model
- 新增 `src/parser/dialect/luajit`
- 按 LuaJIT dump 协议单独解析

#### LuaJIT parser 最低需要覆盖的内容

- `ESC 'L' 'J'` header
- dump version
- dump flags
- optional chunk name
- proto table
- instruction stream
- upvalue metadata
- KGC constants
- number constants
- debug info

#### LuaJIT 常量池与 PUC-Lua 的关键差异

LuaJIT dump 需要能建模至少这些 KGC 类型:

- child proto
- constant table
- int64
- uint64
- complex
- string

这一步如果建模不对，后续 FFI/cdata/imaginary 相关样例都不可能稳定恢复。

### transformer

LuaJIT 的 VM 语义比 Luau 更接近 Lua 5.1，但仍然不是同一套 bytecode opcode。

因此 transformer 层建议:

- 新增 `src/transformer/dialect/luajit`
- 不复用 `src/transformer/dialect/lua51/parser`
- 但可以复用 Lua 5.1 语义上已经存在的很多 low-IR 抽象

LuaJIT transformer 很可能比 Luau 更适合复用这些现有抽象:

- 闭包
- upvalue
- 数值 for / 泛型 for
- method call
- table access
- 普通 branch / loop

但 parser 到 low-IR 的 lowering 仍然必须独立实现。

### AST / generate

LuaJIT 的源码目标与当前 Lua 5.x / Luau 都不完全一样。

第一阶段生成目标建议直接瞄准:

- `LuaJIT 2.1`

原因:

- 2.1 支持范围更接近仓库已有 LuaJIT case
- 后续如果再补 2.0，可以在内部 target capability 上细分

第一阶段至少需要考虑这些语法能力:

- `goto` / label
- Lua 5.1 风格局部函数 / upvalue / 环境语义
- LuaJIT 特有 numeric / cdata 常量表示
- `ffi` / `jit` / `bit` 等库调用按普通全局/require 调用处理

这里要特别注意:

- LuaJIT 目标不是 Luau，也不是 Lua 5.4/5.5
- 不应生成 `_ENV`、`<close>`、`local<const>` 这类不属于 LuaJIT 目标的语法

### tests / toolchain

当前仓库已经完成:

- `DecompileDialect::Luajit`
- `LuaCaseDialect::Luajit`
- LuaJIT runtime/compiler 抽象
- `tests/lua_cases/luajit/*` 接入 `case-health`
- `tests/lua_cases/luajit/*` 与 `tests/lua_cases/common/*` 接入 `decompile-pipeline-health`

当前测试策略仍然保持为:

- 源码 -> 本地 LuaJIT 编译 -> 反编译 -> 本地 LuaJIT 重新执行
- 不把预生成 dump fixture 当成稳定契约

## 设计原则

### 原则一: 先把 LuaJIT 当成 family，再讨论 2.0/2.1

优先顺序应该是:

1. 先建立 `LuaJit` family
2. 再确定 2.1 parser/transformer 主线
3. 最后补 2.0 兼容

而不是反过来。

### 原则二: 先支持 2.1，再补 2.0

第一阶段就同时兼容 2.0 与 2.1，会让 parser / tests / toolchain / generate 的
复杂度明显上涨，而且收益不高。

更合理的路线是:

- Phase 1: 只做 2.1
- Phase 2: 在既有 `luajit` family 上补 2.0

### 原则三: 测试工具链先对齐 runtime，而不是先追求 cross-target dump

LuaJIT 2.1 的 dump flags 里包含 `FR2`。这意味着:

- bytecode dump 与 runtime 运行模式存在兼容性约束

因此第一阶段 tests 的核心要求应是:

- “编译 bytecode 的 toolchain”和“执行 bytecode 的 runtime”必须来自同一套 LuaJIT

而不是一开始就追求:

- 多 host mode
- 多 target mode
- 预生成二进制 fixture

第一阶段测试更适合继续走:

- 源码 -> 本地 LuaJIT 编译 -> 反编译 -> 本地 LuaJIT 重新执行

## 分层设计

### 一、decompile 入口

需要新增:

- `DecompileDialect::Luajit`

CLI 第一阶段只支持显式选择:

- `--dialect=luajit`

虽然 LuaJIT header 有明确魔数，后续可以评估自动识别；
但第一阶段继续保持显式 dialect，更符合当前仓库入口设计。

### 二、parser 层

#### 2.1 公共 raw model

`src/parser/raw.rs` 需要从当前:

- `PucLua`
- `Luau`

扩展到:

- `PucLua`
- `Luau`
- `LuaJit`

需要新增的 family-aware payload 至少包括:

- `LuaJitChunkLayout`
- `LuaJitHeaderExtra`
- `LuaJitConstPoolExtra`
- `LuaJitInstrExtra`
- `LuaJitProtoExtra`
- `LuaJitDebugExtra`
- `LuaJitUpvalueExtra`

#### 2.2 新增 LuaJIT parser 目录

新增:

- `src/parser/dialect/luajit/mod.rs`
- `src/parser/dialect/luajit/parser.rs`
- `src/parser/dialect/luajit/raw.rs`
- `src/parser/dialect/luajit/debug.rs`

#### 2.3 第一阶段 parser 支持范围

第一阶段建议明确写成:

- 只接受 `BCDUMP_VERSION = 2`

遇到别的 dump version:

- 直接报 unsupported

不要先写成“也许能解析”。

### 三、transformer 层

新增:

- `src/transformer/dialect/luajit/*`

第一阶段 transformer 重点:

- 基本算术 / 比较 / branch
- 数值 for / 泛型 for
- closure / upvalue
- method call
- table access
- goto / label 对应的控制流形状
- LuaJIT 常量类型向 low-IR 的映射

这里有一个重要决策:

- LuaJIT 虽然接近 Lua 5.1，但 transformer 不应依赖“假装它是 lua51”
- 更合理的是“独立 parser/transformer，尽量复用 low-IR 语义抽象”

### 四、AST / generate 层

第一阶段建议新增:

- `AstDialectVersion::LuaJit`

它的 capability 应以 LuaJIT 2.1 为准。

初步建议:

- `goto_label = true`
- `continue_stmt = false`
- `local_close = false`
- `local_const = false`
- `global_decl = false`
- `global_const = false`

第一阶段目标不是恢复“原始 LuaJIT 写法”，而是:

- 生成 LuaJIT 能执行的源码

因此像这些内容可以允许 canonical 化:

- cdata 常量写法
- hexfloat 常量写法
- FFI 相关调用周围的局部变量命名

但前提是:

- 语义不能丢
- 不要为了弥补前层缺口，强行在 emitter 里注入静默 helper/fallback

### 五、tests / toolchain

第一阶段 tests 需要新增:

- `LuaCaseDialect::Luajit`
- `LUAJIT_ONLY`
- LuaJIT runtime/compiler 抽象

运行协议建议:

- 运行源码: `luajit source.lua`
- 编译源码: `luajit -b source.lua output`
- 运行 dump: `luajit output`

但要注意:

- bytecode dump 必须和本地 runtime 模式匹配
- 第一阶段不建议把预生成 dump fixture 提交进仓库当稳定契约

因此第一阶段测试策略建议:

- 先把 `tests/lua_cases/luajit` 纳入 `case-health`
- 等 parser / transformer / generate 基本打通后，再纳入 `decompile-pipeline-health`

## 版本差异与后续扩展

### 2.1 与 2.0 的关键差异

当前已确认的关键点:

- 2.0: `BCDUMP_VERSION = 1`
- 2.1: `BCDUMP_VERSION = 2`
- 2.1 新增 `BCDUMP_F_FR2`

这说明:

- 未来要补 2.0，一定是 parser 内部的正式版本分支
- 但不意味着现在就要公开两个 dialect

### 后续 2.0 支持策略

当第一阶段 2.1 稳定后，第二阶段可以:

- 在 `luajit` parser 内补 `dump_version = 1`
- 为 transformer / generate 增加必要 capability 差异
- 再补 2.0 专属测试样例与工具链验证

## 当前决策

目前明确采用以下路线:

- LuaJIT 作为独立 dialect family 接入
- 对外只保留单一 `luajit` dialect
- 第一阶段只支持 LuaJIT 2.1 dump format
- parser / transformer 内部按 dump version 与 flags 分支
- 不把 `luajit20` / `luajit21` 暴露成公开 dialect
- 生成目标先对齐 LuaJIT 2.1 源码能力

## 建议的推进顺序

1. 先新增 `docs/dialect/luajit.md`
2. 再新增 `DecompileDialect::Luajit`
3. 再打通 tests / toolchain 的 LuaJIT runtime/compiler 抽象
4. 再扩展 parser raw model，新增 `LuaJit` family
5. 再实现 LuaJIT 2.1 parser
6. 再实现 LuaJIT 2.1 transformer
7. 最后补 AST / generate 的 LuaJIT target
8. 等 2.1 稳定后，再单独评估 LuaJIT 2.0

## 当前状态与 TODO

### 当前状态

截至目前，LuaJIT 主线已经打通，现状是:

- 已新增 `DecompileDialect::Luajit`
- 已新增 LuaJIT parser family: `src/parser/dialect/luajit/*`
- 已新增 LuaJIT transformer lowering: `src/transformer/dialect/luajit/*`
- 公共 raw model 已扩展 `LuaJit` family 与 `LuaJitChunkLayout`
- AST / generate 已新增 `AstDialectVersion::LuaJit`
- tests/toolchain 已支持 LuaJIT runtime/compiler 协议
- `tests/lua_cases/common` 与 `tests/lua_cases/luajit` 已能在 `luajit` 下走完整个 decompile pipeline
- 当前 `cargo unit-test --jobs 8` 已通过，矩阵为 `982/982`

当前这条线的实际承诺边界仍然是:

- 公开接口只有一个 `luajit`
- 第一阶段只明确支持 `LuaJIT 2.1`
- parser 只接受 `BCDUMP_VERSION = 2`
- 目标是“生成 LuaJIT 可执行、可复编译源码”，不是恢复原始 FFI/cdata 写法

### TODO

后续建议的具体任务:

- 继续补 LuaJIT 2.1 的 regression 测试，优先沉淀这次接入过程中修掉的 tricky/control-flow 场景
- 明确文档化当前已支持的 opcode / constant / debug info 边界，避免“看起来支持但其实未验证”
- 第二阶段评估并设计 `LuaJIT 2.0` 支持方案，在内部按 dump version 分支，而不是公开新 dialect
- 如果后续需要支持更多 dump 变体，再把 `dump flags -> capability` 的映射进一步收紧并写入测试矩阵
