# Luau Dialect 接入计划

## 背景

当前仓库的 parser / transformer / AST / generate 主线，都是围绕 PUC-Lua
5.1-5.5 的 chunk 结构和语义约束搭起来的。`src/parser/dialect` 与
`src/transformer/dialect` 里现有的几个版本目录，本质上都依赖
`puc_lua` 这一层共享协议。

Luau 不属于这条演进线。

- 它的 chunk header 不是 PUC-Lua 的 `\x1bLua` 结构。
- 它的 constant table 也不是“只有字面量常量”的模型。
- 它的 opcode、closure capture、generic for、import/global access
  语义都和 PUC-Lua 明显不同。

因此，Luau 接入不能走“把 Luau 伪装成 Lua 5.6，再在后面补特判”的路线。
这样做会让 parser、transformer、generator 和 tests 都长期背着错误抽象，
并持续制造静默错误。

## 目标

这一轮 Luau 接入的目标是:

- 能解析 Luau bytecode。
- 能走完现有 decompile pipeline。
- 能输出 Luau 可以重新编译、重新执行的源码。
- 输出源码允许是“无类型的 Luau-compatible Lua”。

换句话说，我们的目标是“可执行、可复编译”，而不是“恢复原始 typed Luau 源码”。

## 非目标

第一阶段明确不做以下事情:

- 不恢复类型标注。
- 不强行恢复 if-expression、字符串插值、复合赋值等 Luau 语法糖。
- 不做启发式的 Luau/Puc-Lua chunk 自动识别。
- 不为了兼容 Luau 而在公共层伪造 PUC-Lua header 或 fake constant pool。

这些信息要么在编译后已经丢失，要么属于后续 readability / sugar pass 的工作，
不应该混进基础 parser / transformer 的结构设计里。

## 核心约束

### 1. Luau 必须被视为独立 dialect family

当前 `src/parser/raw.rs` 里的 `Dialect` / `DialectVersion` / `ChunkHeader`
都是 PUC-Lua 视角。Luau 接入时必须把公共模型改造成“family + family-specific
payload”的结构，不能继续假设所有 chunk 都有同一套 header 字段。

### 2. 第一阶段接受“输出更朴素的源码”

Luau 可以执行大量无类型 Lua 代码，因此只要生成结果可以被 Luau 接受，
就已经达成第一阶段目标。生成代码不必刻意追求 Luau-native 外观。

### 3. 外部工具只存在于测试和 xtask

仓库需要考虑 wasm 分发，所以 `luau` / `luau-compile` 这类外部命令
只能留在 `tests/` 和 `xtask/` 辅助体系中，库本身仍然只处理字节流和 IR。

### 4. 避免 downstream fallback

当某个 Luau case 失败时，优先检查 parser raw model、lowering 契约、
target dialect capability 是否建模错误；不要在 AST / generate 后层
为前层缺失的信息做兜底修补。

## 现状评估

### parser

当前 parser 公共入口默认假设输入是 PUC-Lua chunk，Luau 不能复用这套入口。

现有问题主要有:

- `RawChunk::header` 绑定了 PUC-Lua 风格的 header 字段。
- `RawConstPoolCommon` 只支持字面量常量数组。
- `RawInstrOpcode` / `RawInstrOperands` 是按 Lua 5.x 各版本枚举展开的。
- `src/parser/dialect/puc_lua` 是当前几个 Lua 版本的共享基础，Luau 基本没有
  可以直接依赖的解析协议。

因此 parser 侧基本需要新增一套 Luau raw protocol，并顺手把公共 raw model
做一次去 PUC-Lua 中心化重构。

### transformer

当前 transformer 的 low-IR 里，已经有一些 Luau 可以复用的抽象:

- `AccessBase::Env`
- method call 语义
- closure lowering 结构
- `Continue`
- generic for / numeric for 的统一表示

但 lowering 规则本身仍然是 PUC-Lua 语义。Luau 需要单独的
`src/transformer/dialect/luau`，不能建立在 `puc_lua` 上继续修补。

### AST / generate

当前 AST 更接近“目标 dialect 感知的语法树”，而不是“原始语法忠实恢复”。
这对 Luau 是好事，因为第一阶段只需要补 target capability 和必要的语义映射。

但是 Luau 至少和当前 Lua 5.x target 有以下差异:

- 需要支持 `continue`
- 不应生成 `goto` / label
- 不应生成 `<close>`
- 不应生成 `global` / `global<const>` 这类当前实验性扩展
- 不需要在第一阶段引入 typed AST 节点

### tests / toolchain

当前测试体系里，runtime/compiler 选择仍然围绕 `lua` / `luac` 命名。

Luau 需要:

- 运行源码时使用 `luau`
- 编译源码时使用 `luau-compile --binary`

因此 tests 里需要按 dialect 选择 runtime/compiler，而不是继续写死命令名。

这里还有一个已经验证过的现实约束:

- 当前 `luau` CLI 不能像 stock `lua` 一样直接执行外部 bytecode 文件。
- 要运行 bytecode，需要走 `luau_load` 这类 VM API，而不是直接 `luau chunk.bc`。

因此第一阶段的 Luau `case-health` 只能稳定覆盖“源码执行 + 源码编译成功”，
不能直接复用 PUC-Lua 那套“编译后再执行 chunk”的校验协议。

## 设计原则

### 原则一: 先改模型，再写 Luau parser

如果公共 raw model 仍然是 PUC-Lua 形状，那么 Luau parser 只能被迫制造假数据。
这会直接污染后续层的判断依据，因此必须先完成模型拆分，再落 Luau 解析器。

### 原则二: 先打通测试工具链，再扩大实现面

Luau 相关 case 已经存在于 `tests/lua_cases/luau/`。应优先让它们进入
case-health 体系，这样后续每一层实现都能有稳定回归入口。

### 原则三: AST 第一阶段只承载“目标语法能力”

第一阶段 AST 的工作重点是增加 `Luau` target 与相关 capability，
而不是立刻增加类型系统、插值字符串、if-expression 这类 richer syntax。

## 分层设计

### 一、decompile 入口

需要在 `src/decompile/options.rs` 中新增 `DecompileDialect::Luau`，
并在 `src/decompile/pipeline.rs` 中挂接新的 parse entrypoint。

第一阶段建议:

- 只支持显式选择 `luau`
- 不尝试从 chunk bytes 自动识别

原因是 Luau chunk 没有 PUC-Lua 那样稳定的魔数入口，自动识别只能依赖启发式。

### 二、parser 层

#### 2.1 公共 raw model 重构

`src/parser/raw.rs` 需要从“单一 header + 单一 literal const pool”重构为:

- 公共 chunk / proto / debug / origin 抽象
- family-aware 的 header payload
- family-aware 的 constant pool payload
- family-aware 的 opcode / operands 空间

重构目标不是把所有 dialect 都抹平，而是让公共层只保留真正稳定的部分。

#### 2.2 新增 Luau parser 目录

新增:

- `src/parser/dialect/luau/mod.rs`
- `src/parser/dialect/luau/parser.rs`
- `src/parser/dialect/luau/raw.rs`
- `src/parser/dialect/luau/debug.rs`

这套实现不依赖 `puc_lua`。

#### 2.3 Luau parser 需要覆盖的最低语义

第一阶段 parser 至少需要稳定解码:

- string table
- proto table
- instruction stream
- constant table
- nested proto references
- line/debug info
- upvalue / capture 相关元数据

如果某些类型信息只服务于 typed Luau 恢复，而第一阶段不会消费，
可以先按“保留原始数据但不进入后续语义层”的方式落盘。

### 三、transformer 层

新增 `src/transformer/dialect/luau`，负责把 Luau bytecode 降到现有 low-IR。

第一阶段重点处理:

- import/global access
- method call
- closure + capture
- vararg
- generic for
- 关键条件跳转
- 算术 / 比较 / table access 的 Luau 变体

处理原则:

- 能表达为现有 low-IR 的，优先复用现有抽象。
- 不能无损表达的，先检查 low-IR 是否真的缺抽象，再决定是否扩展。
- 不在 transformer 里恢复类型语法糖。

### 四、AST / generate 层

需要新增 `AstDialectVersion::Luau` 及其 capability 组合。

第一阶段建议的 capability:

- `continue_stmt = true`
- `goto_label = false`
- `local_const = false`
- `local_close = false`
- `global_decl = false`
- `global_const = false`

这层的目标是:

- 让 HIR 能稳定落成 Luau 可接受的源码结构
- 避免生成 Luau 不支持的语法

如果后续发现当前 AST 在某些控制流恢复上过度依赖 `goto`，
应优先检查 structure / HIR 是否应调整，而不是在 emitter 里兜底改写。

### 五、测试体系与工具链

#### 5.1 case manifest

`tests/support/case_manifest.rs` 需要新增 `LuaCaseDialect::Luau`，
并为 Luau case 建立 suite 归属。

建议策略:

- 第一阶段只把 Luau case 纳入 `case-health`
- 等 parser + transformer + generate 基本打通后，再纳入
  `decompile-pipeline-health`

#### 5.2 运行器抽象

`tests/support/mod.rs` 需要把“选择 runtime/compiler 可执行文件名”升级成
按 dialect 决定命令协议的抽象，而不是继续使用固定的 `lua` / `luac` 组合。

最少要区分:

- 运行源码命令
- 编译源码命令
- 运行 chunk 命令

对 Luau 来说，`运行 chunk 命令` 当前应该是显式缺席的 capability，而不是假设
它和 PUC-Lua 一样存在。

#### 5.3 xtask

`xtask/src/toolchain.rs` 已经能下载并构建 Luau。
后续主要工作是让测试帮助函数和 manifest 正确消费 `luau` /
`luau-compile` 这组工具，而不是补新的拉取逻辑。

## 分阶段实施计划

### Phase 1: 测试入口和 dialect 枚举打底

目标:

- `DecompileDialect` 能表达 `Luau`
- tests 能按 dialect 选择正确的 runtime/compiler
- Luau case 能进入 `case-health`

涉及文件:

- `src/decompile/options.rs`
- `src/decompile/pipeline.rs`
- `tests/support/mod.rs`
- `tests/support/case_manifest.rs`

完成标准:

- 可以针对 Luau case 跑“源代码执行 / 编译 / chunk 执行”的健康检查
- 即使 parser 尚未接入 Luau，测试基础设施也已具备

补充:

- 对 Luau 的第一版完成标准应修正为“源码执行 / 编译成功”。
- `chunk 执行` 需要等后续补 dedicated bytecode runner 或 VM API 包装后再恢复。

### Phase 2: parser raw model 去 PUC-Lua 中心化

目标:

- 拆掉当前 PUC-Lua 专属 `ChunkHeader`
- 拆掉“公共常量池只包含字面量”的假设
- 给 Luau parser 留出合法的数据承载位

涉及文件:

- `src/parser/raw.rs`
- `src/parser/mod.rs`
- `src/parser/dialect/mod.rs`
- 现有 Lua51-Lua55 parser 的适配层

完成标准:

- Lua 5.1-5.5 parser 行为不回退
- Luau raw shape 不再需要 fake header / fake const pool

### Phase 3: Luau parser 落地

目标:

- 新增 `src/parser/dialect/luau`
- 能把 Luau chunk 解析成稳定 raw model

涉及文件:

- `src/parser/dialect/luau/*`
- `src/parser/mod.rs`

完成标准:

- Luau chunk 能停在 parse stage 并输出可检查的 debug dump
- parser 对已有 Luau case 的关键结构解码稳定

### Phase 4: Luau transformer 落地

目标:

- 新增 `src/transformer/dialect/luau`
- 能把 Luau raw instructions 降到 low-IR

涉及文件:

- `src/transformer/dialect/mod.rs`
- `src/transformer/dialect/luau/*`
- 必要时的 `src/transformer/common.rs`

完成标准:

- Luau case 能稳定跑到 transform stage
- 低层控制流、闭包、调用、table access 的表达与真实语义一致

### Phase 5: AST / generate 支持 Luau target

目标:

- 新增 `AstDialectVersion::Luau`
- generator 能输出 Luau 可接受源码

涉及文件:

- `src/ast/common.rs`
- `src/decompile/pipeline.rs`
- `src/generate/emit.rs`
- 相关 readability / naming / HIR 适配点

完成标准:

- Luau case 能进入 `decompile-pipeline-health`
- 反编译结果能被 `luau-compile` 重新编译
- 运行输出与原始 case 一致

### Phase 6: 覆盖面扩展与语法糖优化

目标:

- 扩展更多 Luau opcode / case
- 评估是否值得恢复部分 Luau-specific syntax sugar

这阶段不是“接入 Luau”所必需，只在基础语义稳定后再推进。

## AST 适配边界

第一阶段 AST 只需要承载“Luau 允许什么语法”。

可以延后处理的内容:

- typed function / local / table type annotation
- if-expression
- string interpolation
- compound assignment
- 泛型参数语法

这些都不属于“让 Luau 代码可重新执行”的必要条件。

## 风险清单

### 1. 常量池建模不当

如果仍然把 Luau 常量池压扁成“字面量数组 + 一堆 extra side table”，
后续 instruction lowering 很容易拿错索引语义。

### 2. 过早把 Luau 语法糖塞进 AST

如果在 parser / transformer 还不稳定时就引入 typed AST、
interpolated string 等 richer syntax，复杂度会快速失控，而且测试难以定位责任层。

### 3. 测试体系仍旧写死命令名

如果 `tests/support/mod.rs` 继续假设所有 dialect 都是 `lua` / `luac`，
后续再接 LuauJIT 或别的方言时会继续重复同一类问题。

## 当前决策

目前明确采用以下路线:

- Luau 作为独立 dialect family 接入
- 第一阶段只追求“输出 Luau 能执行的源码”
- 不恢复类型
- 不做自动识别，先要求显式选择 `luau`
- parser / transformer 各写一套 Luau 实现
- tests 按 dialect 选择不同可执行文件与编译协议

## 建议的推进顺序

为了减少返工，推荐严格按下面顺序实现:

1. 先改 tests/toolchain 抽象和 `DecompileDialect`
2. 再做 parser raw model 重构
3. 再写 Luau parser
4. 再写 Luau transformer
5. 最后补 AST / generate 的 Luau target

这样每一层失败时，问题边界都最清楚，不会把多个结构性问题混在同一轮里调试。
