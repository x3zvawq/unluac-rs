# unluac-rs

简体中文 | [English](./README_en.md)

## 简介

一个基于 Rust 的、支持多种 dialect 的 Lua 反编译器，目前支持以下版本 / dialect：

- [Lua 5.1](https://www.lua.org/versions.html#5.1)
- [Lua 5.2](https://www.lua.org/versions.html#5.2)
- [Lua 5.3](https://www.lua.org/versions.html#5.3)
- [Lua 5.4](https://www.lua.org/versions.html#5.4)
- [Lua 5.5](https://www.lua.org/versions.html#5.5)
- [LuaJIT 2.1](https://luajit.org/)
- [Luau](https://luau.org/)

基于控制流分析、支配树分析等手段，去除了大多数中间变量。对于当前仓库中的 case 来说，基本可以恢复源码形状。

当前仓库的代码组织大致如下：

- 根包 `unluac`：核心反编译库
- `packages/unluac-cli`：命令行入口
- `packages/unluac-wasm`：wasm 绑定层
- `packages/unluac-js`：npm 包装层
- `xtask`：测试与 Lua 工具链编排

## 使用方式

目前仓库已经围绕以下几种使用方式组织代码，分别面向不同的集成和分发场景：

1. **命令行工具**：当前仓库内可以直接通过 `cargo unluac` 调试使用，后续 GitHub Release 二进制也会从同一套 CLI 产出。
2. **Rust库**：可以将核心库 `unluac` 集成到 Rust 项目中，直接调用反编译 pipeline。
3. **npm包**：仓库内提供了 `packages/unluac-js` 作为 npm 包装层，面向 Node.js / 浏览器等 JavaScript 环境。
4. **WebAssembly**：仓库内提供了 `packages/unluac-wasm` 作为 wasm 绑定层，可供其他语言或运行时继续封装。

### 命令行工具

当前仓库里最直接的命令行入口是：

```bash
cargo unluac -- --input /absolute/path/to/chunk.out --dialect=lua5.1
cargo unluac -- --source tests/lua_cases/lua5.1/01_setfenv.lua --dialect=lua5.1
```

等价命令：

```bash
cargo run -p unluac-cli -- --input /absolute/path/to/chunk.out --dialect=lua5.1
```

说明：

- CLI 当前要求你显式传入 `--input` 或 `--source`
- 如果传入 `--source`，CLI 会先调用 `lua/build/<dialect>/` 下的编译器生成 chunk，再执行反编译
- CLI 默认直接输出纯源码，不打印 debug dump
- CLI 的 dialect / parse / readability / naming / generate 默认值仍与 [examples/debug.rs](./examples/debug.rs) 共用同一份 repo 调试 preset
- 如果你想看 repo debug preset 风格的调试输出，可以显式附加 `--debug`

| 参数 | 说明 | 默认值 |
| - | - | - |
| `--input` | 已编译 chunk 路径 | 无 |
| `--source` | Lua 源码路径，CLI 会先编译再反编译 | 无 |
| `--dialect` | 反编译 / 编译时使用的 dialect | `lua5.1` |
| `--stop-after` | 反编译 pipeline 截止阶段 | `generate` |
| `--debug` | 启用 debug dump | `false` |
| `--detail` | 调试输出粒度 | `verbose`（启用 debug 时） |
| `--color` | 调试输出颜色模式 | `always`（启用 debug 时） |
| `--timing` | 输出耗时报告 | `false` |
| `--parse-mode` | parser 宽松 / 严格模式 | `permissive` |
| `--encoding` | 字符串解码编码 | `utf-8` |
| `--decode-mode` | 字符串解码失败策略 | `strict` |
| `--naming-mode` | 命名策略 | `debug-like` |

更多调试相关命令和参数可参考 [docs/debug.md](./docs/debug.md)。

### Rust库

当前核心库包名为 `unluac`。

如果你希望在本地仓库或其他 Rust 项目里直接集成，当前最稳妥的方式是使用 `path` 或 `git` 依赖：

```toml
[dependencies]
unluac = { git = "https://github.com/X3ZvaWQ/unluac-rs" }
```

最小调用示例：

```rust
use std::fs;

use unluac::decompile::{decompile, DecompileDialect, DecompileOptions, DecompileStage};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bytes = fs::read("sample.out")?;

    let result = decompile(
        &bytes,
        DecompileOptions {
            dialect: DecompileDialect::Lua51,
            target_stage: DecompileStage::Generate,
            ..DecompileOptions::default()
        },
    )?;

    if let Some(generated) = result.state.generated.as_ref() {
        println!("{}", generated.source);
    }

    Ok(())
}
```

这里需要注意：

- 库入口直接接受“已编译 chunk 的字节”，不会替你先编译 Lua 源码
- 如果你手上只有 Lua 源码，当前更方便的方式通常是直接用 CLI
- 主反编译入口在 [src/decompile/mod.rs](./src/decompile/mod.rs) 下统一导出

### Npm包

仓库内的 npm 包装层位于 [packages/unluac-js](./packages/unluac-js)。

它当前是一个很薄的 TypeScript 壳层，会调用 `packages/unluac-wasm` 产出的 wasm 绑定，并将最终发布内容收敛到 `dist/`。

本地构建方式：

```bash
cd packages/unluac-js
npm install
npm run build
```

构建完成后，发布目录位于：

```text
packages/unluac-js/dist
```

对外暴露的主要 API 是：

- `init(input?)`
- `decompile(bytes, options?)`
- `supportedOptionValues()`

Node.js 环境中的最小示例：

```js
import { decompile } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");
const result = await decompile(chunkBytes, {
  dialect: "lua5.1",
  targetStage: "generate",
});

console.log(result.generatedSource);
```

浏览器与更完整的说明可参考 [packages/unluac-js/README.md](./packages/unluac-js/README.md)。

### WebAssembly

wasm 绑定层位于 [packages/unluac-wasm](./packages/unluac-wasm)。

它当前使用 `wasm-bindgen` 和 `serde-wasm-bindgen` 暴露 JS 友好的对象协议，而不是直接把 Rust 内部类型布局暴露到边界外。

如果你只是想在 JavaScript / TypeScript 环境使用，优先建议直接使用上面的 npm 包装层。  
如果你需要把 wasm 接到其他语言或运行时，也可以：

- 从 npm 包的发布目录中获取已经构建好的 `unluac_wasm.js` 与 `unluac_wasm_bg.wasm`
- 或者直接基于本仓库的 `packages/unluac-wasm` 自行构建并准备对应语言的绑定

如果你打算把 wasm 支持扩展到某个特定语言或运行时，欢迎提交 PR。

## 贡献与反馈

欢迎任何形式的贡献，无论是代码、文档、测试用例，还是其他方面的改进。
如果你在使用过程中遇到任何问题，或者有任何建议和想法，欢迎随时提交 issue；如果项目在某些 case 上表现不佳，也可以将对应的二进制文件作为附件上传，方便定位问题。

## License MIT 

本项目采用 MIT License 发布，具体内容见 [LICENSE.txt](./LICENSE.txt)。

## 鸣谢

- [metaworms's lua decompiler](https://luadec.metaworm.site) - 该项目的设计与实现受到了这个项目的启发，也受到了作者教程的帮助。当前该网站已经无法访问。
- Codex + GPT-5.4 - 该项目的大部分代码由 Codex 和 GPT-5.4 生成，感谢 OpenAI 提供的强大工具。
