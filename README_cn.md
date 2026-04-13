# unluac-rs

简体中文 | [English](./README.md)

> 当前仓库仍处于测试阶段，行为、接口和输出细节后续都可能继续调整。非常欢迎提交反编译失败、输出不理想或存在兼容性问题的测试样例，也欢迎通过 issue / discussion 提出使用反馈、改进建议和发布体验上的意见。
> 如果你正在使用这个反编译器，并且遇到了某些字节码文件反编译效果不佳的情况，请务必附上可复现样本；这些样本对我持续优化现有逻辑、补齐边界 case 和提升输出质量非常关键。

一个基于 Rust 的、多版本多方言 Lua 反编译器。

当前已经发布的对外入口包括：

- Rust crate [`unluac`](https://crates.io/crates/unluac)
- GitHub Releases 上的独立 CLI 二进制
- npm 包 [`unluac-js`](https://www.npmjs.com/package/unluac-js)
- [docs.rs](https://docs.rs/unluac) 上的 Rust API 文档

## 简介

当前项目支持以下 Lua 版本 / dialect：

- [Lua 5.1](https://www.lua.org/versions.html#5.1)
- [Lua 5.2](https://www.lua.org/versions.html#5.2)
- [Lua 5.3](https://www.lua.org/versions.html#5.3)
- [Lua 5.4](https://www.lua.org/versions.html#5.4)
- [Lua 5.5](https://www.lua.org/versions.html#5.5)
- [LuaJIT 2.1](https://luajit.org/)
- [Luau](https://luau.org/)

项目会结合控制流分析、支配树分析和后续规范化 pipeline，尽量消除中间变量。对于当前仓库中已覆盖的 case，通常可以恢复出与原始源码较接近的结构。

当前仓库的代码组织大致如下：

- 根包 `unluac`：核心反编译库
- `packages/unluac-cli`：命令行入口
- `packages/unluac-wasm`：wasm 绑定层
- `packages/unluac-js`：npm 包装层
- `xtask`：测试与 Lua 工具链编排

## 使用方式

项目当前主要通过以下几种入口分发：

1. **命令行工具**：使用 GitHub Releases 提供的独立二进制，或者直接在本仓库中运行 / 构建 `unluac-cli`。
2. **Rust 库**：在 Rust 项目中引入已发布的 `unluac` crate，直接调用反编译 pipeline。
3. **npm 包**：安装 `unluac-js`，面向 Node.js 或基于打包器的浏览器环境。
4. **WebAssembly**：直接使用 `packages/unluac-wasm`，适合继续为其他语言或运行时做封装。

### 命令行工具

当前仓库中发布的 CLI 包名是 `unluac-cli`。

推荐安装方式：

- 从 [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases) 下载独立二进制，并放到 PATH 下，建议使用稳定名字例如 `unluac-cli`
- 从本地仓库构建并安装：

```bash
cargo install --path packages/unluac-cli
```

- 在仓库里直接运行：

```bash
cargo run -p unluac-cli -- --help
```

如果你就在这个仓库里开发，`.cargo/config.toml` 里仍然保留了 `cargo unluac -- ...` 这个本地 alias；但文档里的标准 CLI 名称统一写成 `unluac-cli`，以便和发布后的包名保持一致。

常见用法：

```bash
unluac-cli -i /absolute/path/to/chunk.out -D lua5.1
unluac-cli -s tests/lua_cases/lua5.1/01_setfenv.lua -D lua5.1
unluac-cli -i /absolute/path/to/chunk.out -D lua5.1 -o /tmp/case.lua
```

说明：

- CLI 要求你显式传入 `-i/--input` 或 `-s/--source`
- 如果传入 `-s/--source`，CLI 会先调用外部编译器生成 chunk，再执行反编译
- GitHub Releases 提供的独立二进制不会自带 Lua 编译器；`-s/--source` 只有在你显式传入 `-l/--luac`，或运行环境里存在 `lua/build/<dialect>/` / PATH 上的兼容编译器时才可用
- 如果传入 `-o/--output`，CLI 会把最终生成源码写入目标文件，而不是输出到 stdout
- `-o/--output` 只支持纯最终源码输出，不能和 debug / timing 参数一起使用，也不能和早于 `generate` 的 `--stop-after` 组合
- CLI 默认直接输出纯源码，只有显式请求时才会输出 debug dump
- `unluac-cli --help` 与 `unluac-cli --version` 都会附带仓库链接
- CLI 默认值来自核心库的 `DecompileOptions::default()`，但 CLI 会默认关闭 debug 输出，只有你显式开启时才打印调试内容

输入参数：

| 参数 | 说明 | 默认值 |
| - | - | - |
| `-D`, `--dialect` | 反编译 / 编译时使用的 dialect | `lua5.1` |
| `-i`, `--input` | 已编译 chunk 路径 | 无 |
| `-s`, `--source` | Lua 源码路径，CLI 会先调用外部编译器，再执行反编译 | 无 |
| `-l`, `--luac` | 显式指定 `--source` 使用的外部编译器路径 | 先尝试 `lua/build/<dialect>/`，否则回退到 PATH 上的兼容编译器 |
| `-e`, `--encoding` | 字符串解码编码（支持 [Encoding Standard](https://encoding.spec.whatwg.org/) 定义的所有标签，如 `utf-8`、`gbk`、`shift_jis`、`euc-kr`、`big5`） | `utf-8` |
| `-m`, `--decode-mode` | 字符串解码失败策略 | `strict` |
| `-p`, `--parse-mode` | parser 严格 / 宽松模式 | `permissive` |

调试参数：

| 参数 | 说明 | 默认值 |
| - | - | - |
| `-d`, `--debug` | 启用 debug 输出；未显式指定 `--dump` 时默认打印当前目标阶段 | `false` |
| `--dump` | 输出一个或多个 pipeline 阶段；可重复传入 | 无 |
| `--detail` | 调试输出粒度 | `normal`（启用 debug 时） |
| `-c`, `--color` | 调试输出颜色模式 | `auto` |
| `--proto` | 仅输出指定 proto id 的调试结果 | 无 |
| `-t`, `--timing` | 输出耗时报告 | `false` |

可读性与命名参数：

| 参数 | 说明 | 默认值 |
| - | - | - |
| `--return-inline-max-complexity` | return 表达式内联复杂度上限 | `10` |
| `--index-inline-max-complexity` | 表索引表达式内联复杂度上限 | `10` |
| `--args-inline-max-complexity` | 调用参数内联复杂度上限 | `6` |
| `--access-base-inline-max-complexity` | 访问基表达式内联复杂度上限 | `5` |
| `-n`, `--naming-mode` | 命名策略 | `debug-like` |
| `--debug-like-include-function` | debug-like 命名是否包含函数形状名字 | `true` |

生成与输出参数：

| 参数 | 说明 | 默认值 |
| - | - | - |
| `--indent-width` | 生成源码的缩进宽度 | `4` |
| `--max-line-length` | 软换行参考宽度 | `100` |
| `--quote-style` | 字符串引号风格 | `min-escape` |
| `--table-style` | 表构造器布局风格 | `balanced` |
| `--conservative-output` | 是否偏向保守输出 | `true` |
| `--comment` | 是否输出 generate 阶段注释和元信息 | `true` |
| `-g`, `--generate-mode` | 目标 dialect 不支持语法时的处理策略 | `strict` |
| `--stop-after` | pipeline 截止阶段 | `generate` |
| `-o`, `--output` | 将最终生成源码写入文件，而不是输出到 stdout | stdout |

`--dump` 和 `--stop-after` 这类接收阶段名的参数支持以下取值：
`parse`、`transform`、`cfg`、`graph-facts`、`dataflow`、`structure-facts`、`hir`、`ast`、`readability`、`naming`、`generate`。

更多调试命令和 CLI 工作流可参考 [docs/debug.md](./docs/debug.md)。

### Rust 库

当前发布到 crates.io 的 crate 名称是 `unluac`。

如果你使用正式发布版本，推荐直接依赖 crates.io：

```toml
[dependencies]
unluac = "1"
```

如果你需要 `main` 分支上的最新未发布改动，再使用 `git` 依赖：

```toml
[dependencies]
unluac = { git = "https://github.com/x3zvawq/unluac-rs" }
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

- 库接口直接接受“已编译 chunk 的字节”，不会替你先编译 Lua 源码
- 如果你手上只有 Lua 源码，通常更方便的入口还是 CLI
- 主反编译入口统一从 [src/decompile/mod.rs](./src/decompile/mod.rs) 导出

### npm 包

当前发布到 npm 的包名是 [`unluac-js`](https://www.npmjs.com/package/unluac-js)。

安装方式：

```bash
npm install unluac-js
```

`unluac-js` 是基于 `packages/unluac-wasm` 产物提供的一层轻量 TypeScript 包装，对外暴露适合 JavaScript / TypeScript 环境的初始化与反编译 API。

发布到 npm 的 wasm 构建会裁掉 `debug` / `timing` 能力，以控制包体积；CLI 和 Rust 库仍保留完整调试能力。npm 包的 `decompile()` 会直接返回最终源码字符串，而不是暴露中间 pipeline 元信息。

当前主要 API 包括：

- `init(input?)`
- `decompile(bytes, options?)`
- `supportedOptionValues()`

Node.js 环境中的最小示例：

```js
import { decompile } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");
const source = await decompile(chunkBytes, {
  dialect: "lua5.1",
});

console.log(source);
```

浏览器场景和更完整的包级说明可参考 [packages/unluac-js/README.md](./packages/unluac-js/README.md)。

### WebAssembly

wasm 绑定层位于 [packages/unluac-wasm](./packages/unluac-wasm)。

它使用 `wasm-bindgen` 与 `serde-wasm-bindgen` 暴露更适合 JS 消费的对象协议，而不是直接把 Rust 内部布局暴露到边界外。

如果你只是想在 JavaScript / TypeScript 环境里使用，优先建议直接使用上面的 npm 包。
如果你需要把 wasm 接到其他语言或运行时，也可以：

- 直接从 npm 包中取用构建好的 `unluac_wasm.js` 与 `unluac_wasm_bg.wasm`
- 或者基于本仓库里的 `packages/unluac-wasm` 自行构建并准备特定语言的绑定
- 或者直接消费 GitHub Releases 中附带发布的 `unluac_wasm_bg.wasm`

如果你打算把 wasm 支持扩展到某个特定语言或运行时，欢迎提交 PR。

## 贡献与反馈

欢迎任何形式的贡献，无论是代码、文档、测试用例，还是其他方面的改进。
如果你在使用过程中遇到问题，或者有建议和想法，欢迎提交 issue；如果项目在某些 case 上表现不佳，也欢迎附上对应的二进制文件，方便定位问题。

## License

本项目采用 MIT License 发布，具体内容见 [LICENSE.txt](./LICENSE.txt)。

## 鸣谢

- [metaworms's lua decompiler](https://luadec.metaworm.site) - 本项目的设计与实现受到了它的启发，作者的教程也提供了很多帮助。当前该网站已经无法访问。
- 本项目部分代码由 GPT-5.4 以及 Claude Opus 4.6 生成。
