<p align="center">
  <img src="./logo.svg" width="112" height="112" alt="unluac-rs logo" />
</p>

<h1 align="center">unluac-rs</h1>

<p align="center">简体中文 | <a href="./README.md">English</a></p>

<p align="center">
  <a href="https://crates.io/crates/unluac"><img src="https://img.shields.io/crates/v/unluac?style=flat-square&amp;color=147d69" alt="crates.io" /></a>
  <a href="https://www.npmjs.com/package/unluac-js"><img src="https://img.shields.io/npm/v/unluac-js?style=flat-square&amp;color=147d69" alt="npm" /></a>
  <a href="https://github.com/x3zvawq/unluac-rs/actions/workflows/release.yml"><img src="https://img.shields.io/github/actions/workflow/status/x3zvawq/unluac-rs/release.yml?style=flat-square&amp;label=release%20checks" alt="Release checks" /></a>
  <a href="https://github.com/x3zvawq/unluac-rs/actions/workflows/deploy-web.yml"><img src="https://img.shields.io/github/actions/workflow/status/x3zvawq/unluac-rs/deploy-web.yml?style=flat-square&amp;label=web%20build" alt="Web build and deployment" /></a>
  <a href="https://docs.rs/unluac"><img src="https://img.shields.io/docsrs/unluac?style=flat-square" alt="Rust API documentation" /></a>
  <a href="./LICENSE.txt"><img src="https://img.shields.io/badge/license-MIT-596584?style=flat-square" alt="MIT License" /></a>
</p>

<p align="center">
  <a href="https://unluac.x3zvawq.com">在线体验</a> ·
  <a href="https://github.com/x3zvawq/unluac-rs/releases">下载 CLI</a> ·
  <a href="https://docs.rs/unluac">API 文档</a>
</p>

## 简介

**让 Lua 字节码重新可读。** unluac-rs 是一个用 Rust 编写的多方言 Lua 反编译器，从编译后的 chunk 中恢复可读源码。你可以在浏览器工作区里探索程序，也可以通过命令行和库接口将反编译能力接入自己的工具。

- **统一支持 Lua 5.1–5.5、LuaJIT 2.1 与 Luau**，自动识别字节码方言。
- **以程序分析驱动源码恢复**：利用控制流、变量绑定和值的生命周期事实，重建表达式、函数与结构化语句。
- **适合混合版本的工作区**：导入文件或文件夹，为每个文件独立保存方言，编辑、导出源码，并查看函数、常量和控制流图。
- **多种使用方式**：通过 WebAssembly 在浏览器本地运行，使用独立 CLI，或接入 Rust、JavaScript 应用。Web 页面在你的设备上处理文件，无需上传服务器。

## 使用方式

### Web 页面

**[打开 unluac.x3zvawq.com →](https://unluac.x3zvawq.com)**

将编译后的文件拖入工作区，或选择打开文件、文件夹。字节码按内容识别，不限扩展名；也可以打开源码文件进行阅读和编辑。

每个文件独立保存 Lua 方言，点击版本标签即可修改；设置中的方言仅作为新导入文件的默认值。其他反编译设置会自动应用到已有文件。原始文件与方言选择保存在当前浏览器中，刷新后会重新生成结果；手动编辑的内容请在离开页面前下载保存。

通过**结构分析**面板查看函数与常量，选择函数后可以进一步浏览控制流图。专注阅读源码时，可折叠分析区以获得更多空间。

如果当前网络无法访问站点，可以使用下面的 CLI，或[在本地运行 Web 页面](./packages/unluac-web/README.md)。

### 命令行工具

从 [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases) 下载适合当前平台的二进制，或在本地仓库中安装：

```bash
cargo install --path packages/unluac-cli
```

自动识别方言，将字节码还原为源码：

```bash
unluac-cli -i sample.luac -o recovered.lua
```

也可以显式指定方言、从标准输入读取，或先编译源码再反编译：

```bash
unluac-cli -i sample.luac -D lua5.4
cat sample.luac | unluac-cli -i -
unluac-cli -s example.lua -D lua5.4
```

源码输入（`--source`）需要指定方言，并准备兼容的外部编译器；发布的 CLI 不附带编译器。可以用 `--luac` 指定其路径，或将它加入 PATH。源码编译默认剥离调试元数据，使用 `--strip false` 可保留；独立的 `--ignore-debug` 则让两种输入模式都不使用已有调试信息参与恢复。

需要目标方言可接受的 Lua 源码时，请使用 `--generate-mode strict`。默认的 permissive 模式可能为不可表达的结构输出诊断伪源码。`--output` 用于保存最终源码，不能与调试 dump、计时输出或提前停止流水线的选项组合。

完整的格式化、命名和解码选项见 `unluac-cli --help`；查看流水线中间结果的方法见[调试手册](./docs/debug.md)。

### Rust 库

```bash
cargo add unluac
```

库接口直接接收已编译 chunk 的字节；默认选项会自动识别方言，并执行到源码生成阶段。

```rust
use std::fs;
use unluac::decompile::{decompile, DecompileOptions};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bytes = fs::read("sample.luac")?;
    let result = decompile(&bytes, DecompileOptions::default())?;

    if let Some(generated) = result.state.generated.as_ref() {
        println!("{}", generated.source);
    }
    Ok(())
}
```

选项与流水线结果的详细说明见 [Rust API 文档](https://docs.rs/unluac)。

### JavaScript / TypeScript

```bash
npm install unluac-js
```

在 Node.js 中，包会自动初始化自带的 WebAssembly 模块：

```js
import { readFile } from "node:fs/promises";
import { decompile } from "unluac-js";

const bytes = await readFile("sample.luac");
const source = await decompile(bytes, { dialect: "auto" });
console.log(source);
```

此外还提供 `detectDialect()`、`decompileRich()`、`init()` 和 `supportedOptionValues()`。浏览器打包、显式 WASM 初始化与 Luau 向量构造器设置见 [JavaScript 使用说明](./packages/unluac-js/README.md)。完整的调试 dump 和计时能力由 CLI 与 Rust 库提供。

需要自行封装时，可从 [WebAssembly 包](./packages/unluac-wasm) 入手；JavaScript 场景通常直接使用 `unluac-js` 即可。

## 贡献与反馈

项目目前仍处于测试阶段，行为、接口和输出细节可能继续调整。欢迎提交反编译失败、效果不佳或存在兼容性问题的样本，也欢迎反馈工具使用与发布体验上的问题。

如果某个文件无法反编译，或生成代码的行为与预期不符，请[提交 issue](https://github.com/x3zvawq/unluac-rs/issues)，附上可复现样本、Lua 方言、使用的参数，以及预期和实际行为。若有原始源码，也请一并提供。真实样本是提高语义正确性与输出质量的重要依据；编译时丢弃的注释等信息无法通过反编译找回。

欢迎代码、文档和回归测试方面的贡献。参与开发可从[架构说明](./docs/design.md)、[测试协议](./docs/design/11.test.md)和 [Web 开发说明](./packages/unluac-web/README.md)开始。

## License

本项目采用 [MIT License](./LICENSE.txt)。

## 鸣谢

- [metaworms 的 Lua 反编译器](https://luadec.metaworm.site)及作者的教程，为本项目的设计与实现提供了启发。
- 本项目大部分代码由 **ChatGPT + Codex** 协助完成。特别感谢 **Astra** 在反编译实现与大规模重构中的贡献——Astra 太强了！项目早期也曾使用 **Claude** 参与开发。
- 感谢每一位提供测试样本、反馈问题、帮助改善源码恢复质量的使用者与贡献者。
