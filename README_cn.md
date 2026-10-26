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

字符串默认以解码后的可读文本输出为 UTF-8（`--readable-strings true`）。例如 GBK 输入可用
`unluac-cli -i sample.luac --encoding gbk -o recovered.lua` 直接输出中文；`auto` 对短字符串可能误判，
已知字符集时请显式指定。需要保持字符串的原始字节、长度和二进制协议时，使用
`--readable-strings false`。无可用解码文本时仍输出原字节转义。Rust 对应
`options.generate.readable_strings`，JS/WASM 对应 `generate.readableStrings`，Web 的“可读字符串”开关默认开启。
对生成的 UTF-8 源码重新编译后，应按 UTF-8 解码，不再沿用原输入的 GBK 设置。

通过 `--naming-mode` / `-n` 选择后备命名策略。所有模式优先保留合法 debug 名；使用 `--ignore-debug` 可忽略它们。

| 模式 | 无 debug 信息时的名字 |
| --- | --- |
| `debug-like`（默认） | `p1_0`、`r1_0` 等带编号名字，便于对照 |
| `simple` | `a`、`b`、`value` 等通用名，保留基本循环和函数角色 |
| `heuristic` | 根据表达式、字段用途、模块路径和调用名称推测，如 `arr`、`lvl`、`slot`、`user` |

例如：`unluac-cli -i sample.luac -n heuristic`。启发式名字是可读性提示，不保证恢复原名或运行时类型。具体边界见 [Naming 设计](./docs/design/8.naming.md)。

Heuristic 还会使用小型标准库签名表：`os.date` 的实参可提示 `format/time`，`string.sub` 可提示 `text/start_index/end_index`。更具体的字段用途优先，角色冲突时保留通用名。

表构造器通过 `--table-style` 提供四种排版风格。`compact`、`balanced`（默认）与 `expanded` 保持既有行为。`aligned` 风格对每张表按顺序尝试四种布局：

1. **单行** — 整个构造器放得下当前行：`local anchors = { 10, 20, 30 }`。
2. **内容单行** — 否则先尝试把全部内容平铺进花括号内缩进一层的下一行：
   ```lua
   local fallback = {
       alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6, eta = 7, theta = 8
   }
   ```
3. **对齐网格** — 否则纯数组且元素全部是同类小字面量（数字、短字符串、布尔、`nil` 或普通名字）时，按行输出多个单元格并用空格填充，使值按列上下对齐。
4. **逐行记录** — 其余情况（任何字典、混合数组、超宽字符串、非字面量元素）；嵌套表按自身缩进套用同样规则。多行记录带尾逗号，追加字段不会改写已有行。

四个参数只作用于 `aligned` 风格：

| 参数 | 默认 | 作用 |
| --- | --- | --- |
| `--table-align-width` | 100 | 限制网格行渲染宽度（含缩进）；除非单个单元格自身超宽，行不会超出该预算。 |
| `--table-align-string-width` | 16 | 限制可进入网格的字符串字面量渲染宽度（含引号）；超宽字符串让整张表退回逐行布局。 |
| `--table-align-eq` | true | 多行表内按 `=` 对齐记录键：键填充到本对齐系列最宽键的列。`--table-align-eq=false` 保持 `=` 两侧单空格。 |
| `--table-align-eq-max-spaces` | 8 | 限制 `=` 对齐的填充量：需要更多填充的键会开启新的对齐系列，而不是把所有行都撑开。 |
| `--table-drop-index-keys` | false | 把连续的显式 `[1]..[n]` 构造器键改写成位置字段（见下）。 |

各参数的具体效果：

```lua
-- 默认：--table-align-eq 把键对齐到本系列最宽键
local config = {
    name    = "unluac",
    threads = 4,
    paths   = { "/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua" },
    retries = 3,
}
-- --table-align-eq=false：同一张表，无填充
--     name = "unluac",
--     threads = 4,

-- --table-align-eq-max-spaces=2：10 字符的键不再撑开短键；
-- 对齐系列断开，剩余键保持单空格
local options = {
    id   = "op",
    kind = "select",
    retries = 4,
    timeout_ms = 1500,
}

-- --table-align-width=40：网格每行装更少的单元格（8 而不是 15）
local values = {
    10, 11, 12, 13, 14, 15, 16, 17,
    18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39,
}

-- --table-align-string-width=6：13 字符字符串超过上限，
-- 整张表退回逐行布局而不是网格
local labels = {
    "longstring1",
    "longstring2",
}

-- --table-drop-index-keys=true：连续的显式索引键改写为位置字段；
-- 普通数组字面量编译成不带键的 SETLIST 指令，所以输出里的 `[1] =`
-- 必然对应显式写键的源码。改写保持求值顺序与逐字段副作用，只有
-- 未定义的 pairs 顺序变化（哈希部分变成数组部分）。有缺口、乱序、
-- 或与位置字段混用的表保持原样。
local keyed = { "alpha", "beta" }        -- 原为：{ [1] = "alpha", [2] = "beta" }
local mixed = { mode = "dlg", "alpha", "beta", tag = 3 }
                                         -- 原为：{ mode = "dlg", [1] = "alpha", [2] = "beta", tag = 3 }
local untouched = { [1] = "alpha", [3] = "gamma" }   -- 有缺口：保持原样
```

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
