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
  <a href="https://unluac.x3zvawq.com">在线工作区</a> ·
  <a href="https://github.com/x3zvawq/unluac-rs/releases">下载 CLI</a> ·
  <a href="./skills/unluac/SKILL.md">AI Agent Skill</a> ·
  <a href="https://docs.rs/unluac">Rust API 文档</a>
</p>

**让 Lua 字节码重新可读。** `unluac-rs` 是一个用 Rust 编写的多方言 Lua 反编译器，可以从编译后的字节码中恢复干净、语义等价的 Lua 源码，无论自己阅读、批量逆向还是交给 AI 分析都开箱即用。

## 核心特点

- **一套引擎覆盖 7 种方言**：支持 Lua 5.1、5.2、5.3、5.4、5.5、LuaJIT 2.1 和 Luau，按文件内容自动识别版本。
- **开箱即读的输出质量**：默认启用启发式命名、安全的 `self` 方法语法还原（`function M:foo(...)`）、短路表达式折叠、精简注释（`minimal`），并提供面向大型配置表的网格对齐排版。
- **为真实脚本和 AI 工作流设计**：支持目录递归并发批量反编译、单函数（`--proto`）源码导出、`--format json` 结构化输出、`readable / exact / ai` 一键预设，以及配套的 [Agent Skill](./skills/unluac/SKILL.md)。
- **多种使用形态**：Web 浏览器本地运行（WebAssembly，不上传任何文件）、独立命令行工具、Rust 库（`unluac`）与 JavaScript/TypeScript 包（`unluac-js`）。

---

## 快速上手

### 1. 在线工作区（Web）

**[打开 unluac.x3zvawq.com →](https://unluac.x3zvawq.com)**

- 直接拖入单个文件或整个文件夹即可反编译（按内容自动识别方言、跳过非字节码文件，并支持一键本地打包下载 `.zip`）。
- 按 **`Ctrl/Cmd + Shift + F`** 可跨所有已加载文件与常量池全文搜索，点击命中行直接跳转定位。
- 设置抽屉顶部提供 **推荐阅读 / 精确还原 / 给 AI 分析** 三个一键预设；工具栏内置 **对比视图（Diff）** 与 **复制给 AI**，一键生成精简 Markdown 代码块。
- 展开底部 **结构分析** 面板可切换查看函数大纲 / 调用树（点击直接跳转高亮源码区间）、过滤与复制常量表，以及每个函数的控制流图（CFG）。
- 所有解析与反编译都在本地浏览器通过 WebAssembly 完成，不会上传文件。

如需本地启动 Web 版，见 [packages/unluac-web/README.md](./packages/unluac-web/README.md)。

### 2. 命令行工具（`unluac-cli`）

从 [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases) 下载对应平台的二进制文件，或从源码安装：

```bash
cargo install --path packages/unluac-cli
```

常用命令：

```bash
# 单文件反编译（自动识别方言；位置参数与 -i 均支持）
unluac-cli sample.luac -o recovered.lua

# 从标准输入读取
cat sample.luac | unluac-cli -

# 递归并发批量反编译整个目录（自动跳过非字节码文件）
unluac-cli ./scripts_bin -o ./scripts_src -j 8

# 使用场景预设：readable（阅读）/ exact（精确）/ ai（省 Token）
unluac-cli sample.luac --preset readable -o recovered.lua
unluac-cli sample.luac --preset ai

# 指定旧编码读取中文脚本（如 GBK 游戏脚本）
unluac-cli sample.luac -e gbk -o recovered.lua

# 超大脚本按需定位：先导出所有函数和字符串常量摘要，再单独反编译目标函数
unluac-cli big.luac --list-protos --format json
unluac-cli big.luac --proto 17

# 用本地编译器先编译 .lua 再反编译（用于调试/对比）
unluac-cli -s example.lua -D lua5.4
```

#### 常用参数与退出码

| 参数 | 默认值 | 说明 |
| --- | --- | --- |
| `<INPUT>` / `-i` | — | 输入字节码文件、`-`（标准输入）或目录（需配合 `-o <输出目录>`） |
| `-D, --dialect` | `auto` | 手动指定方言（`lua5.1`..`lua5.5`、`luajit`、`luau`） |
| `--preset` | — | `readable`（对齐表格）、`exact`（严格模式+编号命名+原字节字符串）、`ai`（紧凑表格） |
| `-n, --naming-mode` | `heuristic` | 缺少 debug 信息时的命名：`heuristic`（启发式）、`simple`（简短通用）、`debug-like`（编号） |
| `--comment` | `minimal` | 注释详细度：`minimal`（精简文件头与源码行号）、`full`（含每函数 proto 统计）、`none`（关闭） |
| `-e, --encoding` | `auto` | 字符串常量解码编码（`utf-8`、`gbk`、`big5`、`shift_jis`、`euc-kr` 等） |
| `--readable-strings` | `true` | 将已解码字符串直接输出为可读 UTF-8（关闭则保留原始字节转义） |
| `--table-style` | `balanced` | 表排版风格：`compact`、`balanced`、`aligned`、`expanded`（详见[对齐表说明](./docs/table-alignment.md)） |
| `-g, --generate-mode` | `permissive` | `permissive` 遇单函数失败时保留诊断注释并继续；`strict` 要求全部合法否则报错退出 |
| `--format` | `text` | 输出格式：`text` 或 `json`（支持单文件、`--list-protos` 和批量汇总） |
| `-j, --jobs` | CPU 核数 | 目录批量模式下的并发线程数 |

**退出码**：`0` = 干净还原为目标方言源码，`2` = 宽松模式下部分函数降级为诊断伪码（`diagnostic-pseudocode`），`1` = 硬错误（文件损坏、IO 错误或严格模式失败）。

完整选项见 `unluac-cli --help`；查看各流水线中间产物见[调试手册](./docs/debug.md)。

### 3. AI Agent Skill

如果你使用 Claude Code、Codex、Antigravity、Cursor 等 AI 编程助手分析反编译脚本，可以直接使用仓库根目录提供的 [`skills/unluac/SKILL.md`](./skills/unluac/SKILL.md)。它内置了批量反编译、中文编码指定、用 `--list-protos --format json` + `--proto <id>` 按需读取超大脚本以及退出码处理等最佳实践，能显著省去反复试错与 Token 消耗。

### 4. Rust 库

```bash
cargo add unluac
```

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

更多选项与流水线结构见 [Rust API 文档](https://docs.rs/unluac)。

### 5. JavaScript / TypeScript（`unluac-js`）

```bash
npm install unluac-js
```

```js
import { readFile } from "node:fs/promises";
import { decompile, decompileWithMeta } from "unluac-js";

const bytes = await readFile("sample.luac");

// 直接拿到 Lua 源码字符串
const source = await decompile(bytes);

// 或同时获取方言、输出类型与失败 proto 列表（不含重型 CFG）
const meta = await decompileWithMeta(bytes, {
  generate: { tableStyle: "aligned", comment: "minimal" },
});
console.log(meta.dialect, meta.kind, meta.protoCount, meta.failedProtos);
```

浏览器打包、`detectDialect()`、`decompileRich()` 与完整参数列表见 [packages/unluac-js/README.md](./packages/unluac-js/README.md)。

---

## 输出特性简介

- **命名策略（`-n`）**：只要字节码保留了合法 debug 符号，所有模式都会优先使用原变量名（除非传入 `--ignore-debug`）。无 debug 信息时，默认 `heuristic` 会结合表达式、字段访问、标准库参数和 `self` 接收者推断易读名称；`simple` 使用简短通用名（`a`、`b`、`value` 与循环变量 `i`/`k`/`v`）；`debug-like` 使用确定性编号名（`p1_0`、`r1_0`）方便对照字节码。提示：Rust 核心库 `unluac` 默认使用 `GenerateMode::Strict`，CLI / WASM / JS 默认使用 `Permissive`。设计细节见 [Naming 与 Generate](./docs/design/6.naming-and-generate.md)。
- **表格对齐（`--table-style aligned`）**：自动把同类字面量数组排成整齐列网格、把记录表的 `=` 纵向对齐，阅读游戏配置表非常舒服。完整示例见[表格对齐说明](./docs/table-alignment.md)。
- **可读字符串**：默认输出可读 UTF-8 文本（`--readable-strings true`）。已知源脚本使用 GBK/Big5/Shift_JIS 时请直接用 `-e` 指定，避免 `auto` 对极短字符串误判；若需要严格保留原始字节协议，请传 `--readable-strings false`。

---

## 贡献与反馈

欢迎提交真实字节码样本和问题反馈！提 [Issue](https://github.com/x3zvawq/unluac-rs/issues) 时请尽量附上：

- 可复现的最小字节码样本（如有原始 `.lua` 源码更好）；
- 对应的 Lua 方言和使用的参数；
- 预期结果与实际输出/报错。

参与项目开发可查阅：

- 架构与模块地图：[docs/design.md](./docs/design.md)
- 流水线调试速查：[docs/debug.md](./docs/debug.md)
- 测试与回归协议：[docs/design/7.debugging-and-test.md](./docs/design/7.debugging-and-test.md)
- Web 工作区开发指南：[packages/unluac-web/README.md](./packages/unluac-web/README.md)

## License

采用 [MIT License](./LICENSE.txt) 开源。

## 鸣谢

- 设计与实现深受 [metaworms 的 Lua 反编译器](https://luadec.metaworm.site) 及其技术文章启发。
- 本项目经历过 **ChatGPT**、**Claude**、**Gemini** 等 Agent 的维护，当前版本由 **Gemini 4 Neon** 重构并持续进行维护。赞美 Neon 神力！
- 感谢每一位提交真实样本与反馈的社区用户。
