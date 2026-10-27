<p align="center">
  <img src="./logo.svg" width="112" height="112" alt="unluac-rs logo" />
</p>

<h1 align="center">unluac-rs</h1>

<p align="center"><a href="./README_cn.md">简体中文</a> | English</p>

<p align="center">
  <a href="https://crates.io/crates/unluac"><img src="https://img.shields.io/crates/v/unluac?style=flat-square&amp;color=147d69" alt="crates.io" /></a>
  <a href="https://www.npmjs.com/package/unluac-js"><img src="https://img.shields.io/npm/v/unluac-js?style=flat-square&amp;color=147d69" alt="npm" /></a>
  <a href="https://github.com/x3zvawq/unluac-rs/actions/workflows/release.yml"><img src="https://img.shields.io/github/actions/workflow/status/x3zvawq/unluac-rs/release.yml?style=flat-square&amp;label=release%20checks" alt="Release checks" /></a>
  <a href="https://github.com/x3zvawq/unluac-rs/actions/workflows/deploy-web.yml"><img src="https://img.shields.io/github/actions/workflow/status/x3zvawq/unluac-rs/deploy-web.yml?style=flat-square&amp;label=web%20build" alt="Web build and deployment" /></a>
  <a href="https://docs.rs/unluac"><img src="https://img.shields.io/docsrs/unluac?style=flat-square" alt="Rust API documentation" /></a>
  <a href="./LICENSE.txt"><img src="https://img.shields.io/badge/license-MIT-596584?style=flat-square" alt="MIT License" /></a>
</p>

<p align="center">
  <a href="https://unluac.x3zvawq.com">Open the Web App</a> ·
  <a href="https://github.com/x3zvawq/unluac-rs/releases">Download CLI</a> ·
  <a href="https://docs.rs/unluac">API Docs</a>
</p>

## Introduction

**Lua bytecode, made readable.** unluac-rs is a multi-dialect Lua decompiler written in Rust. It reconstructs readable source from compiled chunks, with a browser workspace for exploring the code and libraries for integrating decompilation into your own tools.

- **Lua 5.1–5.5, LuaJIT 2.1 and Luau** in one decompiler, with automatic bytecode dialect detection.
- **Source recovery built on program analysis:** control flow, bindings and value lifetimes inform the reconstruction of expressions, functions and structured statements.
- **A workspace for mixed versions:** open files or folders, keep a separate dialect per file, edit and export source, and inspect functions, constants and control-flow graphs.
- **Runs where you need it:** locally in your browser through WebAssembly, from the command line, or inside Rust and JavaScript applications. The web app processes files on your device without uploading them to a server.

## Usage

### Web

**[Open unluac.x3zvawq.com →](https://unluac.x3zvawq.com)**

Drop compiled files anywhere in the workspace, or open a file or folder. Bytecode is recognized by its contents, so no particular extension is required. Source files can also be opened for reading and editing.

Each file keeps its own Lua dialect. Click its version tag to change it; the dialect in Settings is only the default for new imports. Other decompilation settings apply to existing files automatically. File bytes and dialect choices are saved in the current browser; results are regenerated on reload, and manual edits should be downloaded before leaving.

Use the **Structure** panel to explore functions and constants, then select a function to inspect its control-flow graph. Collapse the panel when you want more room for the source.

If the hosted site is unavailable on your network, use the CLI below or [run the web app locally](./packages/unluac-web/README.md).

### CLI

Download a binary for your platform from [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases), or install from a local checkout:

```bash
cargo install --path packages/unluac-cli
```

Decompile a chunk with automatic dialect detection:

```bash
unluac-cli -i sample.luac -o recovered.lua
```

Choose a dialect explicitly, read from stdin, or compile a source file before decompiling it:

```bash
unluac-cli -i sample.luac -D lua5.4
cat sample.luac | unluac-cli -i -
unluac-cli -s example.lua -D lua5.4
```

Source input (`--source`) requires an explicit dialect and a compatible external compiler; release binaries do not bundle one. Set `--luac` to its path, or make it available on PATH. Source compilation strips debug metadata by default; use `--strip false` to retain it. `--ignore-debug` independently excludes available debug information from recovery for either input mode.

Use `--generate-mode strict` when you require target-compatible Lua output. The default permissive mode can return diagnostic pseudocode for constructs that cannot be represented. `--output` writes final source and cannot be combined with debug dumps, timing output or an earlier pipeline stage.

Strings default to decoded, readable UTF-8 text (`--readable-strings true`). For GBK input, use
`unluac-cli -i sample.luac --encoding gbk -o recovered.lua` to emit Chinese directly. Auto detection can
misidentify short strings, so specify a known input encoding. Use `--readable-strings false` to preserve
original string bytes, byte lengths and binary protocols. Strings without decoded text retain byte escapes.
The option is `options.generate.readable_strings` in Rust and `generate.readableStrings` in JS/WASM;
the Web “Readable Strings” switch is enabled by default. Recompiled generated UTF-8 source should be
decoded as UTF-8, rather than reusing the original input's GBK setting.

Choose fallback names with `--naming-mode` / `-n`. All modes prefer valid debug names; use `--ignore-debug` to disregard them.

| Mode | Names without debug information |
| --- | --- |
| `debug-like` (default) | Numbered names such as `p1_0` and `r1_0` for cross-referencing |
| `simple` | Generic `a`, `b`, `value`, plus basic loop/function roles |
| `heuristic` | Hints from expressions, field usage, module paths and call names, such as `arr`, `lvl`, `slot` and `user` |

For example: `unluac-cli -i sample.luac -n heuristic`. Heuristic names are readability hints, not recovered original names or runtime type guarantees. See [Naming](./docs/design/8.naming.md) for the mode boundaries.

Heuristic mode also uses a small standard-library signature table: arguments to `os.date` can suggest `format` and `time`, while `string.sub` suggests `text`, `start_index` and `end_index`. More specific field usage takes priority; conflicting roles keep generic names.

Table constructors support four layout styles via `--table-style`. `compact`, `balanced` (default) and `expanded` keep their existing behavior. The `aligned` style picks one of four layouts per table, trying them in order:

1. **Single line** — the whole constructor fits on the current line: `local anchors = { 10, 20, 30 }`.
2. **Content on one line** — otherwise the content is kept as a single indented line between the braces whenever it fits there:
   ```lua
   local fallback = {
       alpha = 1, beta = 2, gamma = 3, delta = 4, epsilon = 5, zeta = 6, eta = 7, theta = 8
   }
   ```
3. **Aligned grid** — otherwise a pure array of small homogeneous elements (numbers, short strings, booleans, `nil`, or plain names) is printed several cells per row, space-padded and right-aligned within each column so the trailing commas line up across rows: every column starts at a multiple of *widest cell + 2* characters, which keeps the grid vertically aligned even when cell widths differ.
4. **One entry per line** — everything else (any dictionary, mixed arrays, over-wide strings, non-literal elements); nested tables follow the same rules at their own indentation. Multi-line entries carry trailing commas so appending a field never rewrites earlier lines.

Four options tune the `aligned` style (they do not affect the other styles):

| Option | Default | Effect |
| --- | --- | --- |
| `--table-align-width` | follows `--max-line-length` (100 by default) | Caps the rendered row width (including indentation) of every aligned-table row: grid rows, the flat one-liner and the packed content line. Rows never exceed it unless a single cell alone is wider. |
| `--table-align-string-width` | 16 | Caps the rendered width (quotes included) of a string allowed inside a grid; a wider string disqualifies the whole table from grid mode (falls back to one entry per line). |
| `--table-align-eq` | true | Aligns record keys by `=` in non-single-line tables: keys are padded to the widest key of their alignment run. `--table-align-eq=false` keeps single spaces around `=`. |
| `--table-align-eq-max-spaces` | 8 | Caps the total spaces between a record key and `=` (padding plus the mandatory separator): a key whose gap would exceed the cap starts a new alignment run instead of stretching every row. |
| `--table-drop-index-keys` | false | Rewrites contiguous explicit `[1]..[n]` constructor keys as positional array entries (see below). |

What the options change, concretely:

```lua
-- default: --table-align-eq aligns keys to the widest key of the run
local config = {
    name    = "unluac",
    threads = 4,
    paths   = { "/usr/share/lua/5.1/?.lua", "/usr/local/share/lua/5.1/?.lua" },
    retries = 3,
}
-- --table-align-eq=false: same table, no padding
--     name = "unluac",
--     threads = 4,

-- --table-align-eq-max-spaces=2: same table; the visible gap between a key
-- and `=` never exceeds 2 spaces, so only keys one padding space apart stay
-- aligned and every wider key starts a new alignment run
--     id  = "op",
--     tag = "v1",
--     kind = "select",
--     timeout_ms = 1500,
--     retries = 4,
--     label = "worker",
--     retries_budget = 9,
--     fallback_mode  = true,

-- --table-align-width (default: follows --max-line-length, 100 here) vs 40:
-- mixed one- and two-digit numbers make the alignment visible - cells are
-- right-aligned within their column, so every trailing comma lands on the
-- same column across all rows
local values = {
     7, 42,  5, 91,  3, 28, 64, 12, 80, 56,  9, 47, 31, 75,  2, 60,
    38, 84, 15, 70, 26, 93, 58, 41,  6, 77, 19, 85, 32, 68, 24, 50,
}
-- --table-align-width=40: same table, 8 cells per row
-- local values = {
--      7, 42,  5, 91,  3, 28, 64, 12,
--     80, 56,  9, 47, 31, 75,  2, 60,
--     38, 84, 15, 70, 26, 93, 58, 41,
--      6, 77, 19, 85, 32, 68, 24, 50,
-- }

-- --table-align-string-width=6: strings of different lengths; every rendered
-- width (quotes included) is wider than 6, so the whole table falls back to
-- one entry per line - with the default cap of 16 the grid stays
local labels = {
    "peninsula",   "archipelago", "mountains",   "waterfall",
    "wilderness",  "undergrowth", "tableland",   "watershed",
}
-- --table-align-string-width=6: same table, no grid
-- local labels = {
--     "peninsula",
--     "archipelago",
--     "mountains",
--     "waterfall",
--     "wilderness",
--     "undergrowth",
--     "tableland",
--     "watershed",
-- }

-- --table-drop-index-keys=true: contiguous explicit index keys become positional
-- entries; a plain array literal compiles to SETLIST ops without keys, so any
-- `[1] =` in the output mirrors an explicitly keyed source. The rewrite preserves
-- evaluation order and per-field side effects; only the unspecified pairs() order
-- changes (hash part becomes the array part). Gaps, descending keys and tables
-- that mix positional and keyed fields are left untouched.
local keyed = { "alpha", "beta" }        -- was: { [1] = "alpha", [2] = "beta" }
local mixed = { mode = "dlg", "alpha", "beta", tag = 3 }
                                         -- was: { mode = "dlg", [1] = "alpha", [2] = "beta", tag = 3 }
local untouched = { [1] = "alpha", [3] = "gamma" }   -- gap: kept as-is
```

See `unluac-cli --help` for all formatting, naming and decoding options, and the [debugging guide](./docs/debug.md) for pipeline inspection.

### Rust

```bash
cargo add unluac
```

The library accepts bytes of a compiled chunk; default options detect the dialect and run through source generation.

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

See the [Rust API documentation](https://docs.rs/unluac) for options and pipeline results.

### JavaScript / TypeScript

```bash
npm install unluac-js
```

In Node.js, the package initializes its bundled WebAssembly module automatically:

```js
import { readFile } from "node:fs/promises";
import { decompile } from "unluac-js";

const bytes = await readFile("sample.luac");
const source = await decompile(bytes, { dialect: "auto" });
console.log(source);
```

The package also provides `detectDialect()`, `decompileRich()`, `init()` and `supportedOptionValues()`. See the [JavaScript guide](./packages/unluac-js/README.md) for browser bundling, explicit WASM initialization and Luau vector constructor options. Debug dumps and timing are available through the CLI and Rust library.

For custom bindings, start with [the WebAssembly package](./packages/unluac-wasm); JavaScript users should normally use `unluac-js`.

## Contributing and Feedback

The project is still in a testing phase. Behavior, APIs and output details may evolve. Bug reports, difficult bytecode samples, compatibility findings and suggestions about the tools or releases are very welcome.

If a file fails to decompile or the result behaves differently, please [open an issue](https://github.com/x3zvawq/unluac-rs/issues) with a reproducible sample, its Lua dialect, the options used, and the expected versus actual behavior. Include the original source when available. Real-world samples help improve both semantic correctness and output quality; decompilation cannot recover comments or information that compilation discarded.

Code, documentation and regression tests are all welcome. For development, start with the [architecture guide](./docs/design.md), [test protocol](./docs/design/11.test.md) and [web development guide](./packages/unluac-web/README.md).

## License

Released under the [MIT License](./LICENSE.txt).

## Acknowledgements

- [metaworms’s Lua decompiler](https://luadec.metaworm.site) and the author’s tutorial inspired the project’s design and implementation.
- Most of this project’s code was developed with **ChatGPT + Codex**. A special shout-out to **Astra** for its work on the decompiler and its extensive refactoring — seriously impressive. **Claude** also contributed during an earlier stage of development.
- Thanks to everyone sharing test cases, reporting bugs and helping make recovered Lua more readable.
