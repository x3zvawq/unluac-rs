# unluac-rs

[简体中文](./README_cn.md) | English

> This repository is still in a testing phase, and its behavior, APIs, and output details may continue to evolve. Bug reports, problematic test cases, incompatibility findings, usage feedback, and release-related suggestions are all very welcome.

A multi-dialect Lua decompiler written in Rust.

Published entry points:

- Rust crate [`unluac`](https://crates.io/crates/unluac)
- Standalone CLI binaries on [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases)
- npm package [`unluac-js`](https://www.npmjs.com/package/unluac-js)
- API documentation on [docs.rs](https://docs.rs/unluac)

## Introduction

The project currently supports the following Lua versions and dialects:

- [Lua 5.1](https://www.lua.org/versions.html#5.1)
- [Lua 5.2](https://www.lua.org/versions.html#5.2)
- [Lua 5.3](https://www.lua.org/versions.html#5.3)
- [Lua 5.4](https://www.lua.org/versions.html#5.4)
- [Lua 5.5](https://www.lua.org/versions.html#5.5)
- [LuaJIT 2.1](https://luajit.org/)
- [Luau](https://luau.org/)

It uses control-flow analysis, dominator-tree analysis, and later pipeline normalization passes to eliminate most intermediate variables. For the cases currently tracked in this repository, it can usually reconstruct source code with a close-to-original shape.

The repository is organized roughly like this:

- Root package `unluac`: core decompiler library
- `packages/unluac-cli`: command-line entry point
- `packages/unluac-wasm`: wasm bindings
- `packages/unluac-js`: npm wrapper package
- `xtask`: test orchestration and Lua toolchain helpers

## Usage

The project is currently distributed through these entry points:

1. **CLI**: use the standalone binary from GitHub Releases, or run/build `unluac-cli` from this repository.
2. **Rust library**: add the published crate `unluac` to a Rust project and call the decompilation pipeline directly.
3. **npm package**: install `unluac-js` for Node.js or bundler-based browser environments.
4. **WebAssembly**: use `packages/unluac-wasm` directly when you want to build your own runtime wrapper on top of the wasm layer.

### CLI

The published CLI package in this repository is `unluac-cli`.

Recommended installation paths:

- Download a standalone binary from [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases) and place it on your PATH under a stable name such as `unluac-cli`
- Build and install it from a local checkout:

```bash
cargo install --path packages/unluac-cli
```

- Run it directly from this repository during development:

```bash
cargo run -p unluac-cli -- --help
```

If you are working inside this repository, `.cargo/config.toml` still provides `cargo unluac -- ...` as a local alias, but the documented CLI name is `unluac-cli` because that matches the published package.

Typical usage:

```bash
unluac-cli -i /absolute/path/to/chunk.out -D lua5.1
unluac-cli -s tests/lua_cases/lua5.1/01_setfenv.lua -D lua5.1
unluac-cli -i /absolute/path/to/chunk.out -D lua5.1 -o /tmp/case.lua
```

Notes:

- The CLI requires either `-i/--input` or `-s/--source`
- When `-s/--source` is provided, the CLI first invokes an external compiler to produce a chunk, then decompiles that generated chunk
- Standalone GitHub Release binaries do not bundle a Lua compiler; `-s/--source` only works when you pass `-l/--luac` explicitly, or when a compatible compiler is available under `lua/build/<dialect>/` or on PATH
- When `-o/--output` is provided, the CLI writes the final generated source to the target file instead of stdout
- `-o/--output` only works for pure final-source runs and cannot be combined with debug / timing flags or `--stop-after` earlier than `generate`
- The CLI prints plain generated source by default and does not emit debug dumps unless you explicitly request them
- `unluac-cli --help` and `unluac-cli --version` both include the repository link
- CLI defaults come from the core library's `DecompileOptions::default()`, with CLI debug output disabled unless you explicitly enable it

Input options:

| Argument | Description | Default |
| - | - | - |
| `-D`, `--dialect` | Dialect used for compilation / decompilation | `lua5.1` |
| `-i`, `--input` | Path to a compiled chunk | None |
| `-s`, `--source` | Path to Lua source; the CLI invokes an external compiler before decompiling | None |
| `-l`, `--luac` | Explicit compiler path used by `--source` | First tries `lua/build/<dialect>/`, otherwise falls back to a compatible compiler on PATH |
| `-e`, `--encoding` | String decoding encoding | `utf-8` |
| `-m`, `--decode-mode` | String decode failure strategy | `strict` |
| `-p`, `--parse-mode` | Strict vs permissive parser mode | `permissive` |

Debug options:

| Argument | Description | Default |
| - | - | - |
| `-d`, `--debug` | Enable debug output using the current target stage as the default dump stage | `false` |
| `--dump` | Dump one or more pipeline stages; repeat to request multiple stages | None |
| `--detail` | Debug output detail level | `normal` when debug is enabled |
| `-c`, `--color` | Debug color mode | `auto` |
| `--proto` | Restrict debug dumps to a specific proto id | None |
| `-t`, `--timing` | Print timing report | `false` |

Readability and naming options:

| Argument | Description | Default |
| - | - | - |
| `--return-inline-max-complexity` | Max inline complexity for returned expressions | `10` |
| `--index-inline-max-complexity` | Max inline complexity for table index expressions | `10` |
| `--args-inline-max-complexity` | Max inline complexity for call arguments | `6` |
| `--access-base-inline-max-complexity` | Max inline complexity for table access bases | `5` |
| `-n`, `--naming-mode` | Naming strategy | `debug-like` |
| `--debug-like-include-function` | Whether debug-like names should include function-shaped names | `true` |

Generate and output options:

| Argument | Description | Default |
| - | - | - |
| `--indent-width` | Generated source indentation width | `4` |
| `--max-line-length` | Preferred maximum line length | `100` |
| `--quote-style` | String quote style | `min-escape` |
| `--table-style` | Table constructor layout style | `balanced` |
| `--conservative-output` | Whether to prefer conservative source generation | `true` |
| `--comment` | Whether to emit generate-stage comments and metadata | `true` |
| `-g`, `--generate-mode` | How to handle syntax not supported by the target dialect | `strict` |
| `--stop-after` | Last pipeline stage to run | `generate` |
| `-o`, `--output` | Write the final generated source to a file instead of stdout | stdout |

Stage-valued options such as `--dump` and `--stop-after` accept:
`parse`, `transform`, `cfg`, `graph-facts`, `dataflow`, `structure-facts`, `hir`, `ast`, `readability`, `naming`, `generate`.

For more debugging examples and CLI workflow details, see [docs/debug.md](./docs/debug.md).

### Rust Library

The published crate name is `unluac`.

For released builds, the recommended setup is the crates.io package:

```toml
[dependencies]
unluac = "1"
```

If you need the latest unreleased changes from `main`, use a `git` dependency instead:

```toml
[dependencies]
unluac = { git = "https://github.com/x3zvawq/unluac-rs" }
```

Minimal example:

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

Things to keep in mind:

- The library API accepts bytes of an already compiled chunk and does not compile Lua source for you
- If all you have is Lua source, the CLI is usually the more convenient entry point
- The main decompiler entry points are re-exported from [src/decompile/mod.rs](./src/decompile/mod.rs)

### npm Package

The published npm package is [`unluac-js`](https://www.npmjs.com/package/unluac-js).

Install it with:

```bash
npm install unluac-js
```

`unluac-js` is a thin TypeScript wrapper around the wasm bindings produced by `packages/unluac-wasm`, with publishable contents narrowed to the built package output.

The published npm wasm build trims out `debug` / `timing` support to keep the package smaller. The CLI and Rust APIs still keep the full debugging surface. The npm-facing `decompile()` API returns the final source string directly instead of exposing intermediate pipeline metadata.

The main public APIs are:

- `init(input?)`
- `decompile(bytes, options?)`
- `supportedOptionValues()`

Minimal Node.js example:

```js
import { decompile } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");
const source = await decompile(chunkBytes, {
  dialect: "lua5.1",
});

console.log(source);
```

For browser usage and more complete package-level examples, see [packages/unluac-js/README.md](./packages/unluac-js/README.md).

### WebAssembly

The wasm binding layer lives at [packages/unluac-wasm](./packages/unluac-wasm).

It uses `wasm-bindgen` and `serde-wasm-bindgen` to expose a JS-friendly object protocol instead of leaking Rust internal layouts across the boundary.

If you only want to use this project from JavaScript or TypeScript, the npm wrapper above is the recommended entry point.
If you need to integrate the wasm layer into another language or runtime, you can:

- Take the built `unluac_wasm.js` and `unluac_wasm_bg.wasm` files from the published npm package
- Or build `packages/unluac-wasm` directly in this repository and prepare language-specific bindings yourself
- Or consume the standalone `unluac_wasm_bg.wasm` asset published alongside GitHub Releases

If you plan to extend the wasm support to a specific language or runtime, PRs are welcome.

## Contributing and Feedback

Contributions of all kinds are welcome, including code, documentation, test cases, and other improvements.
If you run into issues while using the project, or have ideas and suggestions, feel free to open an issue. If the project performs poorly on a specific case, attaching the corresponding binary file is also very helpful for diagnosis.

## License

This project is released under the MIT License. See [LICENSE.txt](./LICENSE.txt) for details.

## Acknowledgements

- [metaworms's lua decompiler](https://luadec.metaworm.site) - This project's design and implementation were inspired by it, and the author's tutorial was also very helpful. The website is no longer accessible today.
- Codex + GPT-5.4 - Most of this project's code was generated with Codex and GPT-5.4. Thanks to OpenAI for building such strong tools.
