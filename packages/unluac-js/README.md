# unluac-js

`unluac-js` is the published JavaScript / TypeScript wrapper for
[unluac-rs](https://github.com/x3zvawq/unluac-rs).

It consumes the WebAssembly build produced by `packages/unluac-wasm` and
exposes a small JS-friendly API for decompiling Lua bytecode in Node.js and
bundler-based browser environments.

## Installation

```bash
npm install unluac-js
```

Requirements:

- Node.js `>= 18` for Node usage
- A bundler that can emit package-relative wasm assets for browser usage

## What This Package Provides

- `init(input?)`: initialize the wasm module explicitly
- `decompile(bytes, options?)`: decompile a compiled Lua chunk and return the final source string
- `decompileRich(bytes, options?)`: decompile and return structured analysis result (source + proto metadata + CFGs)
- `supportedOptionValues()`: inspect supported enum-like option values

This package ships a slim wasm build for npm. In particular:

- `decompile()` returns the final generated source string directly
- debug dumps and timing reports are not exposed in the published npm build
- if you need the full debug surface, use the Rust crate or `unluac-cli`

## Node.js Usage

In Node.js, the default initialization path automatically reads the packaged
`unluac_wasm_bg.wasm` file, so you usually do not need to pass a wasm path
manually.

```js
import { decompile, supportedOptionValues } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");

const values = await supportedOptionValues();
console.log(values.dialects);

const source = await decompile(chunkBytes, {
  dialect: "lua5.1",
});

console.log(source);
```

If you want to initialize earlier in your startup path, you can also call:

```js
import { init } from "unluac-js";

await init();
```

## Browser Usage

In the browser, the recommended setup is to use this package through a modern
bundler and make sure both `unluac_wasm.js` and `unluac_wasm_bg.wasm` are emitted
as runtime assets.

If your bundler can resolve the package's relative wasm asset automatically,
calling `init()` is enough:

```ts
import { decompile, init } from "unluac-js";

await init();

const source = await decompile(chunkBytes, {
  dialect: "luau",
});

console.log(source);
```

If you need to provide the wasm location explicitly, pass a `URL`:

```ts
import { decompile, init } from "unluac-js";

await init(new URL("./unluac_wasm_bg.wasm", import.meta.url));

const source = await decompile(chunkBytes, {
  dialect: "lua5.4",
});

console.log(source);
```

## API Notes

### `decompile(bytes, options?)`

- `bytes` accepts `BufferSource` or any `ArrayLike<number>`
- the input must already be a compiled chunk; this package does not compile Lua source for you
- the return value is always the final generated source string

### `decompileRich(bytes, options?)`

Returns a structured analysis result instead of a plain source string:

```ts
import { decompileRich } from "unluac-js";

const result = await decompileRich(chunkBytes, { dialect: "lua5.1" });

console.log(result.source);    // final Lua source
console.log(result.warnings);  // generation warnings
console.log(result.protos);    // proto metadata (DFS order)
console.log(result.cfgs);      // per-proto CFG with blocks and edges
```

The result includes:

- `source`: generated Lua source string
- `warnings`: array of generation-stage warnings
- `protos`: array of `UnluacProtoMeta` with function metadata (name, line range, params, upvalues, constants, instructions, children)
- `cfgs`: array of `UnluacProtoCfg` with control flow graph data (blocks with Low-IR and raw bytecode instructions, edges with type labels)

Supported top-level options:

- `dialect`
- `parse`
- `readability`
- `naming`
- `generate`

Unsupported in the published npm build:

- `debug`
- timing-report style output

### `supportedOptionValues()`

Returns the currently supported enum-like values for:

- `dialects`
- `parseModes`
- `stringEncodings`
- `stringDecodeModes`
- `namingModes`
- `quoteStyles`
- `tableStyles`

## Option Reference

Common `decompile()` options:

- `dialect`: target chunk dialect such as `lua5.1`, `lua5.4`, `luajit`, or `luau`
- `parse.mode`: parser mode, `strict` or `permissive`
- `parse.stringEncoding`: string decoding encoding; accepts any [Encoding Standard](https://encoding.spec.whatwg.org/) label (e.g. `utf-8`, `gbk`, `shift_jis`, `euc-kr`, `big5`)
- `parse.stringDecodeMode`: string decode failure strategy, `strict` or `lossy`
- `naming.mode`: naming strategy, `debug-like`, `simple`, or `heuristic`
- `naming.debugLikeIncludeFunction`: whether debug-like naming should include function-shaped names

`readability` sub-options:

- `returnInlineMaxComplexity`
- `indexInlineMaxComplexity`
- `argsInlineMaxComplexity`
- `accessBaseInlineMaxComplexity`

`generate` sub-options:

- `indentWidth`
- `maxLineLength`
- `quoteStyle`
- `tableStyle`
- `conservativeOutput`
- `comment`

Current library defaults used by this package:

- `parse.mode = permissive`
- `parse.stringEncoding = utf-8`
- `parse.stringDecodeMode = strict`
- `naming.mode = debug-like`
- `naming.debugLikeIncludeFunction = true`
- `generate.indentWidth = 4`
- `generate.maxLineLength = 100`
- `generate.quoteStyle = min-escape`
- `generate.tableStyle = balanced`
- `generate.conservativeOutput = true`
- `generate.comment = true`

## Related Packages

- Root project: [unluac-rs](https://github.com/x3zvawq/unluac-rs)
- Rust crate: [unluac on crates.io](https://crates.io/crates/unluac)
- CLI binaries: [GitHub Releases](https://github.com/x3zvawq/unluac-rs/releases)
