# unluac-js

`unluac-js` 是 [unluac-rs](https://github.com/X3ZvaWQ/unluac-rs) 的 npm 包装。

它会消费 `unluac-wasm` 产出的构建结果，并对外提供适合 JavaScript /
TypeScript 环境的发布入口与包装 API。

## 安装

```bash
npm install unluac-js
```

## Node.js 使用

在 Node.js 里，默认初始化逻辑会自动从包目录读取 wasm 文件，所以通常不需要手动传 wasm 路径。

```js
import { decompile, supportedOptionValues } from "unluac-js";
import { readFile } from "node:fs/promises";

const chunkBytes = await readFile("./sample.luac");

const values = await supportedOptionValues();
console.log(values.dialects);

const source = await decompile(chunkBytes, {
  dialect: "lua5.1"
});

console.log(source);
```

如果你想更早完成初始化，也可以手动先调用：

```js
import { init } from "unluac-js";

await init();
```

## 浏览器使用

在浏览器里，推荐通过现代打包器使用这个包，并确保 `unluac_wasm.js` 和
`unluac_wasm_bg.wasm` 会随构建一起输出。

如果你的打包器能正确处理包内的相对资源路径，直接调用 `init()` 即可：

```ts
import { decompile, init } from "unluac-js";

await init();

const source = await decompile(chunkBytes, {
  dialect: "luau",
});

console.log(source);
```

如果你需要显式指定 wasm 文件位置，也可以传入 URL：

```ts
import { init, decompile } from "unluac-js";

await init(new URL("./unluac_wasm_bg.wasm", import.meta.url));

const source = await decompile(chunkBytes, {
  dialect: "lua5.4",
});

console.log(source);
```

## 参数说明

`decompile(bytes, options?)` 的常用参数如下：

- `dialect`: 目标字节码 dialect，如 `lua5.1`、`lua5.4`、`luajit`、`luau`
- `parse.stringEncoding`: 字符串解码编码，支持 `utf-8` 和 `gbk`
- `parse.stringDecodeMode`: 字符串解码失败策略，支持 `strict` 和 `lossy`
- `naming.mode`: 命名策略，支持 `debug-like`、`simple`、`heuristic`

默认情况下，这个包会直接输出最终源码，并沿用仓库当前默认 preset：

- `parse.mode = permissive`
- `naming.mode = debug-like`
- `naming.debugLikeIncludeFunction = true`

`generate` 子选项：

- `indentWidth`: 缩进宽度
- `maxLineLength`: 软换行参考宽度
- `quoteStyle`: 字符串引号风格
- `tableStyle`: 表构造器布局风格
- `conservativeOutput`: 是否偏向保守输出
- `comment`: 是否输出文件头 / proto 注释，默认 `true`
