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

const result = await decompile(chunkBytes, {
  dialect: "lua5.1",
  targetStage: "generate",
});

console.log(result.generatedSource);
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

const result = await decompile(chunkBytes, {
  dialect: "luau",
  targetStage: "generate",
});

console.log(result.generatedSource);
```

如果你需要显式指定 wasm 文件位置，也可以传入 URL：

```ts
import { init, decompile } from "unluac-js";

await init(new URL("./unluac_wasm_bg.wasm", import.meta.url));

const result = await decompile(chunkBytes, {
  dialect: "lua5.4",
});
```
