import assert from 'node:assert/strict';
import { test } from 'node:test';
import { createRequire } from 'node:module';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import * as esm from '../dist/index.mjs';

const cjs = createRequire(import.meta.url)('../dist/index.cjs');
const root = fileURLToPath(new URL('../../../', import.meta.url));
const out = path.join(root, 'tmp/js-package-test');
mkdirSync(out, { recursive: true });
const source = path.join(out, 'input.lua');
const chunk = path.join(out, 'input.luac');
const suffix = process.platform === 'win32' ? '.exe' : '';
const tools = path.join(root, 'lua/build/lua5.4');
writeFileSync(source, 'print("package API", 42)\n');
execFileSync(path.join(tools, `luac${suffix}`), ['-o', chunk, source]);
const bytes = readFileSync(chunk);

for (const [format, api] of [['esm', esm], ['cjs', cjs]]) {
  test(`${format} package loads its own WASM and exposes detection/decompilation`, async () => {
    assert.equal(await api.detectDialect(bytes), 'lua5.4');
    assert.equal(await api.detectDialect(new TextEncoder().encode('print(42)')), null);
    const generated = path.join(out, `${format}.lua`);
    writeFileSync(generated, await api.decompile(bytes));
    assert.deepEqual(
      execFileSync(path.join(tools, `lua${suffix}`), [generated]),
      execFileSync(path.join(tools, `lua${suffix}`), [source])
    );
  });
}
