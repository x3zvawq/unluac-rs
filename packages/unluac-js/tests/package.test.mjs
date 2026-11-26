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
writeFileSync(
  source,
  'local function greet(who)\n  return "hello " .. who\nend\nprint("package API", greet("world"), 42)\n'
);
execFileSync(path.join(tools, `luac${suffix}`), ['-o', chunk, source]);
const bytes = readFileSync(chunk);

for (const [format, api] of [['esm', esm], ['cjs', cjs]]) {
  test(`${format} package loads its own WASM and exposes detection/decompilation`, async () => {
    assert.equal(await api.detectDialect(bytes), 'lua5.4');
    assert.equal(await api.detectDialect(new TextEncoder().encode('print(42)')), null);

    const supported = await api.supportedOptionValues();
    assert.deepEqual(supported.presets, ['readable', 'exact', 'ai']);
    assert.deepEqual(supported.tableAlignCells, ['auto', 'left', 'right']);
    assert.deepEqual(supported.commentStyles, ['none', 'minimal', 'full']);

    const meta = await api.decompileWithMeta(bytes, {
      preset: 'readable',
      generate: { comment: 'minimal', tableStyle: 'aligned', tableAlignCells: 'auto' },
    });
    assert.equal(meta.dialect, 'lua5.4');
    assert.equal(meta.kind, 'source');
    assert.equal(meta.protoCount, 2);
    assert.deepEqual(meta.failedProtos, []);

    const protoOnly = await api.decompile(bytes, { proto: 1, preset: 'ai' });
    assert.match(protoOnly, /function greet\(who\)/);

    const rich = await api.decompileRich(bytes);
    assert.equal(rich.dialect, 'lua5.4');
    assert.equal(rich.kind, 'source');
    assert.deepEqual(rich.failedProtos, []);
    assert.equal(rich.protos.length, 2);
    assert.equal(rich.protos[1].name, 'greet');
    assert.ok(
      typeof rich.protos[1].generatedLineStart === 'number' &&
        rich.protos[1].generatedLineStart >= 1
    );
    assert.ok(
      typeof rich.protos[1].generatedLineEnd === 'number' &&
        rich.protos[1].generatedLineEnd >= rich.protos[1].generatedLineStart
    );

    // Non-plain-object options (e.g. array) and invalid enums throw UnluacError
    await assert.rejects(
      () => api.decompile(bytes, []),
      (err) => err instanceof api.UnluacError && err.code === 'invalid-options'
    );
    await assert.rejects(
      () => api.decompile(bytes, { dialect: 'lua9.9' }),
      (err) =>
        err instanceof api.UnluacError &&
        err.code === 'invalid-enum-value' &&
        err.field === 'dialect'
    );

    const generated = path.join(out, `${format}.lua`);
    writeFileSync(generated, await api.decompile(bytes));
    assert.deepEqual(
      execFileSync(path.join(tools, `lua${suffix}`), [generated]),
      execFileSync(path.join(tools, `lua${suffix}`), [source])
    );
  });
}
