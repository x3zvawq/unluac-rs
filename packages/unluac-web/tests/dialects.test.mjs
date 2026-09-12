import assert from 'node:assert/strict'
import { test } from 'node:test'
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import path from 'node:path'
import init, { detectDialect, decompile } from '../src/wasm/unluac_wasm.js'

const root = fileURLToPath(new URL('../../../', import.meta.url))
const out = path.join(root, 'tmp/web-closeout/dialects')
mkdirSync(out, { recursive: true })
await init({ module_or_path: readFileSync(new URL('../src/wasm/unluac_wasm_bg.wasm', import.meta.url)) })
const source = path.join(out, 'input.lua')
writeFileSync(source, 'local a = 6\nprint("web-dialect", a * 7)\n')
const suffix = process.platform === 'win32' ? '.exe' : ''

for (const dialect of ['lua5.1', 'lua5.2', 'lua5.3', 'lua5.4', 'lua5.5', 'luajit', 'luau']) {
  test(`official ${dialect} input is detected and decompiled through the actual WASM`, () => {
    const tool = path.join(root, 'lua/build', dialect)
    const bytecode = path.join(out, `${dialect}.luac`)
    let runtime = path.join(tool, `lua${suffix}`)
    if (dialect === 'luau') {
      writeFileSync(bytecode, execFileSync(path.join(tool, `luau-compile${suffix}`), ['--binary', source]))
      runtime = path.join(tool, `luau${suffix}`)
    } else if (dialect === 'luajit') {
      runtime = path.join(tool, `luajit${suffix}`)
      execFileSync(runtime, ['-b', source, bytecode], { env: { ...process.env, LUA_PATH: `${tool}/?.lua;${tool}/?/init.lua;${tool}/jit/?.lua;${tool}/jit/?/init.lua` } })
    } else {
      execFileSync(path.join(tool, `luac${suffix}`), ['-o', bytecode, source])
    }
    const bytes = readFileSync(bytecode)
    assert.equal(detectDialect(bytes), dialect)
    const generated = path.join(out, `${dialect}.lua`)
    writeFileSync(generated, decompile(bytes, { dialect }))
    assert.equal(execFileSync(runtime, [generated], { encoding: 'utf8' }), execFileSync(runtime, [source], { encoding: 'utf8' }))
    assert.throws(() => decompile(bytes.subarray(0, Math.min(bytes.length - 1, 12)), { dialect }))
  })
}

test('ordinary text is source, but a truncated recognized header remains an error', () => {
  assert.equal(detectDialect(new TextEncoder().encode('print("hello")')), null)
  assert.throws(() => detectDialect(new Uint8Array([27, 76, 117, 97])))
})
