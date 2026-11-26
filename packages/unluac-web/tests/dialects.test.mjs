import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import path from 'node:path'
import { test } from 'node:test'
import { fileURLToPath } from 'node:url'
import init, { decompile, decompileRich, detectDialect } from '../src/wasm/unluac_wasm.js'

const root = fileURLToPath(new URL('../../../', import.meta.url))
const out = path.join(root, 'tmp/web-closeout/dialects')
await init({ module_or_path: readFileSync(new URL('../src/wasm/unluac_wasm_bg.wasm', import.meta.url)) })
const suffix = process.platform === 'win32' ? '.exe' : ''

// Compiled Lua 5.1 chunk for: `local a = 6\nreturn a * 7\n` (stripped)
// Keeps real WASM decompilation verified even in CI environments without `lua/build/`.
const EMBEDDED_LUA51_CHUNK = new Uint8Array([
  27, 76, 117, 97, 81, 0, 1, 4, 8, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  2, 2, 4, 0, 0, 0, 1, 0, 0, 0, 78, 64, 64, 0, 94, 0, 0, 1, 30, 0, 128, 0, 2, 0, 0, 0, 3, 0, 0, 0,
  0, 0, 0, 24, 64, 3, 0, 0, 0, 0, 0, 0, 28, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
])

test('embedded lua5.1 chunk is detected and decompiled through the actual WASM without external toolchains', () => {
  assert.equal(detectDialect(EMBEDDED_LUA51_CHUNK), 'lua5.1')
  const source = decompile(EMBEDDED_LUA51_CHUNK, { dialect: 'lua5.1' })
  assert.match(source, /return\s+6\s*\*\s*7|return\s+\w+\s*\*\s*7/)

  const rich = decompileRich(EMBEDDED_LUA51_CHUNK, { dialect: 'lua5.1' })
  assert.equal(rich.dialect, 'lua5.1')
  assert.equal(rich.kind, 'source')
  assert.ok(Array.isArray(rich.protos) && rich.protos.length >= 1)
  assert.ok(Number.isInteger(rich.protos[0].generatedLineStart) && rich.protos[0].generatedLineStart >= 1)
})

function dialectToolchainPaths(dialect) {
  const tool = path.join(root, 'lua/build', dialect)
  if (dialect === 'luau') {
    return {
      tool,
      compiler: path.join(tool, `luau-compile${suffix}`),
      runtime: path.join(tool, `luau${suffix}`),
    }
  }
  if (dialect === 'luajit') {
    const runtime = path.join(tool, `luajit${suffix}`)
    return { tool, compiler: runtime, runtime }
  }
  return {
    tool,
    compiler: path.join(tool, `luac${suffix}`),
    runtime: path.join(tool, `lua${suffix}`),
  }
}

for (const dialect of ['lua5.1', 'lua5.2', 'lua5.3', 'lua5.4', 'lua5.5', 'luajit', 'luau']) {
  const { tool, compiler, runtime } = dialectToolchainPaths(dialect)
  const hasToolchain = existsSync(compiler) && existsSync(runtime)

  test(
    `official ${dialect} input is detected and decompiled through the actual WASM`,
    { skip: hasToolchain ? false : `local toolchain not built under lua/build/${dialect}` },
    () => {
      mkdirSync(out, { recursive: true })
      const source = path.join(out, 'input.lua')
      writeFileSync(source, 'local a = 6\nprint("web-dialect", a * 7)\n')
      const bytecode = path.join(out, `${dialect}.luac`)
      if (dialect === 'luau') {
        writeFileSync(bytecode, execFileSync(compiler, ['--binary', source]))
      } else if (dialect === 'luajit') {
        execFileSync(runtime, ['-b', source, bytecode], {
          env: {
            ...process.env,
            LUA_PATH: `${tool}/?.lua;${tool}/?/init.lua;${tool}/jit/?.lua;${tool}/jit/?/init.lua`,
          },
        })
      } else {
        execFileSync(compiler, ['-o', bytecode, source])
      }
      const bytes = readFileSync(bytecode)
      assert.equal(detectDialect(bytes), dialect)
      const generated = path.join(out, `${dialect}.lua`)
      writeFileSync(generated, decompile(bytes, { dialect }))
      assert.equal(
        execFileSync(runtime, [generated], { encoding: 'utf8' }),
        execFileSync(runtime, [source], { encoding: 'utf8' }),
      )
      assert.throws(() => decompile(bytes.subarray(0, Math.min(bytes.length - 1, 12)), { dialect }))
    },
  )
}

test('ordinary text is source, but a truncated recognized header remains an error', () => {
  assert.equal(detectDialect(new TextEncoder().encode('print("hello")')), null)
  assert.throws(() => detectDialect(new Uint8Array([27, 76, 117, 97])))
})
