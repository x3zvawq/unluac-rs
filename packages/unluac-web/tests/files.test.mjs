import assert from 'node:assert/strict'
import { test } from 'node:test'
import { createPinia, setActivePinia } from 'pinia'
import { useFilesStore } from '../src/stores/files.ts'
import { defaultOptions } from '../src/stores/settings.ts'
import { useFileDecompile } from '../src/composables/useFileDecompile.ts'
import { createCacheKey, getCached, setCache } from '../src/composables/useDecompileCache.ts'
import { WASM_ENGINE_ID } from '../src/wasm/engine-id.ts'

// In-memory IndexedDB with asynchronous request delivery, exercising the actual cache/history APIs.
const databases = new Map()
let holdCacheReads = false
const cacheReads = []
globalThis.localStorage = { getItem: () => null, setItem() {} }
globalThis.indexedDB = { open(name) {
  const request = {}
  queueMicrotask(() => {
    const fresh = !databases.has(name)
    if (fresh) databases.set(name, new Map())
    const stores = databases.get(name)
    const db = {
      objectStoreNames: { contains: (key) => stores.has(key) },
      createObjectStore: (key) => stores.set(key, new Map()),
      transaction: (key) => ({ objectStore() {
        const values = stores.get(key)
        const read = (value) => {
          const req = {}
          const finish = () => { req.result = structuredClone(value); req.onsuccess?.() }
          if (holdCacheReads && name === 'unluac-cache') cacheReads.push(finish)
          else queueMicrotask(finish)
          return req
        }
        return {
          put(value, id = value.id) { values.set(id, structuredClone(value)) },
          get: (id) => read(values.get(id)), getAll: () => read([...values.values()]),
          delete: (id) => values.delete(id), clear: () => values.clear(),
        }
      } }),
    }
    request.result = db
    if (fresh) request.onupgradeneeded?.()
    request.onsuccess()
  })
  return request
} }

function file(id, dialect) {
  return { id, name: `${id}.luac`, relativePath: `${id}.luac`, size: 1, bytes: new Uint8Array([id.charCodeAt(0)]), status: 'pending', dialect, revision: 0 }
}
const turn = () => new Promise((resolve) => setImmediate(resolve))

test('cache key keeps engine/input/option identity and is reused unchanged for writeback', async () => {
  const options = defaultOptions()
  const bytes = new Uint8Array([27, 76, 117, 97])
  const key = await createCacheKey(bytes, options)
  assert.ok(key.startsWith(`${WASM_ENGINE_ID}:`))
  options.dialect = 'lua5.4'
  const other = await createCacheKey(bytes, options)
  assert.notEqual(key, other)
  assert.notEqual(key, await createCacheKey(new Uint8Array([1]), defaultOptions()))
  await setCache(key, 'old options output')
  assert.equal(await getCached(key), 'old options output')
  assert.equal(await getCached(other), undefined)
  assert.equal(await getCached(key.replace(WASM_ENGINE_ID, 'different-engine')), undefined)
})

test('mixed dialects, isolated overrides and history restore keep per-file choices', async () => {
  setActivePinia(createPinia())
  const files = useFilesStore()
  files.addFiles([file('a', 'lua5.1'), file('b', 'lua5.4')])
  const options = defaultOptions()
  options.dialect = 'luau'
  assert.equal(files.beginDecompile('a', options).resultOptions.dialect, 'lua5.1')
  assert.equal(files.beginDecompile('b', options).resultOptions.dialect, 'lua5.4')
  const old = files.files[0].revision
  files.setDialect('a', 'lua5.2')
  files.beginDecompile('a', options)
  assert.equal(files.isCurrent('a', old), false)
  assert.equal(files.files[1].dialect, 'lua5.4')
  await turn()
  setActivePinia(createPinia())
  const restored = await useFilesStore().restoreFromHistory()
  assert.equal(restored.find((f) => f.id === 'a').dialect, 'lua5.2')
  assert.equal(restored.find((f) => f.id === 'b').dialect, 'lua5.4')
})

test('same name and size do not collapse distinct bytecode inputs', () => {
  setActivePinia(createPinia())
  const files = useFilesStore()
  const one = file('a', 'lua5.4')
  const two = { ...file('b', 'lua5.5'), name: one.name, relativePath: one.relativePath }
  files.addFiles([one, two, { ...one, id: 'duplicate' }])
  assert.deepEqual(files.files.map((f) => f.id), ['a', 'b'])
})

test('old detection and pending decompile cannot commit into a new file revision', async () => {
  setActivePinia(createPinia())
  const files = useFilesStore()
  files.addFiles([file('c', 'auto')])
  const detections = []
  const outputs = []
  const jobs = useFileDecompile({
    cancel() {},
    detectDialect: () => new Promise((resolve) => detections.push(resolve)),
    decompile: (_, bytes, options) => new Promise((resolve) => outputs.push({ resolve, options })),
  })
  const first = jobs.decompileFile('c')
  const second = jobs.decompileFile('c')
  detections[0]('lua5.1')
  await first
  assert.equal(files.files[0].dialect, 'auto')
  detections[1]('lua5.4')
  while (!outputs.length) await turn()
  assert.equal(outputs[0].options.dialect, 'lua5.4')
  const third = jobs.decompileFile('c')
  outputs[0].resolve('stale')
  await second
  assert.equal(files.files[0].result, undefined)
  detections[2]('lua5.4')
  while (outputs.length < 2) await turn()
  outputs[1].resolve('current')
  await third
  assert.equal(files.files[0].result, 'current')
})

test('removing a file during cache lookup cannot restart its Worker job', async () => {
  setActivePinia(createPinia())
  const files = useFilesStore()
  files.addFiles([file('d', 'lua5.1')])
  let compiles = 0
  const jobs = useFileDecompile({ cancel() {}, detectDialect: async () => 'lua5.1', decompile: async () => { compiles++; return 'obsolete' } })
  holdCacheReads = true
  const pending = jobs.decompileFile('d')
  while (!cacheReads.length) await turn()
  files.removeFile('d')
  holdCacheReads = false
  cacheReads.shift()()
  await pending
  assert.equal(compiles, 0)
  assert.equal(files.files.length, 0)
})
