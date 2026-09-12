import assert from 'node:assert/strict'
import { test } from 'node:test'
import { useDecompiler } from '../src/composables/useDecompiler.ts'
import { createSSRApp } from 'vue'
import { renderToString } from '@vue/server-renderer'

async function createApi() {
  let api
  await renderToString(createSSRApp({ setup() { api = useDecompiler(); return () => null } }))
  return api
}

class WorkerDouble {
  static instances = []
  constructor() { this.sent = []; WorkerDouble.instances.push(this) }
  postMessage(message) { this.sent.push(structuredClone(message)) }
  terminate() { this.terminated = true }
  reply(index, value) {
    this.onmessage({ data: { type: 'result', requestId: this.sent[index].requestId, value } })
  }
}
globalThis.Worker = WorkerDouble

test('reading the landing page does not start a worker; the first request does', async () => {
  const before = WorkerDouble.instances.length
  const api = await createApi()
  assert.equal(WorkerDouble.instances.length, before)
  const detected = api.detectDialect('first', new Uint8Array([1]))
  assert.equal(WorkerDouble.instances.length, before + 1)
  WorkerDouble.instances.at(-1).reply(0, 'lua5.4')
  assert.equal(await detected, 'lua5.4')
  api.terminate()
})

test('same file, out-of-order source/rich replies preserve every request', async () => {
  const api = await createApi()
  const options = { dialect: 'lua5.1' }
  const source = api.decompile('a', new Uint8Array([1]), options)
  const rich = api.decompileRich('a', new Uint8Array([2]), options)
  options.dialect = 'lua5.4'
  const worker = WorkerDouble.instances.at(-1)
  assert.equal(worker.sent[0].options.dialect, 'lua5.1')
  worker.reply(1, { source: 'rich' })
  worker.reply(0, 'source')
  assert.deepEqual(await Promise.all([source, rich]), ['source', { source: 'rich' }])
  api.terminate()
})

test('cancel/reissue cannot consume an old response; file cancellation rejects all requests', async () => {
  const api = await createApi()
  const one = api.detectDialect('a', new Uint8Array([1]))
  const two = api.decompileRich('a', new Uint8Array([1]), {})
  const cancelled = [assert.rejects(one, /Cancelled/), assert.rejects(two, /Cancelled/)]
  api.cancel('a')
  const fresh = api.detectDialect('a', new Uint8Array([1]))
  const worker = WorkerDouble.instances.at(-1)
  worker.reply(0, 'lua5.1')
  worker.reply(1, { source: 'old' })
  worker.reply(2, 'luau')
  assert.equal(await fresh, 'luau')
  await Promise.all(cancelled)
  api.terminate()
})

test('individual abort and retired workers cannot affect fresh requests', async () => {
  const api = await createApi()
  const controller = new AbortController()
  const old = api.decompileRich('a', new Uint8Array([1]), {}, controller.signal)
  const cancelled = assert.rejects(old, /Cancelled/)
  controller.abort()
  const retired = WorkerDouble.instances.at(-1)
  api.cancelAll()
  const fresh = api.detectDialect('b', new Uint8Array([1]))
  retired.reply(0, { source: 'old' })
  WorkerDouble.instances.at(-1).reply(0, 'lua5.4')
  assert.equal(await fresh, 'lua5.4')
  await cancelled
  api.terminate()
})
