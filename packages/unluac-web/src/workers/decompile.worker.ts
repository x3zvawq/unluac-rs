/**
 * 反编译 Web Worker。
 *
 * 在独立线程中加载 WASM 模块并执行反编译，避免阻塞主线程。
 * 通过 postMessage 与主线程通信，协议见 types/decompiler.ts。
 *
 * 直接导入 wasm-bindgen 生成的 glue code（src/wasm/ 下的 vendor 文件），
 * Vite 会识别 glue code 中的 `new URL(..., import.meta.url)` 并自动处理 WASM 文件。
 */

import type { WorkerRequest, WorkerResponse } from '@/types/decompiler'
import initWasm, {
  decompile as wasmDecompile,
  decompileRich as wasmDecompileRich,
} from '@/wasm/unluac_wasm.js'
import wasmUrl from '@/wasm/unluac_wasm_bg.wasm?url'

let initialized = false

async function ensureInit() {
  if (initialized) return
  await initWasm({ module_or_path: wasmUrl })
  initialized = true
}

/**
 * WASM 通过 serde_wasm_bindgen 抛出的错误是 {code, message, field} 纯对象，
 * 不是 Error 实例，String(obj) 只会得到 "[object Object]"。
 */
function extractErrorMessage(err: unknown): string {
  if (err instanceof Error) return err.message
  if (typeof err === 'object' && err !== null && 'message' in err) {
    return String((err as { message: unknown }).message)
  }
  return String(err)
}

self.onmessage = async (e: MessageEvent<WorkerRequest>) => {
  const msg = e.data

  if (msg.type === 'decompile') {
    try {
      await ensureInit()

      const source = wasmDecompile(msg.bytes, msg.options)

      const response: WorkerResponse = { type: 'result', fileId: msg.fileId, source }
      self.postMessage(response)
    } catch (err) {
      console.error('[decompile worker] decompile failed:', err)
      const response: WorkerResponse = {
        type: 'error',
        fileId: msg.fileId,
        message: extractErrorMessage(err),
      }
      self.postMessage(response)
    }
  } else if (msg.type === 'decompile-rich') {
    try {
      await ensureInit()

      const rich = wasmDecompileRich(msg.bytes, msg.options)

      const response: WorkerResponse = { type: 'rich-result', fileId: msg.fileId, rich }
      self.postMessage(response)
    } catch (err) {
      console.error('[decompile worker] decompileRich failed:', err)
      const response: WorkerResponse = {
        type: 'error',
        fileId: msg.fileId,
        message: extractErrorMessage(err),
      }
      self.postMessage(response)
    }
  }
}

// 通知主线程 Worker 已就绪
const readyMsg: WorkerResponse = { type: 'ready' }
self.postMessage(readyMsg)
