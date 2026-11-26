/** 输入识别与反编译都调用同一 WASM；每个响应携带原请求身份。 */
import type { WorkerRequest, WorkerResponse } from '@/types/decompiler'
import initWasm, { decompile, decompileRich, detectDialect } from '@/wasm/unluac_wasm.js'
import wasmUrl from '@/wasm/unluac_wasm_bg.wasm?url'

let initPromise: Promise<unknown> | null = null

function ensureInitialized(): Promise<unknown> {
  if (!initPromise) {
    initPromise = initWasm({ module_or_path: wasmUrl })
      .then((exports) => {
        self.postMessage({ type: 'ready' } satisfies WorkerResponse)
        return exports
      })
      .catch((error) => {
        // 失败时清空缓存 Promise，允许后续请求重新尝试加载 WASM
        initPromise = null
        throw error
      })
  }
  return initPromise
}

function extractErrorMessage(error: unknown): string {
  if (typeof error === 'object' && error !== null && 'message' in error)
    return String(error.message)
  return String(error)
}

self.onmessage = async ({ data: msg }: MessageEvent<WorkerRequest>) => {
  let response: WorkerResponse
  try {
    await ensureInitialized()
    const value =
      msg.type === 'detect'
        ? detectDialect(msg.bytes)
        : msg.type === 'decompile'
          ? decompile(msg.bytes, msg.options)
          : decompileRich(msg.bytes, msg.options)
    response = { type: 'result', requestId: msg.requestId, value }
  } catch (error) {
    response = { type: 'error', requestId: msg.requestId, message: extractErrorMessage(error) }
  }
  self.postMessage(response)
}

// 预热 WASM；失败时静默复位，实际错误在首次请求时返回
ensureInitialized().catch(() => {})
