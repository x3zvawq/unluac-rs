/** 输入识别与反编译都调用同一 WASM；每个响应携带原请求身份。 */
import type { WorkerRequest, WorkerResponse } from '@/types/decompiler'
import initWasm, { detectDialect, decompile, decompileRich } from '@/wasm/unluac_wasm.js'
import wasmUrl from '@/wasm/unluac_wasm_bg.wasm?url'

const initialized = initWasm({ module_or_path: wasmUrl })

function extractErrorMessage(error: unknown): string {
  if (typeof error === 'object' && error !== null && 'message' in error)
    return String(error.message)
  return String(error)
}

self.onmessage = async ({ data: msg }: MessageEvent<WorkerRequest>) => {
  let response: WorkerResponse
  try {
    await initialized
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

// 失败由各请求返回；预热失败不留下未处理的 Promise rejection。
initialized.then(
  () => self.postMessage({ type: 'ready' } satisfies WorkerResponse),
  () => {},
)
