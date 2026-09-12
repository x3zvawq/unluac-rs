/** Worker 请求身份由这里签发，文件身份只用于归属和取消，不参与响应匹配。 */
import { onUnmounted, shallowRef } from 'vue'
import type {
  DecompileOptions,
  WorkerRequest,
  WorkerResponse,
  WorkerResults,
} from '@/types/decompiler'

type Pending = {
  fileId: string
  resolve: (value: WorkerResults[keyof WorkerResults]) => void
  reject: (error: Error) => void
  dispose: () => void
}

export function useDecompiler() {
  const ready = shallowRef(false)
  let worker: Worker | null = null
  let nextRequestId = 0
  const pending = new Map<number, Pending>()

  function rejectRequest(id: number, message: string) {
    const request = pending.get(id)
    if (!request) return
    pending.delete(id)
    request.dispose()
    request.reject(new Error(message))
  }

  function terminate(message = 'Worker terminated') {
    worker?.terminate()
    worker = null
    ready.value = false
    for (const id of pending.keys()) rejectRequest(id, message)
  }

  function ensureWorker(): Worker {
    if (worker) return worker
    const current = new Worker(new URL('@/workers/decompile.worker.ts', import.meta.url), {
      type: 'module',
    })
    worker = current
    current.onmessage = ({ data: msg }: MessageEvent<WorkerResponse>) => {
      if (worker !== current) return
      if (msg.type === 'ready') {
        ready.value = true
      } else if (msg.type === 'error') {
        rejectRequest(msg.requestId, msg.message)
      } else {
        const request = pending.get(msg.requestId)
        if (!request) return
        pending.delete(msg.requestId)
        request.dispose()
        request.resolve(msg.value)
      }
    }
    current.onerror = (event) => {
      if (worker === current) terminate(event.message || 'Worker error')
    }
    return current
  }

  function request<K extends keyof WorkerResults>(
    type: K,
    fileId: string,
    bytes: Uint8Array,
    options?: DecompileOptions,
    signal?: AbortSignal,
  ): Promise<WorkerResults[K]> {
    return new Promise((resolve, reject) => {
      if (signal?.aborted) {
        reject(new Error('Cancelled'))
        return
      }
      const requestId = nextRequestId++
      const abort = () => rejectRequest(requestId, 'Cancelled')
      pending.set(requestId, {
        fileId,
        reject,
        resolve: (value) => resolve(value as WorkerResults[K]),
        dispose: () => signal?.removeEventListener('abort', abort),
      })
      signal?.addEventListener('abort', abort, { once: true })
      try {
        // 同步冻结参数，并转移本请求独占的 bytes；调用方保留原始文件。
        const msg: WorkerRequest =
          type === 'detect'
            ? { type, requestId, bytes }
            : { type, requestId, bytes, options: JSON.parse(JSON.stringify(options)) }
        ensureWorker().postMessage(msg, [bytes.buffer])
      } catch (error) {
        rejectRequest(requestId, error instanceof Error ? error.message : String(error))
      }
    })
  }

  function cancel(fileId: string) {
    for (const [id, request] of pending) {
      if (request.fileId === fileId) rejectRequest(id, 'Cancelled')
    }
  }

  onUnmounted(() => terminate())
  // 首页阅读不需要下载 WASM；首个识别/反编译请求才启动 Worker。
  return {
    ready,
    detectDialect: (id: string, bytes: Uint8Array) => request('detect', id, bytes),
    decompile: (id: string, bytes: Uint8Array, options: DecompileOptions) =>
      request('decompile', id, bytes, options),
    decompileRich: (
      id: string,
      bytes: Uint8Array,
      options: DecompileOptions,
      signal?: AbortSignal,
    ) => request('decompile-rich', id, bytes, options, signal),
    cancel,
    cancelAll: () => terminate('Cancelled'),
    terminate,
  }
}
