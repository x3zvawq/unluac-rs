/**
 * 反编译器 Web Worker 通信 composable。
 *
 * 封装 Worker 的生命周期管理和消息通信，对外提供 decompile() 异步方法。
 * Worker 内部加载 WASM 模块执行反编译，避免阻塞主线程。
 *
 * 设计决策：
 * - 使用单一 Worker 实例而非每次创建新 Worker，节省 WASM 初始化开销
 * - 通过 fileId 关联请求和响应，支持并发请求（虽然实际 Worker 串行执行）
 * - ready 状态暴露给调用方，在 Worker 准备好之前可以排队但不丢弃请求
 * - cancel() 从 pending map 移除并拒绝 Promise，WASM 执行无法中断所以会丢弃结果
 * - cancelAll() 终止 Worker 并重建，适用于设置变更后全量重跑的场景
 */

import { onUnmounted, shallowRef } from 'vue'
import type {
  DecompileOptions,
  RichDecompileResult,
  WorkerRequest,
  WorkerResponse,
} from '@/types/decompiler'

type PendingResolve = {
  resolve: (value: any) => void
  reject: (error: Error) => void
}

export function useDecompiler() {
  const ready = shallowRef(false)

  let worker: Worker | null = null
  const pendingMap = new Map<string, PendingResolve>()

  function ensureWorker(): Worker {
    if (worker) return worker

    worker = new Worker(new URL('@/workers/decompile.worker.ts', import.meta.url), {
      type: 'module',
    })

    worker.onmessage = (e: MessageEvent<WorkerResponse>) => {
      const msg = e.data
      if (msg.type === 'ready') {
        ready.value = true
        return
      }

      const pending = pendingMap.get(msg.fileId)
      if (!pending) return
      pendingMap.delete(msg.fileId)

      if (msg.type === 'result') {
        pending.resolve(msg.source)
      } else if (msg.type === 'rich-result') {
        pending.resolve(msg.rich)
      } else {
        pending.reject(new Error(msg.message))
      }
    }

    worker.onerror = (e) => {
      console.error('[decompiler worker] uncaught error:', e)
      // Worker 级别错误，拒绝所有等待中的请求
      for (const [, pending] of pendingMap) {
        pending.reject(new Error(e.message || 'Worker error'))
      }
      pendingMap.clear()
    }

    return worker
  }

  function decompile(
    fileId: string,
    bytes: Uint8Array,
    options: DecompileOptions,
  ): Promise<string> {
    return new Promise((resolve, reject) => {
      pendingMap.set(fileId, { resolve, reject })

      const w = ensureWorker()
      // options 可能是 reactive 代理，structuredClone 无法克隆代理对象
      const msg: WorkerRequest = {
        type: 'decompile',
        fileId,
        bytes,
        options: toRaw(options),
      }
      w.postMessage(msg, [bytes.buffer])
    })
  }

  function decompileRich(
    fileId: string,
    bytes: Uint8Array,
    options: DecompileOptions,
  ): Promise<RichDecompileResult> {
    return new Promise((resolve, reject) => {
      pendingMap.set(fileId, { resolve, reject })

      const w = ensureWorker()
      const msg: WorkerRequest = {
        type: 'decompile-rich',
        fileId,
        bytes,
        options: JSON.parse(JSON.stringify(options)),
      }
      w.postMessage(msg, [bytes.buffer])
    })
  }

  /** 取消单个文件的反编译。WASM 仍在执行但结果会被丢弃。 */
  function cancel(fileId: string) {
    const pending = pendingMap.get(fileId)
    if (pending) {
      pendingMap.delete(fileId)
      pending.reject(new Error('Cancelled'))
    }
  }

  /** 终止 Worker 取消所有任务，下次 decompile 时自动重建。 */
  function cancelAll() {
    worker?.terminate()
    worker = null
    ready.value = false
    for (const [, pending] of pendingMap) {
      pending.reject(new Error('Cancelled'))
    }
    pendingMap.clear()
    // 预热新 Worker
    ensureWorker()
  }

  function terminate() {
    worker?.terminate()
    worker = null
    ready.value = false
    for (const [, pending] of pendingMap) {
      pending.reject(new Error('Worker terminated'))
    }
    pendingMap.clear()
  }

  onUnmounted(() => {
    terminate()
  })

  // 预热 Worker
  ensureWorker()

  return {
    ready,
    decompile,
    decompileRich,
    cancel,
    cancelAll,
    terminate,
  }
}
