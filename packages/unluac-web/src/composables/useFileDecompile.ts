/** 文件结果代次覆盖识别、缓存等待和 Worker 请求；后续分析消费同一参数快照。 */
import { useFilesStore } from '@/stores/files'
import { useSettingsStore } from '@/stores/settings'
import type { UnluacDialect } from '@/types/decompiler'
import { createCacheKey, getCached, setCache } from './useDecompileCache'
import type { useDecompiler } from './useDecompiler'

export function useFileDecompile(decompiler: ReturnType<typeof useDecompiler>) {
  const files = useFilesStore()
  const settings = useSettingsStore()

  async function decompileFile(id: string) {
    decompiler.cancel(id)
    const file = files.beginDecompile(id, settings.options)
    if (!file) return
    const options = file.resultOptions!
    const current = () => files.isCurrent(id, file.revision)
    try {
      const detected = await decompiler.detectDialect(id, new Uint8Array(file.bytes))
      if (!current()) return
      if (detected === null) {
        const encoding = options.parse.stringEncoding
        const text = new TextDecoder(encoding === 'auto' ? 'utf-8' : encoding).decode(file.bytes)
        files.updateFileStatus(id, 'skipped', text)
        return
      }
      if (options.dialect === 'auto') {
        options.dialect = detected
        files.setDialect(id, detected)
      }
      const key = await createCacheKey(file.bytes, options)
      if (!current()) return
      const cached = await getCached(key)
      if (!current()) return
      const source = cached ?? (await decompiler.decompile(id, new Uint8Array(file.bytes), options))
      if (!current()) return
      files.updateFileStatus(id, 'success', source)
      if (cached === undefined) void setCache(key, source)
    } catch (error) {
      if (!current() || (error instanceof Error && error.message === 'Cancelled')) return
      files.updateFileStatus(
        id,
        'error',
        undefined,
        error instanceof Error ? error.message : String(error),
      )
    }
  }

  function changeDialect(id: string, dialect: UnluacDialect) {
    files.setDialect(id, dialect)
    void decompileFile(id)
  }

  return { decompileFile, changeDialect }
}
