/**
 * 全局键盘快捷键 composable。
 *
 * 注册 Ctrl/Cmd+O（打开文件）、Ctrl/Cmd+S（下载当前结果）、
 * Ctrl/Cmd+,（打开设置）、Ctrl/Cmd+Shift+F（跨文件全文搜索）。
 * 通过回调方式通知调用者，不直接操作 DOM 或 store，保持解耦。
 */

import { onMounted, onUnmounted } from 'vue'
import { shouldIgnoreModifierShortcutTarget } from '@/utils/keyboard'

export interface UseShortcutsCallbacks {
  openFile: () => void
  downloadCurrent: () => void
  openSettings: () => void
  openGlobalSearch: () => void
}

export function useShortcuts(callbacks: UseShortcutsCallbacks) {
  function handler(e: KeyboardEvent) {
    const mod = e.metaKey || e.ctrlKey
    if (!mod) return

    // Ctrl/Cmd+Shift+F 类似 IDE 全局搜索，即使焦点在代码编辑器或输入框内也应生效
    if (e.shiftKey && e.key.toLowerCase() === 'f') {
      e.preventDefault()
      callbacks.openGlobalSearch()
      return
    }

    // 不要拦截原生表单输入框内的快捷键；允许在 CodeMirror 代码区触发 Ctrl/Cmd+S/O/,
    if (shouldIgnoreModifierShortcutTarget(e.target)) {
      return
    }

    switch (e.key.toLowerCase()) {
      case 'o':
        e.preventDefault()
        callbacks.openFile()
        break
      case 's':
        e.preventDefault()
        callbacks.downloadCurrent()
        break
      case ',':
        e.preventDefault()
        callbacks.openSettings()
        break
    }
  }

  onMounted(() => {
    document.addEventListener('keydown', handler)
  })

  onUnmounted(() => {
    document.removeEventListener('keydown', handler)
  })
}
