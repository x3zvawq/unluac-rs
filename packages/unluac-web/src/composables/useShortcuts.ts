/**
 * 全局键盘快捷键 composable。
 *
 * 注册 Ctrl/Cmd+O（打开文件）、Ctrl/Cmd+S（下载当前结果）、Ctrl/Cmd+,（打开设置）。
 * 通过回调方式通知调用者，不直接操作 DOM 或 store，保持解耦。
 */

import { onMounted, onUnmounted } from 'vue'

export interface UseShortcutsCallbacks {
  openFile: () => void
  downloadCurrent: () => void
  openSettings: () => void
}

export function useShortcuts(callbacks: UseShortcutsCallbacks) {
  function handler(e: KeyboardEvent) {
    const mod = e.metaKey || e.ctrlKey
    if (!mod) return

    // 不要拦截输入框内的快捷键
    const target = e.target as HTMLElement
    if (target.tagName === 'INPUT' || target.tagName === 'TEXTAREA' || target.isContentEditable) {
      return
    }

    switch (e.key) {
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
