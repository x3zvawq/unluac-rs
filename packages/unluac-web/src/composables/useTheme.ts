/**
 * 主题管理 composable。
 *
 * 负责深色/浅色/跟随系统三种模式的切换和持久化。
 * 实际生效的主题（resolved）由模式 + 系统偏好推导而来。
 * Naive UI 的 theme 对象由 App.vue 通过此 composable 的 isDark 决定。
 */

import { computed, shallowRef, watchEffect } from 'vue'
import type { ThemeMode } from '@/types/theme'

const STORAGE_KEY = 'unluac-theme'

function loadMode(): ThemeMode {
  try {
    const saved = localStorage.getItem(STORAGE_KEY)
    if (saved === 'light' || saved === 'dark' || saved === 'system') return saved
  } catch {
    // ignore
  }
  return 'system'
}

const mode = shallowRef<ThemeMode>(loadMode())
const systemDark = shallowRef(window.matchMedia('(prefers-color-scheme: dark)').matches)

// 监听系统级主题变化
const mql = window.matchMedia('(prefers-color-scheme: dark)')
function onSystemChange(e: MediaQueryListEvent) {
  systemDark.value = e.matches
}
mql.addEventListener('change', onSystemChange)

const isDark = computed(() => {
  if (mode.value === 'system') return systemDark.value
  return mode.value === 'dark'
})

export function useTheme() {
  // 同步 <html> class 以便 Tailwind dark mode 生效
  watchEffect(() => {
    document.documentElement.classList.toggle('dark', isDark.value)
    try {
      localStorage.setItem(STORAGE_KEY, mode.value)
    } catch {
      // ignore
    }
  })

  function setMode(newMode: ThemeMode) {
    mode.value = newMode
  }

  function toggleTheme() {
    if (mode.value === 'system') {
      mode.value = isDark.value ? 'light' : 'dark'
    } else {
      mode.value = mode.value === 'dark' ? 'light' : 'dark'
    }
  }

  return {
    mode,
    isDark,
    setMode,
    toggleTheme,
  }
}
