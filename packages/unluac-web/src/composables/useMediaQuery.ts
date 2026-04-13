/**
 * 媒体查询响应式 composable。
 *
 * 返回 shallowRef<boolean>，跟踪给定 CSS 媒体查询的匹配状态。
 * 组件卸载后自动清理事件监听。
 */

import { onUnmounted, shallowRef } from 'vue'

export function useMediaQuery(query: string) {
  const mql = window.matchMedia(query)
  const matches = shallowRef(mql.matches)

  function handler(e: MediaQueryListEvent) {
    matches.value = e.matches
  }

  mql.addEventListener('change', handler)

  onUnmounted(() => {
    mql.removeEventListener('change', handler)
  })

  return matches
}

/** 小于 768px 视为移动端 */
export function useIsMobile() {
  return useMediaQuery('(max-width: 767px)')
}
