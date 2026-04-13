/**
 * 可拖拽调整面板尺寸的 composable。
 *
 * 用于 App.vue 的左右分栏和 MainContent.vue 的上下分栏。
 * 通过 pointer events 实现拖拽，支持最小尺寸约束和持久化到 localStorage。
 */

import { onUnmounted, shallowRef } from 'vue'

export interface UseResizableOptions {
  /** 方向：水平拖拽改宽度 or 垂直拖拽改高度 */
  direction: 'horizontal' | 'vertical'
  /** 初始尺寸（px） */
  initialSize: number
  /** 最小尺寸（px） */
  minSize?: number
  /** 最大尺寸（px） */
  maxSize?: number
  /** 反向拖拽：向负方向拖动增大尺寸（如底部面板） */
  reverse?: boolean
  /** localStorage 持久化 key，不传则不持久化 */
  storageKey?: string
}

export function useResizable(options: UseResizableOptions) {
  const {
    direction,
    initialSize,
    minSize = 120,
    maxSize = 1200,
    reverse = false,
    storageKey,
  } = options

  const savedSize = storageKey
    ? Number(localStorage.getItem(storageKey)) || initialSize
    : initialSize
  const size = shallowRef(clamp(savedSize, minSize, maxSize))
  const dragging = shallowRef(false)

  let startPos = 0
  let startSize = 0

  function clamp(value: number, min: number, max: number) {
    return Math.max(min, Math.min(max, value))
  }

  function onPointerDown(e: PointerEvent) {
    e.preventDefault()
    dragging.value = true
    startPos = direction === 'horizontal' ? e.clientX : e.clientY
    startSize = size.value
    document.addEventListener('pointermove', onPointerMove)
    document.addEventListener('pointerup', onPointerUp)
    // 拖拽时禁止文本选中
    document.body.style.userSelect = 'none'
    document.body.style.cursor = direction === 'horizontal' ? 'col-resize' : 'row-resize'
  }

  function onPointerMove(e: PointerEvent) {
    const currentPos = direction === 'horizontal' ? e.clientX : e.clientY
    const delta = currentPos - startPos
    size.value = clamp(startSize + (reverse ? -delta : delta), minSize, maxSize)
  }

  function onPointerUp() {
    dragging.value = false
    document.removeEventListener('pointermove', onPointerMove)
    document.removeEventListener('pointerup', onPointerUp)
    document.body.style.userSelect = ''
    document.body.style.cursor = ''
    if (storageKey) {
      localStorage.setItem(storageKey, String(size.value))
    }
  }

  onUnmounted(() => {
    document.removeEventListener('pointermove', onPointerMove)
    document.removeEventListener('pointerup', onPointerUp)
  })

  return { size, dragging, onPointerDown }
}
