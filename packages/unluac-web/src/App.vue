<script setup lang="ts">
import { darkTheme, lightTheme } from 'naive-ui'
import { computed, provide, shallowRef } from 'vue'
import { useDecompiler } from '@/composables/useDecompiler'
import { useIsMobile } from '@/composables/useMediaQuery'
import { useResizable } from '@/composables/useResizable'
import { useShortcuts } from '@/composables/useShortcuts'
import { useTheme } from '@/composables/useTheme'

const { isDark } = useTheme()
const decompiler = useDecompiler()
const isMobile = useIsMobile()
const showMobileFiles = shallowRef(false)

provide('decompiler', decompiler)
provide('isMobile', isMobile)

const naiveTheme = computed(() => (isDark.value ? darkTheme : lightTheme))

const {
  size: sidebarWidth,
  dragging: sidebarDragging,
  onPointerDown: onSidebarPointerDown,
} = useResizable({
  direction: 'horizontal',
  initialSize: 280,
  minSize: 180,
  maxSize: 600,
  storageKey: 'unluac-sidebar-width',
})

/**
 * 快捷键触发的操作通过 provide/inject 传递给子组件。
 * 子组件注册回调函数，App 层面注册全局快捷键来调用它们。
 */
const shortcutActions = shallowRef<{
  openFile?: () => void
  downloadCurrent?: () => void
  openSettings?: () => void
}>({})

provide('shortcutActions', shortcutActions)

useShortcuts({
  openFile: () => shortcutActions.value.openFile?.(),
  downloadCurrent: () => shortcutActions.value.downloadCurrent?.(),
  openSettings: () => shortcutActions.value.openSettings?.(),
})
</script>

<template>
  <NConfigProvider :theme="naiveTheme" class="h-full">
    <NMessageProvider>
      <NDialogProvider>
        <NNotificationProvider>
          <div class="flex h-full flex-col" style="background: var(--app-bg); color: var(--app-text)">
            <AppHeader @toggle-files="showMobileFiles = !showMobileFiles" />
            <div class="flex min-h-0 flex-1">
              <!-- 桌面端：固定侧边栏 + 拖拽分割条 -->
              <FilePanel v-if="!isMobile" :style="{ width: `${sidebarWidth}px` }" class="shrink-0" />
              <div
                v-if="!isMobile"
                class="shrink-0 cursor-col-resize transition-colors hover:bg-indigo-400/40"
                :class="{ 'bg-indigo-400/40': sidebarDragging }"
                :style="{ width: '4px' }"
                @pointerdown="onSidebarPointerDown"
              />
              <MainContent />
            </div>
            <!-- 移动端：底部抽屉 -->
            <NDrawer
              v-if="isMobile"
              v-model:show="showMobileFiles"
              placement="bottom"
              :height="'60vh'"
            >
              <NDrawerContent title="Files" closable body-content-class="!p-0">
                <FilePanel class="w-full! border-0!" />
              </NDrawerContent>
            </NDrawer>
          </div>
        </NNotificationProvider>
      </NDialogProvider>
    </NMessageProvider>
  </NConfigProvider>
</template>
