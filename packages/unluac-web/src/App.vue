<script setup lang="ts">
import { darkTheme, lightTheme, type GlobalThemeOverrides } from 'naive-ui'
import { computed, provide, shallowRef, useTemplateRef } from 'vue'
import { useI18n } from 'vue-i18n'
import FilePanel from '@/components/layout/FilePanel.vue'
import { useDecompiler } from '@/composables/useDecompiler'
import { useIsMobile } from '@/composables/useMediaQuery'
import { useResizable } from '@/composables/useResizable'
import { useShortcuts } from '@/composables/useShortcuts'
import { useTheme } from '@/composables/useTheme'

const { isDark } = useTheme()
const decompiler = useDecompiler()
const isMobile = useIsMobile()
const showMobileFiles = shallowRef(false)
const filePanel = useTemplateRef('filePanel')
const { t } = useI18n()

provide('decompiler', decompiler)
provide('isMobile', isMobile)

const naiveTheme = computed(() => (isDark.value ? darkTheme : lightTheme))
const themeOverrides = computed<GlobalThemeOverrides>(() => ({
  common: {
    primaryColor: isDark.value ? '#83e8cf' : '#147d69',
    primaryColorHover: isDark.value ? '#a3f1de' : '#106c5b',
    primaryColorPressed: isDark.value ? '#5cd2b5' : '#0d5b4c',
    borderRadius: '8px',
    fontFamily: 'Inter, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif',
    bodyColor: isDark.value ? '#101526' : '#f3f5f9',
    cardColor: isDark.value ? '#191f34' : '#ffffff',
    modalColor: isDark.value ? '#191f34' : '#ffffff',
    popoverColor: isDark.value ? '#191f34' : '#ffffff',
  },
}))

const {
  size: sidebarWidth,
  dragging: sidebarDragging,
  onPointerDown: onSidebarPointerDown,
} = useResizable({
  direction: 'horizontal',
  initialSize: 292,
  minSize: 240,
  maxSize: 600,
  storageKey: 'unluac-sidebar-width',
})

/**
 * 快捷键触发的操作通过 provide/inject 传递给子组件。
 * 子组件注册回调函数，App 层面注册全局快捷键来调用它们。
 */
const shortcutActions = shallowRef<{
  openFile?: () => void
  openFolder?: () => void
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
  <NConfigProvider :theme="naiveTheme" :theme-overrides="themeOverrides" class="h-full">
    <NMessageProvider>
      <NDialogProvider>
        <NNotificationProvider>
          <div class="app-shell" @drop="filePanel?.onDrop($event)" @dragover="filePanel?.handleDragOver($event)" @dragleave="filePanel?.handleDragLeave($event)">
            <AppHeader :files-open="showMobileFiles" @toggle-files="showMobileFiles = !showMobileFiles" />
            <div class="workspace-shell">
              <!-- 桌面端：固定侧边栏 + 拖拽分割条 -->
              <FilePanel ref="filePanel" v-show="!isMobile || showMobileFiles" :style="{ width: isMobile ? '100%' : `${sidebarWidth}px` }" class="shrink-0" @selected="showMobileFiles = false" />
              <div
                v-if="!isMobile"
                class="resize-handle shrink-0 cursor-col-resize"
                :class="{ 'bg-indigo-400/40': sidebarDragging }"
                :style="{ width: '4px' }"
                @pointerdown="onSidebarPointerDown"
              />
              <MainContent v-show="!isMobile || !showMobileFiles" />
            </div>
            <Transition name="drop">
              <div v-if="filePanel?.isDragging" class="drop-overlay">
                <div><i-mdi-tray-arrow-down class="mx-auto mb-4 text-4xl" />{{ t('filePanel.dropHint') }}</div>
              </div>
            </Transition>
          </div>
        </NNotificationProvider>
      </NDialogProvider>
    </NMessageProvider>
  </NConfigProvider>
</template>
