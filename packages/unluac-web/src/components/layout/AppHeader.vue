<script setup lang="ts">
/**
 * 顶栏组件。
 *
 * 职责：展示 Logo + 项目名，提供语言切换、主题切换和设置入口。
 * 不持有业务状态，通过 composable 和 emit 与外部交互。
 */

import { inject, type ShallowRef, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import { useTheme } from '@/composables/useTheme'

const { t, locale } = useI18n()
const { isDark, toggleTheme } = useTheme()

const emit = defineEmits<{
  'toggle-files': []
}>()

const isMobile = inject<ShallowRef<boolean>>('isMobile')!

const showSettings = shallowRef(false)

// 注册快捷键回调
const shortcutActions =
  inject<ShallowRef<Record<string, (() => void) | undefined>>>('shortcutActions')!
shortcutActions.value = {
  ...shortcutActions.value,
  openSettings: () => {
    showSettings.value = true
  },
}

const languageOptions = [
  { label: '简体中文', key: 'zh-CN' },
  { label: '繁體中文', key: 'zh-TW' },
  { label: 'English', key: 'en-US' },
  { label: '한국어', key: 'ko-KR' },
  { label: 'Русский', key: 'ru-RU' },
  { label: 'Español', key: 'es-ES' },
  { label: 'Português', key: 'pt-BR' },
  { label: 'Français', key: 'fr-FR' },
  { label: 'Deutsch', key: 'de-DE' },
  { label: '日本語', key: 'ja-JP' },
]

function handleLanguageSelect(key: string) {
  locale.value = key
  try {
    localStorage.setItem('unluac-locale', key)
  } catch {
    // ignore
  }
}
</script>

<template>
  <header
    class="flex h-12 shrink-0 items-center px-4"
    style="border-bottom: 1px solid var(--app-border)"
  >
    <!-- Logo + 项目名（点击跳转 GitHub） -->
    <a
      href="https://github.com/x3zvawq/unluac-rs"
      target="_blank"
      rel="noopener noreferrer"
      class="flex items-center gap-2 text-inherit no-underline hover:opacity-80"
    >
      <div
        class="flex h-7 w-7 items-center justify-center rounded bg-indigo-600 text-xs font-bold text-white"
      >
        U
      </div>
      <span class="text-base font-semibold">unluac-rs web</span>
      <span class="hidden text-xs sm:inline" style="color: var(--app-text-secondary)">
        {{ t('app.subtitle') }}
      </span>
    </a>

    <div class="flex-1" />

    <!-- 移动端文件列表切换 -->
    <NButton v-if="isMobile" quaternary size="small" class="mr-1" @click="emit('toggle-files')">
      <template #icon>
        <NIcon>
          <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M13 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V9z"/><polyline points="13 2 13 9 20 9"/></svg>
        </NIcon>
      </template>
    </NButton>

    <!-- 语言切换 -->
    <NDropdown :options="languageOptions" @select="handleLanguageSelect">
      <NButton quaternary size="small" class="mr-1">
        <template #icon>
          <NIcon>
            <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M2 12h20"/><path d="M12 2a15.3 15.3 0 0 1 4 10 15.3 15.3 0 0 1-4 10 15.3 15.3 0 0 1-4-10 15.3 15.3 0 0 1 4-10z"/></svg>
          </NIcon>
        </template>
      </NButton>
    </NDropdown>

    <!-- 主题切换 -->
    <NTooltip>
      <template #trigger>
        <NButton quaternary size="small" class="mr-1" @click="toggleTheme">
          <template #icon>
            <NIcon>
              <!-- 太阳/月亮图标 -->
              <svg v-if="isDark" xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="5"/><line x1="12" y1="1" x2="12" y2="3"/><line x1="12" y1="21" x2="12" y2="23"/><line x1="4.22" y1="4.22" x2="5.64" y2="5.64"/><line x1="18.36" y1="18.36" x2="19.78" y2="19.78"/><line x1="1" y1="12" x2="3" y2="12"/><line x1="21" y1="12" x2="23" y2="12"/><line x1="4.22" y1="19.78" x2="5.64" y2="18.36"/><line x1="18.36" y1="5.64" x2="19.78" y2="4.22"/></svg>
              <svg v-else xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 12.79A9 9 0 1 1 11.21 3 7 7 0 0 0 21 12.79z"/></svg>
            </NIcon>
          </template>
        </NButton>
      </template>
      {{ isDark ? t('header.theme.light') : t('header.theme.dark') }}
    </NTooltip>

    <!-- 设置 -->
    <NTooltip>
      <template #trigger>
        <NButton quaternary size="small" @click="showSettings = true">
          <template #icon>
            <NIcon>
              <svg xmlns="http://www.w3.org/2000/svg" width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1 0 2.83 2 2 0 0 1-2.83 0l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-2 2 2 2 0 0 1-2-2v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83 0 2 2 0 0 1 0-2.83l.06-.06A1.65 1.65 0 0 0 4.68 15a1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1-2-2 2 2 0 0 1 2-2h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 0-2.83 2 2 0 0 1 2.83 0l.06.06A1.65 1.65 0 0 0 9 4.68a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 2-2 2 2 0 0 1 2 2v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 0 2 2 0 0 1 0 2.83l-.06.06A1.65 1.65 0 0 0 19.4 9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 2 2 2 2 0 0 1-2 2h-.09a1.65 1.65 0 0 0-1.51 1z"/></svg>
            </NIcon>
          </template>
        </NButton>
      </template>
      {{ t('header.settings') }}
    </NTooltip>

    <SettingsDrawer v-model:show="showSettings" />
  </header>
</template>
