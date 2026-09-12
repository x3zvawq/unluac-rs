<script setup lang="ts">
/**
 * 顶栏组件。
 *
 * 职责：展示 Logo + 项目名，提供语言切换、主题切换和设置入口。
 * 不持有业务状态，通过 composable 和 emit 与外部交互。
 */

import { defineAsyncComponent, inject, type ShallowRef, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import logoUrl from '@logo'
import { useTheme } from '@/composables/useTheme'

const { t, locale } = useI18n()
const { isDark, toggleTheme } = useTheme()

defineProps<{ filesOpen: boolean }>()

const emit = defineEmits<{
  'toggle-files': []
}>()

const isMobile = inject<ShallowRef<boolean>>('isMobile')!

const showSettings = shallowRef(false)
const SettingsDrawer = defineAsyncComponent(() => import('@/components/settings/SettingsDrawer.vue'))

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
  <header class="app-header">
    <a href="https://github.com/x3zvawq/unluac-rs" target="_blank" rel="noopener noreferrer" class="brand" title="GitHub · unluac-rs">
      <img :src="logoUrl" alt="" width="38" height="38" />
      <span class="brand-name">unluac<span>-rs</span></span>
      <span class="brand-description">{{ t('app.subtitle') }}</span>
    </a>
    <div class="header-tools">
      <span class="local-indicator"><span />{{ t('workspace.local') }}</span>
      <NButton v-if="isMobile" quaternary class="mobile-files-button" :aria-label="t('filePanel.title')" :aria-pressed="filesOpen" @click="emit('toggle-files')">
        <template #icon><i-mdi-folder-outline /></template>
        <span class="mobile-files-label">{{ t('filePanel.title') }}</span>
      </NButton>
      <NDropdown trigger="click" :options="languageOptions" @select="handleLanguageSelect">
        <NButton quaternary :aria-label="t('header.language')" :title="t('header.language')"><template #icon><i-mdi-translate /></template></NButton>
      </NDropdown>
      <NButton quaternary :aria-label="isDark ? t('header.theme.light') : t('header.theme.dark')" :title="isDark ? t('header.theme.light') : t('header.theme.dark')" @click="toggleTheme">
        <template #icon><i-mdi-white-balance-sunny v-if="isDark" /><i-mdi-weather-night v-else /></template>
      </NButton>
      <NButton secondary :aria-label="t('header.settings')" @click="showSettings = true">
        <template #icon><i-mdi-tune-variant /></template>
        <span class="settings-label">{{ t('header.settings') }}</span>
      </NButton>
    </div>
    <SettingsDrawer v-if="showSettings" v-model:show="showSettings" />
  </header>
</template>
