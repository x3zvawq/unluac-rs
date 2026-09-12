<script setup lang="ts">
import { computed, inject, type ShallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import logoUrl from '@logo'
import productEnglish from '@/content/product.en.html?raw'
import productChinese from '@/content/product.zh.html?raw'
import { site } from '@/content/site'

const { t, locale } = useI18n()
const productOverview = computed(() => locale.value === 'zh-CN' ? productChinese : productEnglish)
const productLanguage = computed(() => locale.value === 'zh-CN' ? 'zh-CN' : 'en')
const actions = inject<ShallowRef<Record<string, (() => void) | undefined>>>('shortcutActions')!
</script>

<template>
  <div class="welcome-view">
    <div class="welcome-content">
      <div class="welcome-eyebrow"><span /> LUA · LUAJIT · LUAU</div>
      <h1>{{ t('workspace.headline') }}<br /><span>{{ t('workspace.headlineAccent') }}</span></h1>
      <p class="welcome-description">{{ t('workspace.description') }}</p>
      <a class="welcome-repository" :href="site.repository" target="_blank" rel="noopener noreferrer"><i-mdi-github />GitHub <span aria-hidden="true">↗</span></a>
      <div class="welcome-import">
        <img :src="logoUrl" alt="" width="72" height="72" />
        <div class="welcome-import-copy">
          <h2>{{ t('filePanel.dropHint') }}</h2>
          <p>{{ t('workspace.importHint') }}</p>
        </div>
        <div class="welcome-actions">
          <NButton type="primary" size="large" @click="actions.openFile?.()"><template #icon><i-mdi-tray-arrow-up /></template>{{ t('filePanel.openFile') }}</NButton>
          <NButton quaternary @click="actions.openFolder?.()">{{ t('filePanel.openFolder') }}</NButton>
        </div>
      </div>
      <div class="welcome-features">
        <div><i-mdi-shield-check-outline /><h3>{{ t('workspace.local') }}</h3><p>{{ t('workspace.privacy') }}</p></div>
        <div><i-mdi-code-braces /><h3>{{ t('workspace.multiDialect') }}</h3><p>Lua 5.1–5.5 · LuaJIT · Luau</p></div>
        <div><i-mdi-file-tree-outline /><h3>{{ t('workspace.explore') }}</h3><p>{{ t('workspace.exploreHint') }}</p></div>
      </div>
      <div class="welcome-footer"><span>Rust + WebAssembly</span><span>{{ t('workspace.history') }}</span></div>
      <!-- Only repository-owned HTML is rendered here; the same English source is in the initial HTML. -->
      <div :lang="productLanguage" v-html="productOverview" />
    </div>
  </div>
</template>
