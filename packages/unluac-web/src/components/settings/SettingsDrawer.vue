<script setup lang="ts">
/**
 * 设置面板。
 *
 * 当前将设置收敛为“通用 / 高级 / 关于”三组：
 * - 通用：最常改、最影响输出风格的少量选项；
 * - 高级：保留所有细粒度调参项，避免默认界面过于拥挤；
 * - 关于：补充产品定位、能力边界与项目入口，减少面板信息过干的问题。
 */

import { shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import { generateShareUrl } from '@/composables/useShareUrl'
import { useSettingsStore } from '@/stores/settings'

defineProps<{
  show: boolean
}>()

const emit = defineEmits<{
  'update:show': [value: boolean]
}>()

const { t } = useI18n()
const settings = useSettingsStore()
const copied = shallowRef(false)
const appVersion = __APP_VERSION__

function copyShareUrl() {
  const url = generateShareUrl()
  navigator.clipboard.writeText(url).then(() => {
    copied.value = true
    setTimeout(() => {
      copied.value = false
    }, 2000)
  })
}

const dialectOptions = [
  { label: 'Lua 5.1', value: 'lua5.1' },
  { label: 'Lua 5.2', value: 'lua5.2' },
  { label: 'Lua 5.3', value: 'lua5.3' },
  { label: 'Lua 5.4', value: 'lua5.4' },
  { label: 'Lua 5.5', value: 'lua5.5' },
  { label: 'LuaJIT', value: 'luajit' },
  { label: 'Luau', value: 'luau' },
]

const parseModeOptions = [
  { label: 'strict', value: 'strict' },
  { label: 'permissive', value: 'permissive' },
]

const stringEncodingOptions = [
  { label: 'UTF-8', value: 'utf-8' },
  { label: 'GBK', value: 'gbk' },
  { label: 'GB18030', value: 'gb18030' },
  { label: 'Big5', value: 'big5' },
  { label: 'Shift_JIS', value: 'shift_jis' },
  { label: 'EUC-JP', value: 'euc-jp' },
  { label: 'EUC-KR', value: 'euc-kr' },
  { label: 'Windows-1252', value: 'windows-1252' },
  { label: 'Windows-1251', value: 'windows-1251' },
  { label: 'KOI8-R', value: 'koi8-r' },
  { label: 'Windows-874', value: 'windows-874' },
]

const stringDecodeModeOptions = [
  { label: 'strict', value: 'strict' },
  { label: 'lossy', value: 'lossy' },
]

const namingModeOptions = [
  { label: 'debug-like', value: 'debug-like' },
  { label: 'simple', value: 'simple' },
  { label: 'heuristic', value: 'heuristic' },
]

const generateModeOptions = [
  { label: 'strict', value: 'strict' },
  { label: 'best-effort', value: 'best-effort' },
  { label: 'permissive', value: 'permissive' },
]

const quoteStyleOptions = [
  { label: 'prefer-double', value: 'prefer-double' },
  { label: 'prefer-single', value: 'prefer-single' },
  { label: 'min-escape', value: 'min-escape' },
]

const tableStyleOptions = [
  { label: 'compact', value: 'compact' },
  { label: 'balanced', value: 'balanced' },
  { label: 'expanded', value: 'expanded' },
]
</script>

<template>
  <NDrawer :show="show" :width="400" placement="right" @update:show="emit('update:show', $event)">
    <NDrawerContent :title="t('settings.title')" closable :body-content-style="{ padding: '0 16px 16px' }">
      <NTabs type="line" size="small" animated>
        <!-- General Tab -->
        <NTabPane :name="t('settings.tabs.general')" :tab="t('settings.tabs.general')">
          <NSpace vertical :size="14" class="pt-3">
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm font-medium">{{ t('settings.dialect') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.dialect') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.dialect"
                :options="dialectOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm font-medium">{{ t('settings.generate.mode') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.generateMode') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.mode"
                :options="generateModeOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.parse.stringEncoding') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.stringEncoding') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.parse.stringEncoding"
                :options="stringEncodingOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.naming.mode') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.namingMode') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.naming.mode"
                :options="namingModeOptions"
                size="small"
              />
            </div>
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.comment') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.comment') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.generate.comment" size="small" />
            </div>
          </NSpace>
        </NTabPane>

        <!-- Advanced Tab -->
        <NTabPane :name="t('settings.tabs.advanced')" :tab="t('settings.tabs.advanced')">
          <NSpace vertical :size="14" class="pt-3">
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.parse.mode') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.parseMode') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.parse.mode"
                :options="parseModeOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.parse.stringDecodeMode') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.stringDecodeMode') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.parse.stringDecodeMode"
                :options="stringDecodeModeOptions"
                size="small"
              />
            </div>
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-1">
                <label class="text-sm">{{ t('settings.naming.debugLikeIncludeFunction') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.debugLikeIncludeFunction') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.naming.debugLikeIncludeFunction" size="small" />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.readability.returnInlineMaxComplexity') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.returnInlineMaxComplexity') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.readability.returnInlineMaxComplexity"
                :min="1"
                :max="50"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.readability.indexInlineMaxComplexity') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.indexInlineMaxComplexity') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.readability.indexInlineMaxComplexity"
                :min="1"
                :max="50"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.readability.argsInlineMaxComplexity') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.argsInlineMaxComplexity') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.readability.argsInlineMaxComplexity"
                :min="1"
                :max="50"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.readability.accessBaseInlineMaxComplexity') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.accessBaseInlineMaxComplexity') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.readability.accessBaseInlineMaxComplexity"
                :min="1"
                :max="50"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.indentWidth') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.indentWidth') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.generate.indentWidth"
                :min="1"
                :max="8"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.maxLineLength') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.maxLineLength') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.generate.maxLineLength"
                :min="40"
                :max="200"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.quoteStyle') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.quoteStyle') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.quoteStyle"
                :options="quoteStyleOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableStyle') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableStyle') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.tableStyle"
                :options="tableStyleOptions"
                size="small"
              />
            </div>
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.conservativeOutput') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.conservativeOutput') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.generate.conservativeOutput" size="small" />
            </div>
          </NSpace>
        </NTabPane>

        <!-- About Tab -->
        <NTabPane :name="t('settings.tabs.about')" :tab="t('settings.tabs.about')">
          <NSpace vertical :size="12" class="pt-3">
            <div class="rounded-lg border px-3 py-3" style="border-color: var(--app-border); background: var(--app-bg-alt)">
              <div class="text-sm font-medium">{{ t('settings.about.summary') }}</div>
              <p class="mt-2 text-xs leading-5" style="color: var(--app-text-secondary)">
                {{ t('settings.about.description') }}
              </p>
            </div>

            <div class="grid gap-2">
              <div class="rounded-lg border px-3 py-3" style="border-color: var(--app-border)">
                <div class="text-sm font-medium">{{ t('settings.about.highlights.multiDialect.title') }}</div>
                <p class="mt-1 text-xs leading-5" style="color: var(--app-text-secondary)">
                  {{ t('settings.about.highlights.multiDialect.description') }}
                </p>
              </div>
              <div class="rounded-lg border px-3 py-3" style="border-color: var(--app-border)">
                <div class="text-sm font-medium">{{ t('settings.about.highlights.localFirst.title') }}</div>
                <p class="mt-1 text-xs leading-5" style="color: var(--app-text-secondary)">
                  {{ t('settings.about.highlights.localFirst.description') }}
                </p>
              </div>
              <div class="rounded-lg border px-3 py-3" style="border-color: var(--app-border)">
                <div class="text-sm font-medium">{{ t('settings.about.highlights.tooling.title') }}</div>
                <p class="mt-1 text-xs leading-5" style="color: var(--app-text-secondary)">
                  {{ t('settings.about.highlights.tooling.description') }}
                </p>
              </div>
            </div>

            <div class="rounded-lg border px-3 py-3" style="border-color: var(--app-border)">
              <div class="mb-2 text-xs font-medium uppercase tracking-wide" style="color: var(--app-text-dim)">
                {{ t('settings.about.metaTitle') }}
              </div>
              <div class="flex items-center justify-between">
                <span class="text-sm">{{ t('settings.about.version') }}</span>
                <span class="text-sm opacity-60">{{ appVersion }}</span>
              </div>
              <div class="mt-3 flex items-center justify-between gap-3">
                <span class="text-sm">{{ t('settings.about.repo') }}</span>
                <NA href="https://github.com/x3zvawq/unluac-rs" target="_blank">
                  github.com/x3zvawq/unluac-rs
                </NA>
              </div>
            </div>

            <div class="flex gap-2 pt-1">
              <NButton size="small" secondary @click="copyShareUrl">
                {{ copied ? t('settings.share.copied') : t('settings.share.button') }}
              </NButton>
              <NButton size="small" secondary @click="settings.resetToDefaults()">
                {{ t('settings.share.reset') }}
              </NButton>
            </div>
          </NSpace>
        </NTabPane>
      </NTabs>
    </NDrawerContent>
  </NDrawer>
</template>
