<script setup lang="ts">
import { dialectOptions } from '@/utils/dialects'
/**
 * 设置面板。
 *
 * 当前将设置收敛为“通用 / 高级 / 关于”三组：
 * - 通用：最常改、最影响输出风格的少量选项；
 * - 高级：保留所有细粒度调参项，避免默认界面过于拥挤；
 * - 关于：补充产品定位、能力边界与项目入口，减少面板信息过干的问题。
 */

import { computed, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import { generateShareUrl } from '@/composables/useShareUrl'
import { defaultOptions, useSettingsStore } from '@/stores/settings'
import type { SettingsPresetId } from '@/types/decompiler'

defineProps<{
  show: boolean
}>()

const emit = defineEmits<{
  'update:show': [value: boolean]
}>()

const { t } = useI18n()
const settings = useSettingsStore()
const copied = shallowRef(false)
const cliCopied = shallowRef(false)
const appVersion = __APP_VERSION__
const luauVectorEnabled = computed({
  get: () => settings.options.generate.luauVectorConstructor !== null,
  set: (enabled: boolean) => {
    settings.options.generate.luauVectorConstructor = enabled
      ? { library: 'vector', constructor: 'create', size: 3 }
      : null
  },
})
const luauVectorLibrary = computed({
  get: () => settings.options.generate.luauVectorConstructor?.library ?? '',
  set: (library: string) => {
    const vector = settings.options.generate.luauVectorConstructor
    if (vector) vector.library = library || null
  },
})

async function copyText(text: string) {
  try {
    await navigator.clipboard.writeText(text)
  } catch {
    const textarea = document.createElement('textarea')
    textarea.value = text
    document.body.appendChild(textarea)
    textarea.select()
    document.execCommand('copy')
    document.body.removeChild(textarea)
  }
}

function copyShareUrl() {
  const url = generateShareUrl()
  void copyText(url).then(() => {
    copied.value = true
    setTimeout(() => {
      copied.value = false
    }, 2000)
  })
}

function copyCliArgs() {
  const args = buildCliArgs()
  void copyText(args).then(() => {
    cliCopied.value = true
    setTimeout(() => {
      cliCopied.value = false
    }, 2000)
  })
}

function buildCliArgs(): string {
  const defaults = defaultOptions()
  const options = settings.options
  const args: string[] = []
  pushOption(args, '--dialect', options.dialect, defaults.dialect)
  pushOption(args, '--encoding', options.parse.stringEncoding, defaults.parse.stringEncoding)
  pushOption(args, '--decode-mode', options.parse.stringDecodeMode, defaults.parse.stringDecodeMode)
  pushOption(args, '--parse-mode', options.parse.mode, defaults.parse.mode)
  if (options.parse.ignoreDebug) args.push('--ignore-debug')
  pushOption(args, '--naming-mode', options.naming.mode, defaults.naming.mode)
  pushOption(
    args,
    '--debug-like-include-function',
    options.naming.debugLikeIncludeFunction,
    defaults.naming.debugLikeIncludeFunction,
  )
  pushOption(args, '--generate-mode', options.generate.mode, defaults.generate.mode)
  pushOption(args, '--indent-width', options.generate.indentWidth, defaults.generate.indentWidth)
  pushOption(
    args,
    '--max-line-length',
    options.generate.maxLineLength,
    defaults.generate.maxLineLength,
  )
  pushOption(args, '--number-format', options.generate.numberFormat, defaults.generate.numberFormat)
  pushOption(args, '--quote-style', options.generate.quoteStyle, defaults.generate.quoteStyle)
  pushOption(
    args,
    '--readable-strings',
    options.generate.readableStrings,
    defaults.generate.readableStrings,
  )
  pushOption(args, '--table-style', options.generate.tableStyle, defaults.generate.tableStyle)
  if (options.generate.tableAlignWidth !== null) {
    args.push('--table-align-width', String(options.generate.tableAlignWidth))
  }
  pushOption(
    args,
    '--table-align-string-width',
    options.generate.tableAlignStringWidth,
    defaults.generate.tableAlignStringWidth,
  )
  pushOption(
    args,
    '--table-align-eq',
    options.generate.tableAlignEq,
    defaults.generate.tableAlignEq,
  )
  pushOption(
    args,
    '--table-align-eq-max-spaces',
    options.generate.tableAlignEqMaxSpaces,
    defaults.generate.tableAlignEqMaxSpaces,
  )
  pushOption(
    args,
    '--table-align-cells',
    options.generate.tableAlignCells,
    defaults.generate.tableAlignCells,
  )
  if (options.generate.tableDropIndexKeys) args.push('--table-drop-index-keys')
  if (options.generate.luauVectorConstructor) {
    if (options.generate.luauVectorConstructor.library) {
      args.push('--luau-vector-library', shellQuote(options.generate.luauVectorConstructor.library))
    }
    args.push(
      '--luau-vector-constructor',
      shellQuote(options.generate.luauVectorConstructor.constructor),
    )
    args.push('--luau-vector-size', String(options.generate.luauVectorConstructor.size))
  }
  pushOption(args, '--comment', options.generate.comment, defaults.generate.comment)
  return args.join(' ')
}

function pushOption(
  args: string[],
  flag: string,
  value: string | number | boolean,
  defaultValue: string | number | boolean,
) {
  if (value === defaultValue) return
  args.push(flag, shellQuote(String(value)))
}

function shellQuote(value: string): string {
  return /^[A-Za-z0-9._/-]+$/.test(value) ? value : `'${value.replaceAll("'", "'\\''")}'`
}

const parseModeOptions = [
  { label: 'strict', value: 'strict' },
  { label: 'permissive', value: 'permissive' },
]

const stringEncodingOptions = [
  { label: 'Auto', value: 'auto' },
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
  { label: 'permissive', value: 'permissive' },
]

const quoteStyleOptions = [
  { label: 'prefer-double', value: 'prefer-double' },
  { label: 'prefer-single', value: 'prefer-single' },
  { label: 'min-escape', value: 'min-escape' },
]

const numberFormatOptions = [
  { label: 'decimal', value: 'decimal' },
  { label: 'hex', value: 'hex' },
]

const tableStyleOptions = [
  { label: 'compact', value: 'compact' },
  { label: 'balanced', value: 'balanced' },
  { label: 'aligned', value: 'aligned' },
  { label: 'expanded', value: 'expanded' },
]

const tableAlignCellsOptions = [
  { label: 'auto', value: 'auto' },
  { label: 'left', value: 'left' },
  { label: 'right', value: 'right' },
]

const commentStyleOptions = computed(() => [
  { label: t('settings.generate.commentOptions.minimal'), value: 'minimal' },
  { label: t('settings.generate.commentOptions.full'), value: 'full' },
  { label: t('settings.generate.commentOptions.none'), value: 'none' },
])

const presetItems = computed<{ id: SettingsPresetId; label: string; description: string }[]>(() => [
  {
    id: 'readable',
    label: t('settings.presets.readable.label'),
    description: t('settings.presets.readable.description'),
  },
  {
    id: 'exact',
    label: t('settings.presets.exact.label'),
    description: t('settings.presets.exact.description'),
  },
  {
    id: 'ai',
    label: t('settings.presets.ai.label'),
    description: t('settings.presets.ai.description'),
  },
])

const activePresetDescription = computed(() => {
  const current = presetItems.value.find((item) => item.id === settings.activePreset)
  return current?.description ?? t('settings.presets.hint')
})
</script>

<template>
  <NDrawer :show="show" :width="'min(440px, 100vw)'" placement="right" @update:show="emit('update:show', $event)">
    <NDrawerContent :title="t('settings.title')" closable :body-content-style="{ padding: '8px 24px 24px' }">
      <p class="settings-intro">{{ t('workspace.settingsHint') }}</p>
      <NTabs type="segment" size="small" animated>
        <!-- General Tab -->
        <NTabPane :name="t('settings.tabs.general')" :tab="t('settings.tabs.general')">
          <NSpace vertical :size="22" class="pt-5">
            <div
              class="rounded-lg border p-3"
              style="border-color: var(--app-border); background: var(--app-bg-alt)"
            >
              <div class="mb-2 text-xs font-semibold uppercase tracking-wide" style="color: var(--app-text-secondary)">
                {{ t('settings.presets.title') }}
              </div>
              <div class="grid grid-cols-3 gap-2">
                <NButton
                  v-for="preset in presetItems"
                  :key="preset.id"
                  size="small"
                  :type="settings.activePreset === preset.id ? 'primary' : 'default'"
                  :secondary="settings.activePreset !== preset.id"
                  @click="settings.applyPreset(preset.id)"
                >
                  {{ preset.label }}
                </NButton>
              </div>
              <p class="setting-hint mt-2 mb-0">{{ activePresetDescription }}</p>
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm font-medium">{{ t('settings.importDialect') }}</label>
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
              <p class="setting-hint">{{ t('settings.tips.dialect') }}</p>
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
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.comment') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.comment') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.comment"
                :options="commentStyleOptions"
                size="small"
              />
            </div>
          </NSpace>
        </NTabPane>

        <!-- Advanced Tab -->
        <NTabPane :name="t('settings.tabs.advanced')" :tab="t('settings.tabs.advanced')">
          <NSpace vertical :size="22" class="pt-5">
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
                <label class="text-sm">{{ t('settings.parse.ignoreDebug') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.ignoreDebug') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.parse.ignoreDebug" size="small" />
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
                <label class="text-sm">{{ t('settings.generate.readableStrings') }}</label>
                <NTooltip>
                  <template #trigger><span class="cursor-help opacity-50">ⓘ</span></template>
                  {{ t('settings.tips.readableStrings') }}
                </NTooltip>
                <NSwitch v-model:value="settings.options.generate.readableStrings" :aria-label="t('settings.generate.readableStrings')" size="small" />
              </div>
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
                <label class="text-sm">{{ t('settings.generate.numberFormat') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.numberFormat') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.numberFormat"
                :options="numberFormatOptions"
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
                <label class="text-sm">{{ t('settings.generate.tableDropIndexKeys') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableDropIndexKeys') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.generate.tableDropIndexKeys" size="small" />
            </div>
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableAlignEq') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableAlignEq') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="settings.options.generate.tableAlignEq" size="small" />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableAlignEqMaxSpaces') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableAlignEqMaxSpaces') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.generate.tableAlignEqMaxSpaces"
                :min="0"
                :max="32"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableAlignCells') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableAlignCells') }}
                </NTooltip>
              </div>
              <NSelect
                v-model:value="settings.options.generate.tableAlignCells"
                :options="tableAlignCellsOptions"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableAlignWidth') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableAlignWidth') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.generate.tableAlignWidth"
                :min="20"
                :max="240"
                clearable
                :placeholder="String(settings.options.generate.maxLineLength)"
                size="small"
              />
            </div>
            <div>
              <div class="mb-1 flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.tableAlignStringWidth') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.tableAlignStringWidth') }}
                </NTooltip>
              </div>
              <NInputNumber
                v-model:value="settings.options.generate.tableAlignStringWidth"
                :min="4"
                :max="120"
                size="small"
              />
            </div>
            <div class="flex items-center justify-between">
              <div class="flex items-center gap-1">
                <label class="text-sm">{{ t('settings.generate.luauVectorConstructor') }}</label>
                <NTooltip>
                  <template #trigger>
                    <NIcon :size="14" class="cursor-help opacity-50"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><line x1="12" y1="17" x2="12.01" y2="17"/></svg></NIcon>
                  </template>
                  {{ t('settings.tips.luauVectorConstructor') }}
                </NTooltip>
              </div>
              <NSwitch v-model:value="luauVectorEnabled" size="small" />
            </div>
            <div v-if="settings.options.generate.luauVectorConstructor" class="grid grid-cols-3 gap-2">
              <NInput
                v-model:value="luauVectorLibrary"
                :placeholder="t('settings.generate.luauVectorLibrary')"
                clearable
                size="small"
              />
              <NInput
                v-model:value="settings.options.generate.luauVectorConstructor.constructor"
                :placeholder="t('settings.generate.luauVectorConstructorName')"
                size="small"
              />
              <NSelect
                v-model:value="settings.options.generate.luauVectorConstructor.size"
                :options="[
                  { label: '3D', value: 3 },
                  { label: '4D', value: 4 },
                ]"
                size="small"
              />
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

            <div class="flex flex-wrap gap-2 pt-1">
              <NButton size="small" secondary @click="copyShareUrl">
                {{ copied ? t('settings.share.copied') : t('settings.share.button') }}
              </NButton>
              <NButton size="small" secondary @click="copyCliArgs">
                {{ cliCopied ? t('settings.share.cliCopied') : t('settings.share.cliButton') }}
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
