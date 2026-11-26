<script setup lang="ts">
/**
 * 常量表面板。
 *
 * 展示选中 proto（或默认 proto#0）的常量池字面量列表，
 * 支持实时关键词过滤、类型筛选胶囊与点击复制常量值。
 */

import { computed, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import type { ProtoConstant } from '@/types/decompiler'

const props = defineProps<{
  constants: ProtoConstant[]
  protoName: string
}>()

const { t } = useI18n()

type ConstantFilterKind = 'all' | 'string' | 'number' | 'other'
const query = shallowRef('')
const kindFilter = shallowRef<ConstantFilterKind>('all')
const copiedIndex = shallowRef<number | null>(null)

function classifyKind(type: ProtoConstant['type']): Exclude<ConstantFilterKind, 'all'> {
  if (type === 'string') return 'string'
  if (type === 'integer' || type === 'number' || type === 'int64' || type === 'uint64') {
    return 'number'
  }
  return 'other'
}

const filteredConstants = computed(() => {
  const q = query.value.trim().toLowerCase()
  return props.constants.filter((c) => {
    if (kindFilter.value !== 'all' && classifyKind(c.type) !== kindFilter.value) return false
    if (q && !c.display.toLowerCase().includes(q) && !c.type.toLowerCase().includes(q)) return false
    return true
  })
})

const typeColorMap: Record<string, string> = {
  nil: 'text-slate-400',
  boolean: 'text-violet-500 dark:text-violet-400',
  integer: 'text-amber-600 dark:text-amber-400',
  number: 'text-amber-600 dark:text-amber-400',
  string: 'text-emerald-600 dark:text-emerald-400',
  int64: 'text-amber-600 dark:text-amber-400',
  uint64: 'text-amber-600 dark:text-amber-400',
  complex: 'text-orange-600 dark:text-orange-400',
  vector: 'text-sky-600 dark:text-sky-400',
}

async function copyConstant(constant: ProtoConstant) {
  try {
    await navigator.clipboard.writeText(constant.display)
  } catch {
    const textarea = document.createElement('textarea')
    textarea.value = constant.display
    document.body.appendChild(textarea)
    textarea.select()
    document.execCommand('copy')
    document.body.removeChild(textarea)
  }
  copiedIndex.value = constant.index
  setTimeout(() => {
    if (copiedIndex.value === constant.index) copiedIndex.value = null
  }, 1400)
}
</script>

<template>
  <div class="flex h-full flex-col">
    <div
      class="shrink-0 px-3 py-1.5 text-xs font-medium"
      style="color: var(--app-text-secondary); border-bottom: 1px solid var(--app-border)"
    >
      <div class="flex items-center justify-between gap-2">
        <span class="truncate">{{ t('analysis.constants.title') }} — {{ protoName }}</span>
        <span class="shrink-0 tabular-nums" style="color: var(--app-text-dim)">
          ({{ filteredConstants.length }}<template v-if="filteredConstants.length !== constants.length">/{{ constants.length }}</template>)
        </span>
      </div>
      <div v-if="constants.length > 0" class="mt-1.5 flex flex-col gap-1.5">
        <NInput
          v-model:value="query"
          size="tiny"
          clearable
          :placeholder="t('analysis.constants.searchPlaceholder')"
        >
          <template #prefix><i-mdi-magnify /></template>
        </NInput>
        <div class="flex flex-wrap gap-1">
          <button
            v-for="pill in (['all', 'string', 'number', 'other'] as const)"
            :key="pill"
            type="button"
            class="const-filter-pill"
            :class="{ active: kindFilter === pill }"
            @click="kindFilter = pill"
          >
            {{ pill === 'all' ? t('analysis.constants.filterAll') : pill }}
          </button>
        </div>
      </div>
    </div>

    <div v-if="constants.length === 0" class="flex flex-1 items-center justify-center">
      <span class="text-xs" style="color: var(--app-text-dim)">{{ t('analysis.constants.empty') }}</span>
    </div>
    <div v-else-if="filteredConstants.length === 0" class="flex flex-1 items-center justify-center">
      <span class="text-xs" style="color: var(--app-text-dim)">{{ t('globalSearch.noResults') }}</span>
    </div>
    <div v-else class="flex-1 overflow-y-auto">
      <table class="w-full text-xs">
        <thead class="sticky top-0" style="background: var(--app-bg)">
          <tr style="border-bottom: 1px solid var(--app-border)">
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim); width: 38px">#</th>
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim); width: 58px">{{ t('analysis.constants.type') }}</th>
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim)">{{ t('analysis.constants.value') }}</th>
          </tr>
        </thead>
        <tbody>
          <tr
            v-for="c in filteredConstants"
            :key="c.index"
            class="const-row cursor-pointer transition-colors"
            style="border-bottom: 1px solid var(--app-border)"
            :title="t('analysis.constants.clickToCopy')"
            @click="copyConstant(c)"
          >
            <td class="px-2 py-1 tabular-nums" style="color: var(--app-text-dim)">
              {{ copiedIndex === c.index ? '✓' : c.index }}
            </td>
            <td class="px-2 py-1" :class="typeColorMap[c.type] ?? ''">{{ c.type }}</td>
            <td class="max-w-50 truncate px-2 py-1 font-mono" :title="c.display">{{ c.display }}</td>
          </tr>
        </tbody>
      </table>
    </div>
  </div>
</template>
