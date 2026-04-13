<script setup lang="ts">
/**
 * 常量表面板。
 *
 * 展示选中 proto（或默认 proto#0）的常量池字面量列表。
 * 以紧凑表格形式呈现，每行显示索引、类型标签和值。
 */

import { computed } from 'vue'
import { useI18n } from 'vue-i18n'
import type { ProtoConstant } from '@/types/decompiler'

const props = defineProps<{
  constants: ProtoConstant[]
  protoName: string
}>()

const { t } = useI18n()

/** 类型标签对应的颜色类 */
const typeColorMap: Record<string, string> = {
  nil: 'text-gray-400',
  boolean: 'text-purple-500 dark:text-purple-400',
  integer: 'text-blue-600 dark:text-blue-400',
  number: 'text-cyan-600 dark:text-cyan-400',
  string: 'text-green-600 dark:text-green-400',
  int64: 'text-blue-600 dark:text-blue-400',
  uint64: 'text-blue-600 dark:text-blue-400',
  complex: 'text-orange-600 dark:text-orange-400',
}
</script>

<template>
  <div class="flex h-full flex-col">
    <div class="shrink-0 px-3 py-1.5 text-xs font-medium" style="color: var(--app-text-secondary); border-bottom: 1px solid var(--app-border)">
      {{ t('analysis.constants.title') }} — {{ protoName }}
      <span class="ml-1" style="color: var(--app-text-dim)">({{ constants.length }})</span>
    </div>
    <div v-if="constants.length === 0" class="flex flex-1 items-center justify-center">
      <span class="text-xs" style="color: var(--app-text-dim)">{{ t('analysis.constants.empty') }}</span>
    </div>
    <div v-else class="flex-1 overflow-y-auto">
      <table class="w-full text-xs">
        <thead class="sticky top-0" style="background: var(--app-bg)">
          <tr style="border-bottom: 1px solid var(--app-border)">
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim); width: 40px">#</th>
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim); width: 64px">{{ t('analysis.constants.type') }}</th>
            <th class="px-2 py-1 text-left font-medium" style="color: var(--app-text-dim)">{{ t('analysis.constants.value') }}</th>
          </tr>
        </thead>
        <tbody>
          <tr
            v-for="c in constants"
            :key="c.index"
            class="transition-colors hover:bg-gray-50 dark:hover:bg-gray-800/50"
            style="border-bottom: 1px solid var(--app-border)"
          >
            <td class="px-2 py-0.5 tabular-nums" style="color: var(--app-text-dim)">{{ c.index }}</td>
            <td class="px-2 py-0.5" :class="typeColorMap[c.type] ?? ''">{{ c.type }}</td>
            <td class="max-w-[200px] truncate px-2 py-0.5 font-mono" :title="c.display">{{ c.display }}</td>
          </tr>
        </tbody>
      </table>
    </div>
  </div>
</template>
