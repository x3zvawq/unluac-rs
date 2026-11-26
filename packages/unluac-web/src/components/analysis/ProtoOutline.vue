<script setup lang="ts">
/**
 * 可搜索的函数大纲视图（Outline）。
 *
 * 适合快速按名称/常量定位函数，或在包含数百至数千 proto 的大型脚本中提供零卡顿导航。
 * 点击行直接跳转到源码对应行；右侧 CFG 按钮进入控制流图视图。
 */

import { computed, shallowRef } from 'vue'
import { useI18n } from 'vue-i18n'
import type { ProtoMeta } from '@/types/decompiler'

const props = defineProps<{
  protos: ProtoMeta[]
  failedProtos?: number[]
  selectedProtoId?: number | null
}>()

const emit = defineEmits<{
  'select-proto': [protoId: number]
  'jump-to-source': [protoId: number]
}>()

const { t } = useI18n()
const filter = shallowRef('')

const failedSet = computed(() => new Set(props.failedProtos ?? []))

interface OutlineRow {
  proto: ProtoMeta
  depth: number
  displayName: string
  lineLabel: string
  hasLine: boolean
  isFailed: boolean
}

const allRows = computed<OutlineRow[]>(() => {
  const depths = new Map<number, number>([[0, 0]])
  const rows: OutlineRow[] = []

  for (const proto of props.protos) {
    const depth = depths.get(proto.id) ?? 0
    for (const childId of proto.children) {
      depths.set(childId, depth + 1)
    }

    const displayName =
      proto.name ?? (proto.id === 0 ? `${t('analysis.protoGraph.root')} #0` : `Proto #${proto.id}`)
    const start =
      proto.generatedLineStart && proto.generatedLineStart > 0
        ? proto.generatedLineStart
        : proto.lineStart
    const end =
      proto.generatedLineStart && proto.generatedLineStart > 0
        ? (proto.generatedLineEnd ?? start)
        : proto.lineEnd || start

    rows.push({
      proto,
      depth,
      displayName,
      lineLabel: start > 0 ? (start === end ? `L${start}` : `L${start}-${end}`) : '',
      hasLine: start > 0,
      isFailed: failedSet.value.has(proto.id),
    })
  }

  return rows
})

const filteredRows = computed(() => {
  const q = filter.value.trim().toLowerCase()
  if (!q) return allRows.value
  return allRows.value.filter((row) => {
    if (row.displayName.toLowerCase().includes(q)) return true
    if (`#${row.proto.id}`.includes(q) || `proto#${row.proto.id}`.includes(q)) return true
    return row.proto.constants.some((c) => c.display.toLowerCase().includes(q))
  })
})
</script>

<template>
  <div class="flex h-full flex-col">
    <div
      class="flex shrink-0 items-center gap-2 px-3 py-2"
      style="border-bottom: 1px solid var(--app-border); background: var(--app-bg)"
    >
      <NInput
        v-model:value="filter"
        size="tiny"
        clearable
        :placeholder="t('analysis.outline.searchPlaceholder')"
        class="max-w-xs"
      >
        <template #prefix><i-mdi-magnify /></template>
      </NInput>
      <span class="text-[11px] tabular-nums" style="color: var(--app-text-dim)">
        {{ filteredRows.length }} / {{ allRows.length }}
      </span>
    </div>

    <div v-if="filteredRows.length === 0" class="flex flex-1 items-center justify-center">
      <span class="text-xs" style="color: var(--app-text-dim)">{{ t('filePanel.noFiles') }}</span>
    </div>

    <div v-else class="flex-1 overflow-y-auto py-1">
      <div
        v-for="row in filteredRows"
        :key="row.proto.id"
        class="outline-row group flex items-center gap-2 px-3 py-1.5 text-xs"
        :class="{ active: row.proto.id === selectedProtoId }"
        :style="{ paddingLeft: `${Math.min(row.depth, 8) * 14 + 12}px` }"
        @click="row.hasLine ? emit('jump-to-source', row.proto.id) : emit('select-proto', row.proto.id)"
      >
        <span
          class="inline-block h-1.5 w-1.5 shrink-0 rounded-full"
          :style="{ background: row.isFailed ? '#ef4444' : 'var(--app-accent)' }"
        />
        <span class="font-mono text-[11px] tabular-nums" style="color: var(--app-text-dim)">
          #{{ row.proto.id }}
        </span>
        <span class="min-w-0 flex-1 truncate font-mono font-medium" :title="row.displayName">
          {{ row.displayName }}
        </span>
        <span
          v-if="row.lineLabel"
          class="shrink-0 font-mono text-[10px] tabular-nums"
          style="color: var(--app-accent)"
        >
          {{ row.lineLabel }}
        </span>
        <span
          class="hidden shrink-0 font-mono text-[10px] tabular-nums sm:inline"
          style="color: var(--app-text-dim)"
        >
          P{{ row.proto.numParams }}{{ row.proto.isVararg ? '+' : '' }} · ↑{{ row.proto.numUpvalues }} · I{{ row.proto.numInstructions }}
        </span>
        <button
          type="button"
          class="outline-cfg-btn shrink-0 rounded px-1.5 py-0.5 text-[10px] font-medium"
          @click.stop="emit('select-proto', row.proto.id)"
        >
          CFG
        </button>
      </div>
    </div>
  </div>
</template>
