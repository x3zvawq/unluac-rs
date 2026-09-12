import type { UnluacDialect } from '@/types/decompiler'

/** 界面标签只映射显示名称；字节码版本识别属于核心 Parser。 */
export const dialectOptions: { label: string; value: UnluacDialect }[] = [
  { label: 'Auto', value: 'auto' },
  { label: 'Lua 5.1', value: 'lua5.1' },
  { label: 'Lua 5.2', value: 'lua5.2' },
  { label: 'Lua 5.3', value: 'lua5.3' },
  { label: 'Lua 5.4', value: 'lua5.4' },
  { label: 'Lua 5.5', value: 'lua5.5' },
  { label: 'LuaJIT', value: 'luajit' },
  { label: 'Luau', value: 'luau' },
]
