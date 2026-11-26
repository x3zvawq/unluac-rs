/**
 * document 级快捷键的目标判定。
 *
 * 这个文件把“键盘事件是否应该交还给局部控件”做成单一事实源。
 * 区分普通单键导航（ArrowUp/Down/Delete，编辑区内必须拦截）
 * 与带 Ctrl/Cmd 修饰符的全局动作（Ctrl/Cmd+S/O/, 在代码编辑器内仍应生效，
 * 仅在普通表单控件如搜索输入框内让位）。
 */

const LOCAL_KEYBOARD_TAGS = new Set(['INPUT', 'TEXTAREA', 'SELECT', 'BUTTON'])

interface KeyboardElementLike {
  tagName?: string
  isContentEditable?: boolean
  classList?: { contains(name: string): boolean }
  parentElement?: KeyboardElementLike | null
}

function toKeyboardElementLike(target: EventTarget | null): KeyboardElementLike | null {
  if (!target || typeof target !== 'object') return null
  return target as KeyboardElementLike
}

export function shouldIgnoreDocumentShortcutTarget(target: EventTarget | null): boolean {
  let element = toKeyboardElementLike(target)
  while (element) {
    if (element.isContentEditable) return true
    const tagName = element.tagName?.toUpperCase()
    if (tagName && LOCAL_KEYBOARD_TAGS.has(tagName)) return true
    element = element.parentElement ?? null
  }
  return false
}

/**
 * 修饰键全局快捷键（Ctrl/Cmd+S/O/,）的目标判定：
 * 允许在 CodeMirror 代码编辑区（`.cm-content`）内触发，但在原生表单输入控件中放行。
 */
export function shouldIgnoreModifierShortcutTarget(target: EventTarget | null): boolean {
  let element = toKeyboardElementLike(target)
  let inCodeMirrorEditor = false
  let sawContentEditable = false
  while (element) {
    const tagName = element.tagName?.toUpperCase()
    if (tagName && LOCAL_KEYBOARD_TAGS.has(tagName)) return true
    if (element.classList?.contains('cm-content')) {
      inCodeMirrorEditor = true
    }
    if (element.isContentEditable) {
      sawContentEditable = true
    }
    element = element.parentElement ?? null
  }
  return sawContentEditable && !inCodeMirrorEditor
}
