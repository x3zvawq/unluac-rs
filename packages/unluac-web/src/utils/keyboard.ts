/**
 * document 级快捷键的目标判定。
 *
 * 这个文件把“键盘事件是否应该交还给局部控件”做成单一事实源。
 * web 界面里既有 App 级快捷键，也有 FilePanel 级 Delete/Arrow
 * 操作；如果每个监听器各自判断，很容易漏掉 CodeMirror 搜索框、
 * contenteditable 或表单控件，导致输入时误触全局动作。
 */

const LOCAL_KEYBOARD_TAGS = new Set(['INPUT', 'TEXTAREA', 'SELECT', 'BUTTON'])

interface KeyboardElementLike {
  tagName?: string
  isContentEditable?: boolean
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
