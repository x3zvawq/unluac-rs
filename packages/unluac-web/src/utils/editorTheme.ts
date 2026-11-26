/**
 * 与 unluac-web 深蓝薄荷/瓷白青绿设计语言完全融合的 CodeMirror 6 编辑器与语法高亮主题。
 *
 * 替代通用 One Dark，使代码区、搜索栏、行号沟槽、高亮行与 Diff 视图都和工作区表面自然衔接。
 */

import { HighlightStyle, syntaxHighlighting } from '@codemirror/language'
import type { Extension } from '@codemirror/state'
import { EditorView } from '@codemirror/view'
import { tags as t } from '@lezer/highlight'

const darkHighlight = HighlightStyle.define([
  {
    tag: [t.keyword, t.controlKeyword, t.operatorKeyword, t.definitionKeyword],
    color: '#c4a7ff',
    fontWeight: '500',
  },
  { tag: [t.atom, t.bool, t.null, t.special(t.variableName)], color: '#f7a97e' },
  { tag: [t.number, t.integer, t.float], color: '#f8be7c' },
  { tag: [t.string, t.special(t.string), t.regexp], color: '#83e8cf' },
  { tag: [t.comment, t.lineComment, t.blockComment], color: '#6c7c9d', fontStyle: 'italic' },
  { tag: [t.function(t.variableName), t.function(t.propertyName)], color: '#7cc7ff' },
  { tag: [t.propertyName, t.attributeName], color: '#a5c6ff' },
  { tag: [t.variableName], color: '#e5e9ff' },
  { tag: [t.operator, t.punctuation, t.bracket], color: '#94a6c8' },
  { tag: [t.invalid], color: '#ff7d8d', textDecoration: 'underline' },
])

const lightHighlight = HighlightStyle.define([
  {
    tag: [t.keyword, t.controlKeyword, t.operatorKeyword, t.definitionKeyword],
    color: '#6c38d9',
    fontWeight: '500',
  },
  { tag: [t.atom, t.bool, t.null, t.special(t.variableName)], color: '#b54d1b' },
  { tag: [t.number, t.integer, t.float], color: '#b55210' },
  { tag: [t.string, t.special(t.string), t.regexp], color: '#0f7460' },
  { tag: [t.comment, t.lineComment, t.blockComment], color: '#7a88a1', fontStyle: 'italic' },
  { tag: [t.function(t.variableName), t.function(t.propertyName)], color: '#1b64c9' },
  { tag: [t.propertyName, t.attributeName], color: '#2b5599' },
  { tag: [t.variableName], color: '#202943' },
  { tag: [t.operator, t.punctuation, t.bracket], color: '#5b6b87' },
  { tag: [t.invalid], color: '#c8283f', textDecoration: 'underline' },
])

const darkChrome = EditorView.theme(
  {
    '&': {
      height: '100%',
      backgroundColor: '#171d30',
      color: '#e5e9ff',
      fontSize: '13px',
    },
    '.cm-content': {
      padding: '14px 0',
      caretColor: '#83e8cf',
      fontFamily: '"JetBrains Mono", "Cascadia Code", "SFMono-Regular", Consolas, monospace',
      lineHeight: '1.72',
    },
    '.cm-cursor, .cm-dropCursor': {
      borderLeftColor: '#83e8cf',
      borderLeftWidth: '2px',
    },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection': {
      backgroundColor: 'rgba(131, 232, 207, 0.2)',
    },
    '.cm-activeLine': {
      backgroundColor: 'rgba(131, 232, 207, 0.055)',
    },
    '.cm-activeLineGutter': {
      backgroundColor: 'rgba(131, 232, 207, 0.08)',
      color: '#d4ddf7',
    },
    '.cm-gutters': {
      backgroundColor: '#151b2d',
      color: '#637191',
      borderRight: '1px solid rgba(43, 52, 75, 0.6)',
    },
    '.cm-lineNumbers .cm-gutterElement': {
      padding: '0 14px 0 12px',
      minWidth: '42px',
    },
    '.cm-scroller': {
      overflow: 'auto',
    },
    '.cm-selectionMatch': {
      backgroundColor: 'rgba(124, 199, 255, 0.2)',
      borderRadius: '2px',
    },
    '.cm-searchMatch': {
      backgroundColor: 'rgba(248, 190, 124, 0.28)',
      outline: '1px solid rgba(248, 190, 124, 0.5)',
      borderRadius: '2px',
    },
    '.cm-searchMatch.cm-searchMatch-selected': {
      backgroundColor: 'rgba(131, 232, 207, 0.35)',
    },
    '.cm-panels': {
      backgroundColor: '#141a2b',
      color: '#e5e9ff',
      borderColor: '#2b344b',
    },
    '.cm-panels.cm-panels-bottom': {
      borderTop: '1px solid #2b344b',
    },
    '.cm-textfield': {
      backgroundColor: '#101526',
      color: '#e5e9ff',
      border: '1px solid #2b344b',
      borderRadius: '6px',
      padding: '3px 8px',
    },
    '.cm-button': {
      backgroundImage: 'none',
      backgroundColor: '#232d43',
      color: '#e5e9ff',
      border: '1px solid #32405e',
      borderRadius: '6px',
      padding: '3px 9px',
    },
    '.cm-highlighted-line': {
      backgroundColor: 'rgba(131, 232, 207, 0.14)',
      boxShadow: 'inset 3px 0 0 #83e8cf',
    },
  },
  { dark: true },
)

const lightChrome = EditorView.theme(
  {
    '&': {
      height: '100%',
      backgroundColor: '#ffffff',
      color: '#202943',
      fontSize: '13px',
    },
    '.cm-content': {
      padding: '14px 0',
      caretColor: '#147d69',
      fontFamily: '"JetBrains Mono", "Cascadia Code", "SFMono-Regular", Consolas, monospace',
      lineHeight: '1.72',
    },
    '.cm-cursor, .cm-dropCursor': {
      borderLeftColor: '#147d69',
      borderLeftWidth: '2px',
    },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground, .cm-content ::selection': {
      backgroundColor: 'rgba(20, 125, 105, 0.16)',
    },
    '.cm-activeLine': {
      backgroundColor: 'rgba(20, 125, 105, 0.045)',
    },
    '.cm-activeLineGutter': {
      backgroundColor: 'rgba(20, 125, 105, 0.07)',
      color: '#202943',
    },
    '.cm-gutters': {
      backgroundColor: '#fafbfe',
      color: '#8c99b0',
      borderRight: '1px solid #edf1f7',
    },
    '.cm-lineNumbers .cm-gutterElement': {
      padding: '0 14px 0 12px',
      minWidth: '42px',
    },
    '.cm-scroller': {
      overflow: 'auto',
    },
    '.cm-selectionMatch': {
      backgroundColor: 'rgba(27, 100, 201, 0.12)',
      borderRadius: '2px',
    },
    '.cm-searchMatch': {
      backgroundColor: 'rgba(234, 179, 8, 0.25)',
      outline: '1px solid rgba(202, 138, 4, 0.45)',
      borderRadius: '2px',
    },
    '.cm-searchMatch.cm-searchMatch-selected': {
      backgroundColor: 'rgba(20, 125, 105, 0.25)',
    },
    '.cm-panels': {
      backgroundColor: '#f5f7fb',
      color: '#202943',
      borderColor: '#e3e8f0',
    },
    '.cm-panels.cm-panels-bottom': {
      borderTop: '1px solid #e3e8f0',
    },
    '.cm-textfield': {
      backgroundColor: '#ffffff',
      color: '#202943',
      border: '1px solid #d4dce8',
      borderRadius: '6px',
      padding: '3px 8px',
    },
    '.cm-button': {
      backgroundImage: 'none',
      backgroundColor: '#ffffff',
      color: '#202943',
      border: '1px solid #d4dce8',
      borderRadius: '6px',
      padding: '3px 9px',
    },
    '.cm-highlighted-line': {
      backgroundColor: 'rgba(20, 125, 105, 0.11)',
      boxShadow: 'inset 3px 0 0 #147d69',
    },
  },
  { dark: false },
)

export function createUnluacEditorTheme(dark: boolean): Extension {
  return dark
    ? [darkChrome, syntaxHighlighting(darkHighlight)]
    : [lightChrome, syntaxHighlighting(lightHighlight)]
}
