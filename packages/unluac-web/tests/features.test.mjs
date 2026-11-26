import assert from 'node:assert/strict'
import { test } from 'node:test'
import { createPinia, setActivePinia } from 'pinia'
import { unflattenSafe } from '../src/composables/useShareUrl.ts'
import {
  defaultOptions,
  normalizeCommentStyle,
  sanitizeOptions,
  useSettingsStore,
} from '../src/stores/settings.ts'
import { formatCodeForAi, stripVerboseDecompilerComments } from '../src/utils/aiSnippet.ts'
import { looksLikeBinaryFile } from '../src/utils/binarySniff.ts'
import { shouldIgnoreModifierShortcutTarget } from '../src/utils/keyboard.ts'
import { searchWorkspaceFiles } from '../src/utils/workspaceSearch.ts'
import { buildZip, resolveLuaExportPaths } from '../src/utils/zip.ts'

globalThis.localStorage ??= { getItem: () => null, setItem() {} }

function makeFile(id, relativePath, result, overrides = {}) {
  return {
    id,
    name: relativePath.split('/').pop(),
    relativePath,
    bytes: new Uint8Array([27, 76, 117, 97]),
    size: 4,
    status: 'success',
    dialect: 'lua5.1',
    revision: 1,
    result,
    ...overrides,
  }
}

test('defaultOptions, presets and strict option sanitization block invalid values & prototype pollution', () => {
  const defaults = defaultOptions()
  assert.equal(defaults.naming.mode, 'heuristic')
  assert.equal(defaults.generate.comment, 'minimal')
  assert.equal(defaults.generate.tableAlignCells, 'auto')
  assert.equal(defaults.generate.tableAlignEq, true)
  assert.equal(defaults.generate.tableDropIndexKeys, false)

  assert.equal(normalizeCommentStyle(true, 'minimal'), 'full')
  assert.equal(normalizeCommentStyle(false, 'minimal'), 'none')
  assert.equal(normalizeCommentStyle('minimal', 'full'), 'minimal')
  assert.equal(normalizeCommentStyle('unknown', 'minimal'), 'minimal')

  // Prototype pollution & hostile URL/localStorage parameters must be blocked/clamped
  const flat = unflattenSafe({
    '__proto__.polluted': 'yes',
    'constructor.prototype.polluted': 'yes',
    'generate.indentWidth': '999',
    'generate.maxLineLength': '5',
    'generate.tableStyle': 'bogus',
    'dialect': 'evil-lua',
    'parse.mode': 'strict',
  })
  assert.equal(({}).polluted, undefined)
  const sanitized = sanitizeOptions(flat)
  assert.equal(sanitized.dialect, 'auto')
  assert.equal(sanitized.parse.mode, 'strict')
  assert.equal(sanitized.generate.indentWidth, 8)
  assert.equal(sanitized.generate.maxLineLength, 40)
  assert.equal(sanitized.generate.tableStyle, 'balanced')

  setActivePinia(createPinia())
  const store = useSettingsStore()
  store.options.parse.stringEncoding = 'gbk'

  store.applyPreset('readable')
  assert.equal(store.activePreset, 'readable')
  assert.equal(store.options.generate.tableStyle, 'aligned')
  assert.equal(store.options.generate.tableDropIndexKeys, true)
  assert.equal(store.options.parse.stringEncoding, 'gbk')

  store.applyPreset('exact')
  assert.equal(store.activePreset, 'exact')
  assert.equal(store.options.naming.mode, 'debug-like')
  assert.equal(store.options.generate.comment, 'full')
  assert.equal(store.options.generate.readableStrings, false)

  store.applyPreset('ai')
  assert.equal(store.activePreset, 'ai')
  assert.equal(store.options.generate.tableStyle, 'compact')
  assert.equal(store.options.generate.comment, 'minimal')
})

test('searchWorkspaceFiles finds code, edited text, spaced queries, Unicode case-insensitive offsets and generatedLineStart constants', () => {
  const files = [
    makeFile(
      '1',
      'scripts/boss.luac',
      'local boss = {}\nfunction boss:Attack(target)\n  local İtag = "Attack"\n  return target.hp - 10\nend',
      {
        richResult: {
          source: '',
          kind: 'source',
          protos: [
            {
              id: 0,
              name: 'boss:Attack',
              lineStart: 99,
              lineEnd: 120,
              generatedLineStart: 2,
              generatedLineEnd: 5,
              numParams: 2,
              isVararg: false,
              numUpvalues: 0,
              numConstants: 1,
              numInstructions: 4,
              constants: [{ index: 0, type: 'string', display: '"SECRET_TOKEN_99"' }],
              children: [],
            },
          ],
          cfgs: [],
        },
      },
    ),
    makeFile('2', 'scripts/ui.luac', 'local title = "attack button"\n', {
      editedResult: 'local title = "ATTACK_EDITED"\n',
    }),
  ]

  const plain = searchWorkspaceFiles(files, 'attack')
  assert.equal(plain.totalMatches, 3)
  assert.equal(plain.groups.length, 2)
  // Line 3 contains Turkish dotted capital 'İ' before 'Attack' — RegExp match keeps exact UTF-16 slice!
  const unicodeMatch = plain.groups[0].matches[1]
  assert.equal(unicodeMatch.preview.slice(unicodeMatch.matchStart, unicodeMatch.matchEnd), 'Attack')
  assert.equal(plain.groups[1].matches[0].preview, 'local title = "ATTACK_EDITED"')

  // Meaningful spaces are preserved (not blindly trimmed)
  const spaced = searchWorkspaceFiles(files, ' = ')
  assert.equal(spaced.totalMatches, 3)

  const cs = searchWorkspaceFiles(files, 'Attack', { caseSensitive: true })
  assert.equal(cs.totalMatches, 2)
  assert.equal(cs.groups[0].fileId, '1')

  // Constant hit prefers generatedLineStart (2) over debug lineStart (99)
  const constHit = searchWorkspaceFiles(files, 'SECRET_TOKEN')
  assert.equal(constHit.totalMatches, 1)
  assert.equal(constHit.groups[0].matches[0].source, 'constant')
  assert.equal(constHit.groups[0].matches[0].line, 2)

  const badRegex = searchWorkspaceFiles(files, '[unclosed', { useRegex: true })
  assert.ok(badRegex.regexError)
  assert.equal(badRegex.totalMatches, 0)
})

test('formatCodeForAi strips real unluac banners, metadata, and inline proto/lines comments', () => {
  const realOutput = [
    '-- file: @boss.lua',
    '-- dialect: lua5.1',
    '-- encoding: auto',
    '-- decompiled by unluac-rs v1.4.5 (https://github.com/x3zvawq/unluac-rs)',
    '',
    'local M = {}',
    'function M:hit(target) -- lines=4-7',
    '    return target.hp - 1',
    'end',
    'local function aux() -- proto#2 params=0 locals=0 upvalues=0 lines=9-11',
    '    return true',
    'end',
    'return M',
  ].join('\n')

  const stripped = stripVerboseDecompilerComments(realOutput)
  assert.ok(!stripped.includes('-- file:'))
  assert.ok(!stripped.includes('-- dialect:'))
  assert.ok(!stripped.includes('-- encoding:'))
  assert.ok(!stripped.includes('decompiled by unluac-rs'))
  assert.ok(!stripped.includes('-- lines='))
  assert.ok(!stripped.includes('proto#2'))
  assert.ok(stripped.includes('function M:hit(target)\n'))
  assert.ok(stripped.includes('local function aux()\n'))

  const formatted = formatCodeForAi(
    { relativePath: 'scripts/boss.luac', dialect: 'lua5.1', status: 'success' },
    realOutput,
  )
  assert.ok(formatted.startsWith('File: `scripts/boss.luac` (Lua 5.1)\n```lua\n'))
  assert.ok(formatted.endsWith('\n```'))
})

test('looksLikeBinaryFile distinguishes empty/text Lua source from binary blobs', () => {
  assert.equal(looksLikeBinaryFile(new Uint8Array([])), false)
  assert.equal(looksLikeBinaryFile(new TextEncoder().encode('local x = "你好"\nreturn x\n')), false)
  // PNG header with NUL bytes
  assert.equal(looksLikeBinaryFile(new Uint8Array([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0x00])), true)
})

test('buildZip creates valid archive with disambiguated relative Lua paths', () => {
  const paths = resolveLuaExportPaths(['a/foo.luac', 'a/foo.lua', 'b/bar.bin'])
  assert.deepEqual(paths, ['a/foo.luac.lua', 'a/foo.lua', 'b/bar.lua'])

  const zip = buildZip([
    { path: paths[0], content: 'return 1\n' },
    { path: paths[2], content: 'return 2\n' },
  ])
  // Local file header magic PK\x03\x04 and EOCD magic PK\x05\x06
  assert.equal(zip[0], 0x50)
  assert.equal(zip[1], 0x4b)
  assert.equal(zip[2], 0x03)
  assert.equal(zip[3], 0x04)
  assert.equal(zip[zip.length - 22], 0x50)
  assert.equal(zip[zip.length - 21], 0x4b)
  assert.equal(zip[zip.length - 20], 0x05)
  assert.equal(zip[zip.length - 19], 0x06)
})

test('modifier shortcuts work inside CodeMirror .cm-content while yielding to form inputs', () => {
  const cmContent = {
    tagName: 'DIV',
    isContentEditable: true,
    classList: { contains: (c) => c === 'cm-content' },
    parentElement: null,
  }
  const cmLine = {
    tagName: 'DIV',
    isContentEditable: true,
    classList: { contains: () => false },
    parentElement: cmContent,
  }
  const input = {
    tagName: 'INPUT',
    isContentEditable: false,
    classList: { contains: () => false },
    parentElement: null,
  }
  assert.equal(shouldIgnoreModifierShortcutTarget(cmLine), false)
  assert.equal(shouldIgnoreModifierShortcutTarget(input), true)
})
