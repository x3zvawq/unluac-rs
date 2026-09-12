import { execFileSync } from 'node:child_process'
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { expect, test } from '@playwright/test'

const root = resolve(import.meta.dirname, '../../../..')
const fixtures = resolve(root, 'tmp/web-ui-tests/fixtures')

test.beforeAll(() => {
  mkdirSync(fixtures, { recursive: true })
  writeFileSync(resolve(fixtures, 'sample.lua'), 'local function twice(n) return n * 2 end\nprint("browser-test", twice(21))\n')
  for (const dialect of ['lua5.1', 'lua5.4']) {
    execFileSync(resolve(root, 'lua/build', dialect, process.platform === 'win32' ? 'luac.exe' : 'luac'), [
      '-o', resolve(fixtures, `${dialect}.luac`), resolve(fixtures, 'sample.lua'),
    ])
  }
})

test('mixed dialects, search, settings, structure and editing work together', async ({ page }) => {
  const errors: string[] = []
  page.on('pageerror', error => errors.push(error.message))
  await page.addInitScript(() => {
    const NativeWorker = window.Worker
    ;(window as any).sourceJobs = 0
    window.Worker = class extends NativeWorker {
      postMessage(message: any, transfer: any) {
        if (message.type === 'decompile') (window as any).sourceJobs++
        super.postMessage(message, transfer)
      }
    }
  })
  await page.goto('/')
  await expect(page.getByRole('heading', { level: 1 })).toContainText('made readable')
  const picker = page.waitForEvent('filechooser')
  await page.locator('.welcome-actions').getByRole('button', { name: 'Open File', exact: true }).click()
  await (await picker).setFiles(['lua5.1', 'lua5.4'].map(d => resolve(fixtures, `${d}.luac`)))
  const rows = page.locator('.file-row')
  await expect(rows.filter({ hasText: 'lua5.1.luac' }).locator('.dialect-tag')).toHaveText('Lua 5.1')
  await expect(rows.filter({ hasText: 'lua5.4.luac' }).locator('.dialect-tag')).toHaveText('Lua 5.4')
  await expect(rows.filter({ hasText: 'Success' })).toHaveCount(2)
  await expect(page.locator('.cm-content')).toContainText('browser-test')
  await page.getByRole('textbox', { name: 'Find a file…' }).fill('5.4')
  await expect(rows).toHaveCount(1)
  await page.getByRole('textbox', { name: 'Find a file…' }).fill('')

  const jobs = await page.evaluate(() => (window as any).sourceJobs)
  await page.getByRole('button', { name: 'Settings', exact: true }).click()
  await page.getByText('Default dialect for new files', { exact: true }).locator('../..').locator('.n-base-selection').click()
  await page.getByText('Lua 5.2', { exact: true }).last().click()
  await page.keyboard.press('Escape')
  await expect.poll(() => page.evaluate(() => (window as any).sourceJobs)).toBe(jobs)
  await expect(rows.filter({ hasText: 'lua5.1.luac' }).locator('.dialect-tag')).toHaveText('Lua 5.1')

  // Rich analysis is available and can release the space used by the graph.
  await expect(page.locator('.vue-flow__node').first()).toBeVisible()
  await page.locator('.vue-flow__node').first().click()
  await expect(page.getByRole('button', { name: 'Bytecode', exact: true })).toBeVisible()
  await page.getByRole('button', { name: 'Structure', exact: true }).click()
  await expect(page.getByRole('button', { name: 'Structure', exact: true })).toHaveAttribute('aria-expanded', 'false')

  const editor = page.locator('.cm-content')
  const original = await editor.innerText()
  await editor.click()
  await editor.press('ControlOrMeta+End')
  await page.keyboard.insertText('\n-- browser edit')
  await expect(page.getByText('Modified', { exact: true })).toBeVisible()
  await editor.press('ControlOrMeta+z')
  await expect(editor).toHaveText(original, { useInnerText: true })
  await editor.press('ControlOrMeta+End')
  await page.keyboard.insertText('\n-- keep this edit')
  await rows.filter({ hasText: 'lua5.4.luac' }).locator('.file-select').click()
  const otherSource = await editor.innerText()
  await editor.click()
  await editor.press('ControlOrMeta+z')
  await expect(editor).toHaveText(otherSource, { useInnerText: true })
  await rows.filter({ hasText: 'lua5.1.luac' }).locator('.file-select').click()
  await expect(editor).toContainText('-- keep this edit')
  const download = page.waitForEvent('download')
  await page.getByRole('button', { name: 'Download', exact: true }).click()
  const saved = await (await download).path()
  expect(readFileSync(saved!, 'utf8')).toContain('-- keep this edit')
  await page.getByRole('button', { name: 'Wrap lines', exact: true }).click()
  await expect(editor).toHaveClass(/cm-lineWrapping/)
  await page.screenshot({ path: resolve(root, 'tmp/web-ui-tests/workspace.png'), animations: 'disabled' })
  expect(errors).toEqual([])
})

test('mobile imports, settings, file menus and history survive responsive layout changes', async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 })
  await page.goto('/')
  const picker = page.waitForEvent('filechooser')
  await page.getByRole('button', { name: 'Open File', exact: true }).click()
  await (await picker).setFiles(resolve(fixtures, 'lua5.1.luac'))
  await expect(page.locator('.cm-content')).toContainText('browser-test')
  await expect(page.getByRole('button', { name: 'Structure', exact: true })).toHaveAttribute('aria-expanded', 'false')
  await page.getByRole('button', { name: 'Structure', exact: true }).click()
  await expect(page.locator('.vue-flow__node').first()).toBeVisible()
  await page.getByRole('button', { name: 'Constants', exact: true }).click()
  await expect(page.getByRole('cell', { name: '"browser-test"', exact: true })).toBeVisible()
  await page.getByRole('button', { name: 'Files', exact: true }).click()
  await expect(page.locator('.file-panel')).toBeVisible()
  await page.getByRole('button', { name: 'lua5.1.luac: File actions', exact: true }).click()
  await expect(page.getByText('Download Result', { exact: true })).toBeVisible()
  await page.keyboard.press('Escape')
  await page.locator('.file-select').click()
  await expect(page.locator('.file-panel')).not.toBeVisible()
  await page.getByRole('button', { name: 'Settings', exact: true }).click()
  const drawer = page.locator('.n-drawer')
  await expect(drawer).toBeVisible()
  expect((await drawer.boundingBox())!.width).toBeLessThanOrEqual(390)
  await page.keyboard.press('Escape')
  await page.reload()
  await page.getByRole('button', { name: 'Files', exact: true }).click()
  await expect(page.locator('.dialect-tag')).toHaveText('Lua 5.1')
  await page.setViewportSize({ width: 1440, height: 960 })
  await expect(page.locator('.file-row')).toHaveCount(1)
  await expect(page.locator('.file-panel')).toBeVisible()
})

test('welcome, branding and reduced motion fit light, dark and narrow layouts', async ({ page }) => {
  await page.emulateMedia({ reducedMotion: 'reduce' })
  await page.goto('/')
  const logo = page.locator('.brand img')
  expect(await logo.evaluate((img: HTMLImageElement) => img.complete && img.naturalWidth > 0)).toBe(true)
  const favicon = await page.locator('link[rel="icon"]').getAttribute('href')
  expect((await page.request.get(favicon!)).ok()).toBe(true)
  await expect(page.locator('.welcome-content')).toHaveCSS('animation-name', 'none')
  await page.screenshot({ path: resolve(root, 'tmp/web-ui-tests/welcome-light.png'), animations: 'disabled' })
  await page.getByRole('button', { name: 'Dark Mode', exact: true }).click()
  await expect(page.locator('html')).toHaveClass(/dark/)
  await page.screenshot({ path: resolve(root, 'tmp/web-ui-tests/welcome-dark.png'), animations: 'disabled' })
  await page.setViewportSize({ width: 320, height: 740 })
  expect(await page.locator('.app-header').evaluate(el => el.scrollWidth <= el.clientWidth)).toBe(true)
  expect((await page.locator('.brand').boundingBox())!.x + (await page.locator('.brand').boundingBox())!.width).toBeLessThanOrEqual((await page.locator('.header-tools').boundingBox())!.x)
  await page.screenshot({ path: resolve(root, 'tmp/web-ui-tests/mobile.png'), animations: 'disabled' })
})

test('workspace drops, folder imports and empty source files use the same file collection', async ({ page }) => {
  await page.goto('/')
  // The browser supplies filesystem entries for native OS drops. Reproduce that
  // boundary while keeping the production reader, import and decompile paths.
  await page.locator('main').evaluate((target, bytes) => {
    const dataTransfer = new DataTransfer()
    const file = new File([new Uint8Array(bytes)], 'dropped.chunk')
    dataTransfer.items.add(file)
    const original = DataTransferItem.prototype.webkitGetAsEntry
    DataTransferItem.prototype.webkitGetAsEntry = () => ({
      isFile: true, isDirectory: false, file: (callback: (file: File) => void) => callback(file),
    }) as FileSystemEntry
    target.dispatchEvent(new DragEvent('dragover', { bubbles: true, cancelable: true, dataTransfer }))
    target.dispatchEvent(new DragEvent('drop', { bubbles: true, cancelable: true, dataTransfer }))
    DataTransferItem.prototype.webkitGetAsEntry = original
  }, [...readFileSync(resolve(fixtures, 'lua5.1.luac'))])
  await expect(page.locator('.cm-content')).toContainText('browser-test')
  await expect(page.locator('.drop-overlay')).not.toBeVisible()
  const folder = resolve(fixtures, 'folder/nested')
  mkdirSync(folder, { recursive: true })
  writeFileSync(resolve(folder, 'another.chunk'), readFileSync(resolve(fixtures, 'lua5.4.luac')))
  await page.locator('input[webkitdirectory]').setInputFiles(resolve(fixtures, 'folder'))
  await page.getByRole('button', { name: 'OK', exact: true }).click()
  await expect(page.locator('.file-row').filter({ hasText: 'another.chunk' }).locator('.dialect-tag')).toHaveText('Lua 5.4')
  await page.locator('input[type=file]:not([webkitdirectory])').setInputFiles({ name: 'empty.lua', mimeType: 'text/plain', buffer: Buffer.alloc(0) })
  await expect(page.locator('.cm-content')).toBeVisible()
  await expect(page.locator('.cm-content')).toHaveText('')
  await expect(page.locator('.file-row')).toHaveCount(3)
})
