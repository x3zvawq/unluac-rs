import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { expect, test } from '@playwright/test'
import { site } from '../../src/content/site'

test('initial HTML exposes product content, metadata and links without JavaScript', async ({ browser, baseURL }) => {
  const context = await browser.newContext({ javaScriptEnabled: false })
  const page = await context.newPage()
  const response = await page.goto(baseURL!)
  expect(response!.status()).toBe(200)
  const raw = await response!.text()
  expect(raw).toContain('unluac-cli -i sample.luac -o recovered.lua')
  await expect(page.getByRole('heading', { level: 1 })).toHaveText('Online Lua Decompiler')
  await expect(page.getByRole('heading', { name: 'A Lua decompiler for your browser and your tools' })).toBeVisible()
  await expect(page.locator('title')).toHaveCount(1)
  await expect(page).toHaveTitle(site.title)
  await expect(page.locator('link[rel="canonical"]')).toHaveAttribute('href', site.url)
  await expect(page.locator('meta[name="description"]')).toHaveAttribute('content', site.description)
  await expect(page.locator('meta[name="robots"]')).not.toHaveAttribute('content', /noindex/)
  await expect(page.getByRole('link', { name: 'Command-line decompiler' })).toHaveAttribute('href', `${site.repository}/releases`)
  await page.getByText('Which files can I decompile?', { exact: true }).click()
  await expect(page.locator('details[open]')).toContainText('detection uses the file contents')
  const graph = JSON.parse((await page.locator('script[type="application/ld+json"]').textContent())!)
  expect(graph['@graph'].map((node: any) => node['@type'])).toEqual(['WebSite', 'SoftwareSourceCode'])
  expect(graph['@graph'][1].codeRepository).toBe(site.repository)
  const imageResponse = await page.request.get('/social-card.png')
  expect(imageResponse.ok()).toBe(true)
  const png = await imageResponse.body()
  expect(png.readUInt32BE(16)).toBe(1200)
  expect(png.readUInt32BE(20)).toBe(630)
  const robots = await page.request.get('/robots.txt')
  expect(await robots.text()).toContain(`Sitemap: ${site.url}sitemap.xml`)
  const sitemap = await page.request.get('/sitemap.xml')
  expect(await sitemap.text()).toContain(`<loc>${site.url}</loc>`)
  await page.screenshot({ path: resolve(import.meta.dirname, '../../../../tmp/web-ui-tests/no-javascript.png'), fullPage: true })
  await context.close()
})

test('rendered product copy matches initial HTML and retains the repository entry point', async ({ page }) => {
  const workers: string[] = []
  page.on('worker', worker => workers.push(worker.url()))
  await page.goto('/')
  await expect(page.locator('.welcome-content')).toBeVisible()
  await expect(page.locator('.welcome-repository')).toHaveAttribute('href', site.repository)
  const initial = readFileSync(resolve(import.meta.dirname, '../../src/content/product.en.html'), 'utf8')
  const rendered = await page.locator('.product-overview').evaluate(el => el.outerHTML)
  // Browser HTML serialization may normalize whitespace; compare the actual text and links.
  const expected = await page.evaluate(html => {
    const doc = new DOMParser().parseFromString(html, 'text/html')
    return doc.body.textContent!.replace(/\s+/g, ' ').trim()
  }, initial)
  const actual = await page.locator('.product-overview').textContent()
  expect(actual!.replace(/\s+/g, ' ').trim()).toBe(expected)
  expect(rendered).toContain('https://www.npmjs.com/package/unluac-js')
  expect(workers).toEqual([])
})
