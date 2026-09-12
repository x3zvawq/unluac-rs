import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { chromium } from 'playwright'
import { site } from '../src/content/site.ts'

// This is an authored preview asset. Regenerate it when the logo or branding changes.
const logo = readFileSync(resolve(import.meta.dirname, '../../../logo.svg')).toString('base64')
const browser = await chromium.launch({ channel: process.env.PLAYWRIGHT_CHANNEL })
try {
  const page = await browser.newPage({ viewport: { width: 1200, height: 630 }, deviceScaleFactor: 1 })
  await page.setContent(`<!doctype html><html><head><meta charset="utf-8"><style>
    * { box-sizing: border-box; } body { margin: 0; font-family: Arial, sans-serif; color: #e5e9ff; background: #171c3d; }
    main { width: 1200px; height: 630px; padding: 64px 76px; position: relative; overflow: hidden; }
    .orbit { position: absolute; width: 700px; height: 700px; border: 1px solid #343d5f; border-radius: 50%; right: -300px; top: -230px; }
    .brand { display: flex; align-items: center; gap: 20px; font-size: 30px; font-weight: 700; }
    img { width: 72px; height: 72px; } h1 { font-size: 76px; line-height: 1.1; letter-spacing: -3px; margin: 44px 0 26px; }
    h1 span { color: #83e8cf; } p { font-size: 24px; color: #b5c1e5; margin: 0; }
    footer { position: absolute; bottom: 58px; left: 76px; right: 76px; display: flex; justify-content: space-between; padding-top: 24px; border-top: 1px solid #343d5f; font-size: 18px; color: #b5c1e5; }
  </style></head><body><main><div class="orbit"></div>
    <div class="brand"><img src="data:image/svg+xml;base64,${logo}" alt="">${site.name}</div>
    <h1>Lua bytecode,<br><span>made readable.</span></h1>
    <p>Lua 5.1–5.5 · LuaJIT · Luau</p>
    <footer><span>Browser · CLI · Rust · JavaScript</span><span>${new URL(site.url).hostname}</span></footer>
  </main></body></html>`)
  await page.locator('img').evaluate(image => image.decode())
  const path = resolve(import.meta.dirname, '../public/social-card.png')
  await page.screenshot({ path })
  console.log(path)
} finally {
  await browser.close()
}
