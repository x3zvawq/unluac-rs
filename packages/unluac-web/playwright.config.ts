import { defineConfig } from '@playwright/test'

export default defineConfig({
  testDir: './tests/browser',
  outputDir: '../../tmp/web-ui-tests/results',
  fullyParallel: false,
  workers: 1,
  use: {
    baseURL: process.env.WEB_TEST_URL ?? 'http://127.0.0.1:4178',
    locale: 'en-US',
    viewport: { width: 1440, height: 960 },
    launchOptions: { channel: process.env.PLAYWRIGHT_CHANNEL },
    screenshot: 'only-on-failure',
    trace: 'retain-on-failure',
  },
  webServer: process.env.WEB_TEST_URL ? undefined : {
    command: 'npm run preview -- --host 127.0.0.1 --port 4178 --strictPort',
    url: 'http://127.0.0.1:4178',
    reuseExistingServer: !process.env.CI,
  },
})
