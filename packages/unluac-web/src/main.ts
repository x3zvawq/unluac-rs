import { createPinia } from 'pinia'
import { createApp, watchEffect } from 'vue'
import { restoreFromUrl } from '@/composables/useShareUrl'
import App from './App.vue'
import { i18n } from './i18n'
import '@/styles/main.css'

const app = createApp(App)

app.use(createPinia())
app.use(i18n)
watchEffect(() => {
  document.documentElement.lang = i18n.global.locale.value
})

// 从 URL query params 恢复设置（如有）
restoreFromUrl()

app.mount('#app')
