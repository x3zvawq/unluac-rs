import { createI18n } from 'vue-i18n'
import deDE from './de-DE.json'
import enUS from './en-US.json'
import esES from './es-ES.json'
import frFR from './fr-FR.json'
import jaJP from './ja-JP.json'
import koKR from './ko-KR.json'
import ptBR from './pt-BR.json'
import ruRU from './ru-RU.json'
import zhCN from './zh-CN.json'
import zhTW from './zh-TW.json'

const SUPPORTED_LOCALES = [
  'zh-CN',
  'zh-TW',
  'en-US',
  'ja-JP',
  'ko-KR',
  'ru-RU',
  'es-ES',
  'pt-BR',
  'fr-FR',
  'de-DE',
] as const

/** 语言前缀 → 默认完整 locale 的映射 */
const PREFIX_MAP: Record<string, string> = {
  zh: 'zh-CN',
  en: 'en-US',
  ja: 'ja-JP',
  ko: 'ko-KR',
  ru: 'ru-RU',
  es: 'es-ES',
  pt: 'pt-BR',
  fr: 'fr-FR',
  de: 'de-DE',
}

function detectLocale(): string {
  const saved = localStorage.getItem('unluac-locale')
  if (saved && (SUPPORTED_LOCALES as readonly string[]).includes(saved)) return saved

  // 完整匹配 → 前缀匹配 → 默认英语
  // zh-TW 由完整匹配命中，前缀 zh 默认回退到 zh-CN
  const nav = navigator.language
  if ((SUPPORTED_LOCALES as readonly string[]).includes(nav)) return nav
  const prefix = nav.split('-')[0]
  return PREFIX_MAP[prefix] ?? 'en-US'
}

export const i18n = createI18n({
  legacy: false,
  locale: detectLocale(),
  fallbackLocale: 'en-US',
  messages: {
    'zh-CN': zhCN,
    'zh-TW': zhTW,
    'en-US': enUS,
    'ja-JP': jaJP,
    'ko-KR': koKR,
    'ru-RU': ruRU,
    'es-ES': esES,
    'pt-BR': ptBR,
    'fr-FR': frFR,
    'de-DE': deDE,
  },
})
