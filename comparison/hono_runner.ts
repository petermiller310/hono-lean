import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const { TrieRouter } = await import(pathToFileURL(resolve(process.argv[2], 'src/router/trie-router/router.ts')).href)
const scenarios = JSON.parse(await Bun.stdin.text())

// Copy own entries only, preserving every value. JSON.stringify alone would
// silently omit undefined captures, so unsupported values must fail instead.
function own(value: unknown): unknown {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return value
  if (typeof value === 'number' && Number.isFinite(value)) return value
  if (Array.isArray(value)) return value.map(own)
  if (typeof value === 'object') return Object.fromEntries(Object.entries(value).map(([key, item]) => [key, own(item)]))
  throw new Error(`Hono returned a non-JSON value: ${typeof value}`)
}

function normalize(raw: any): any[] {
  if (!Array.isArray(raw) || raw.length !== 1 || !Array.isArray(raw[0])) throw new Error('Unexpected TrieRouter result shape')
  return raw[0].map(([payload, params]: any) => ({
    registration: payload.registration,
    handler: payload.handler,
    params: own(params),
  }))
}

const outputs = scenarios.map((scenario: any) => {
  try {
    const router = new TrieRouter()
    let next = 0
    const add = (route: any) => {
      const registration = next++
      router.add(route.method, route.pattern, { registration, handler: route.handler })
      return { registration }
    }
    for (const route of scenario.routes) add(route)
    const retained: { raw: any; before: any }[] = []
    const results = scenario.steps.map((step: any) => {
      if (step.op === 'register') return add(step.route)
      const raw = router.match(step.request.method, step.request.path)
      const before = normalize(raw)
      retained.push({ raw, before })
      return { matches: before }
    })
    return { results, nextRegistration: next,
      retained: retained.map(({ raw, before }) => ({ before, after: normalize(raw) })) }
  } catch (error) {
    return { runnerError: String(error) }
  }
})
process.stdout.write(JSON.stringify(outputs))
