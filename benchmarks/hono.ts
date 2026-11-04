import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const { TrieRouter } = await import(pathToFileURL(resolve(process.argv[2], 'src/router/trie-router/router.ts')).href)
const input = JSON.parse(await Bun.stdin.text())
const { warmupSamples, samples, buildIterations, lookupIterations } = input.config
const now = () => process.hrtime.bigint()

function build(routes: any[]) {
  const router = new TrieRouter()
  routes.forEach((r, registration) => router.add(r.method, r.pattern, { registration, handler: r.handler }))
  return router
}

function normalize(raw: any): any[] {
  return raw[0].map(([payload, params]: any) => ({ ...payload, params: Object.fromEntries(
    Object.entries(params).map(([key, value]) => {
      if (typeof value !== 'string') throw new Error(`Non-string benchmark capture: ${typeof value}`)
      return [key, value]
    })) }))
}

// This small liveness sink is timed for lookup, not JSON normalization/equality.
function digest(raw: any): number {
  let sum = 0
  for (const [payload, params] of raw[0]) {
    const keys = Object.keys(params)
    sum = (sum + payload.registration + payload.handler.length + keys.length + 1) >>> 0
    for (const key of keys) sum = (sum + key.length + params[key].length) >>> 0
  }
  return sum
}

function measure(sample: (offset: number) => any) {
  for (let i = 0; i < warmupSamples; i++) sample(i)
  return Array.from({ length: samples }, (_, i) => sample(warmupSamples + i))
}

const output = input.workloads.map((w: any) => {
  const lookup = (router: any, index: number) => {
    const q = w.requests[index % w.requests.length]
    return router.match(q.method, q.path)
  }
  if (input.mode === 'validate') return { name: w.name,
    observations: w.banks.map((bank: any) => {
      const router = build(bank.routes)
      return w.requests.map((_: any, index: number) => normalize(lookup(router, index)))
    }) }
  if (input.mode !== 'measure') throw new Error('Expected validate or measure mode')
  const router = build(w.banks[0].routes)
  return { name: w.name, build: measure(offset => {
    const roots: any[] = []
    const start = now()
    for (let i = 0; i < buildIterations; i++) roots.push(build(w.banks[(offset + i) % w.banks.length].routes))
    const nanos = Number(now() - start)
    let checksum = 0
    for (const root of roots) checksum = (checksum + digest(lookup(root, 0))) >>> 0
    return { nanos, checksum }
  }), lookup: measure(offset => {
    let checksum = 0
    const start = now()
    for (let i = 0; i < lookupIterations; i++) checksum = (checksum + digest(lookup(router, offset + i))) >>> 0
    return { nanos: Number(now() - start), checksum }
  }) }
})
process.stdout.write(JSON.stringify(output))
