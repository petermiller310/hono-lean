// Finite source-pinned observations for the trust/divergence ledger. No server
// is started: app.request invokes Hono locally, without network fetches.
import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const root = resolve(import.meta.dir, '..')
const arguments_ = Bun.argv.slice(2)
assert(arguments_.length === 2 && arguments_[0] === '--hono',
  'Usage: bun verification/trust_probe.ts --hono /path/to/clean/pinned/hono')
const checkout = resolve(arguments_[1])
const target = await Bun.file(resolve(root, 'verification/target.json')).json()
const baseline = await Bun.file(resolve(root, 'comparison/baseline.json')).json()
assert.equal(target.revision, pin)
assert.equal(baseline.revision, pin)
assert.equal(Bun.version, baseline.bunVersion, 'Use the pinned Bun runtime')

function git(...arguments_: string[]): string {
  const result = spawnSync('git', ['-C', checkout, ...arguments_], { encoding: 'utf8' })
  assert.equal(result.status, 0, result.stderr || 'Git command failed')
  return result.stdout
}
assert.equal(git('rev-parse', 'HEAD').trim(), pin, 'Wrong upstream revision')
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '',
  'Upstream checkout must be clean; this probe never changes it')
assert.equal(git('rev-parse', '--show-object-format').trim(), 'sha1')
// Porcelain alone misses assume-unchanged/skip-worktree edits. Check actual
// package/source bytes against every pinned blob before dynamic source imports.
const blobs = git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)
for (const entry of blobs) {
  const tab = entry.indexOf('\t')
  const [mode, kind, expected] = entry.slice(0, tab).split(' ')
  const path = entry.slice(tab + 1)
  assert(kind === 'blob' && (mode === '100644' || mode === '100755'), path)
  const bytes = Buffer.from(await Bun.file(resolve(checkout, path)).arrayBuffer())
  const actual = createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
  assert.equal(actual, expected, `Worktree differs from pinned source: ${path}`)
}

const upstream = (path: string) => import(pathToFileURL(resolve(checkout, path)).href)
const { Hono } = await upstream('src/hono.ts')
const { TrieRouter } = await upstream('src/router/trie-router/router.ts')
const { SmartRouter } = await upstream('src/router/smart-router/router.ts')
const { RegExpRouter } = await upstream('src/router/reg-exp-router/router.ts')
const { splitPath } = await upstream('src/utils/url.ts')
const observations: Record<string, unknown> = {}
const recorded = (value: Record<string, unknown>) => ({ runtime: `Bun ${Bun.version}`, ...value })

// Preserve own keys and JSON value types; do not silently omit undefined.
function own(value: unknown): unknown {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return value
  if (typeof value === 'number' && Number.isFinite(value)) return value
  if (Array.isArray(value)) return value.map(own)
  if (typeof value === 'object') return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, own(v)]))
  throw new Error(`Unexpected non-JSON observation: ${typeof value}`)
}

const captures = (name: string) => {
  const router = new TrieRouter()
  router.add('GET', `/:${name}`, 'capture')
  return router.match('GET', '/alpha')
}
const d1 = captures('__proto__')
const params = d1[0][0][1]
observations.D1 = recorded({ observedRaw: own(d1), ownKeys: Object.keys(params),
  captureType: typeof params.__proto__, outputParamsHaveNullPrototype: Object.getPrototypeOf(params) === null })
const controls = ['id', 'constructor'].map(name => ({ name, observedRaw: own(captures(name)) }))
const temporary: Record<string, unknown> = {}
temporary.__proto__ = 'alpha'
assert.equal(Object.hasOwn(temporary, '__proto__'), false)
assert.equal(temporary.__proto__, Object.prototype)

const app = new Hono()
const beforeName = app.router.name
app.get('/page', (c: any) => { c.header('X-Method', c.req.method); return c.text('body') })
const head = await app.request('http://hono-lean.invalid/page', { method: 'HEAD' })
const rawHead = new TrieRouter()
rawHead.add('GET', '/page', 'read')
observations['LAYER-HEAD'] = recorded({ appStatus: head.status, appBodyText: await head.text(),
  appBodyWasNull: head.body === null, methodSeenByHandler: head.headers.get('X-Method'),
  GETOnlyRawTrieHEADResult: own(rawHead.match('HEAD', '/page')) })
observations['LAYER-DEFAULT-ROUTER'] = recorded({ beforeName, afterSimpleRequestName: app.router.name })

const smart = new SmartRouter({ routers: [new RegExpRouter(), new TrieRouter()] })
smart.add('GET', '/a', 'a')
smart.match('GET', '/a')
let smartError = ''
try { smart.add('GET', '/b', 'b') } catch (error) {
  assert(error instanceof Error)
  smartError = error.message
}
const trie = new TrieRouter()
trie.add('GET', '/a', 'a')
trie.match('GET', '/a')
trie.add('GET', '/b', 'b')
observations['LIFECYCLE-SMARTROUTER'] = recorded({ smartError, rawTrieAfterAppend: own(trie.match('GET', '/b')) })

const optional = new TrieRouter()
optional.add('GET', '/animals/:type?', 'optional')
const regexp = new TrieRouter()
regexp.add('GET', '/:id{[0-9]+}', 'digits')
observations['SYNTAX-OPTIONAL-REGEXP'] = recorded({ optionalPattern: '/animals/:type?',
  without: own(optional.match('GET', '/animals')), with: own(optional.match('GET', '/animals/cat')),
  regexpPattern: '/:id{[0-9]+}', regexpMatch: own(regexp.match('GET', '/123')),
  regexpMiss: own(regexp.match('GET', '/alpha')) })
const duplicate = new TrieRouter()
duplicate.add('GET', '/:id/:id', 'duplicate')
observations['SYNTAX-DUPLICATE-NAMES'] = recorded({ method: 'GET', pattern: '/:id/:id', path: '/alpha/beta',
  result: own(duplicate.match('GET', '/alpha/beta')) })
observations['LAYER-PATH-REPRESENTATION'] = recorded({ cases:
  ['', '/', '//a', '/a/', '/é', '/a%2Fb'].map(input => ({ input, output: splitPath(input) })) })

const lower = new Hono()
lower.on('get', '/lower', (c: any) => c.text('lower'))
const lowerResponse = await lower.request('http://hono-lean.invalid/lower')
observations['LAYER-REGISTRATION-METHOD'] = recorded({ inputMethod: 'get', storedMethod: lower.routes[0].method,
  responseStatus: lowerResponse.status, responseBody: await lowerResponse.text() })

const trace: string[] = []
const middle = new Hono()
middle.use('*', async (_c: unknown, next: () => Promise<void>) => {
  trace.push('before'); await next(); trace.push('after')
})
middle.get('/trace', (c: any) => { trace.push('handler'); return c.text('ok') })
const traceResponse = await middle.request('http://hono-lean.invalid/trace')
const repeated = new Hono()
repeated.onError((error: Error, c: any) => c.text(error.message, 500))
repeated.use('*', async (_c: unknown, next: () => Promise<void>) => { await next(); await next() })
repeated.get('/trace', (c: any) => c.text('ok'))
const repeatedResponse = await repeated.request('http://hono-lean.invalid/trace')
observations['LAYER-HANDLER-EFFECTS'] = recorded({ trace, responseStatus: traceResponse.status,
  repeatedNextStatus: repeatedResponse.status, repeatedNextBody: await repeatedResponse.text() })

const ledger = await Bun.file(resolve(root, 'verification/divergences.json')).json()
assert.equal(ledger.targetRevision, pin)
const runtimeRows = ledger.entries.filter((entry: any) => entry.evidence.runtimeObservation !== null)
assert.deepEqual(Object.keys(observations).sort(), runtimeRows.map((entry: any) => entry.id).sort())
for (const entry of runtimeRows) {
  assert.deepEqual(observations[entry.id], entry.evidence.runtimeObservation, entry.id)
}
assert.deepEqual(controls, ledger.entries.find((entry: any) => entry.id === 'D1').controls, 'D1 controls')
console.log(JSON.stringify({ revision: pin, runtime: Bun.version, checkedPinnedBlobs: blobs.length,
  evidence: 'finite native observations; not a universal source proof',
  checkedLedgerRows: runtimeRows.length, observations, controls }, null, 2))
