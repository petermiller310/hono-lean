// Bounded whole-router observations. These do not extend baseline D1 or prove
// search reachability, TypeScript loading, engine or native-language adequacy.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

assert.equal(Bun.version, '1.4.0')
const checkout = resolve(Bun.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs, 315)
const { TrieRouter } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/router.ts')).href)
const encode = value => {
  if (value === Object) return { intrinsic: 'Object' }
  if (value === Object.prototype) return { intrinsic: 'Object.prototype' }
  if (typeof value === 'string' || typeof value === 'number' || typeof value === 'boolean' || value === null) return value
  if (value === undefined) return { kind: 'undefined' }
  throw new Error(`Unexpected upstream observed value: ${typeof value}`)
}
const observe = params => ({
  nullPrototype: Object.getPrototypeOf(params) === null,
  entries: Object.getOwnPropertyNames(params).sort().map(name => [name, encode(params[name])]),
  json: JSON.stringify(params)
})
const records = []
const query = (context, router, method, path) => {
  const hits = router.match(method, path)[0]
  records.push({ context, method, path, hits: hits.map(([handler, params]) => ({ handler, params: observe(params) })) })
  return hits
}
const primaryPattern = '/:id/:constructor{[0-9]+}'
const primary = new TrieRouter()
primary.add('GET', primaryPattern, 'get')
primary.add('ALL', primaryPattern, 'all')
const first = query('constructor-second', primary, 'GET', '/alpha/12')
assert.deepEqual(first.map(hit => hit[0]), ['get', 'all'])
for (const [, params] of first) {
  assert.equal(params.id, 'alpha')
  assert.equal(Object.hasOwn(params, 'constructor'), true)
  assert.equal(params.constructor, Object)
  assert.equal(JSON.stringify(params), '{"id":"alpha"}')
}
query('constructor-second-repeat', primary, 'GET', '/alpha/12')
const changed = query('constructor-second-next-query', primary, 'GET', '/beta/34')
assert.equal(changed[0][1].id, 'beta')
assert.equal(first[0][1].id, 'alpha')
assert.notEqual(changed[0][1], first[0][1])
assert.deepEqual(query('all-fallback-post', primary, 'POST', '/gamma/56').map(hit => hit[0]), ['all'])
assert.deepEqual(query('all-fallback-head', primary, 'HEAD', '/delta/78').map(hit => hit[0]), ['all'])
assert.deepEqual(query('regexp-miss', primary, 'GET', '/alpha/no'), [])
assert.deepEqual(query('empty-path', primary, 'GET', ''), [])
assert.deepEqual(query('empty-components', primary, 'POST', '/'), [])

for (const [context, pattern, expected] of [
  ['constructor-first-positive', '/:constructor/:id{[0-9]+}', { constructor: 'alpha', id: '12' }],
  ['ordinary-two-sources', '/:id/:tail{[0-9]+}', { id: 'alpha', tail: '12' }],
  ['same-name-keeps-first', '/:id/:id{[0-9]+}', { id: 'alpha' }]
]) {
  const router = new TrieRouter()
  router.add('GET', pattern, context)
  const hits = query(context, router, 'GET', '/alpha/12')
  assert.equal(hits.length, 1)
  assert.deepEqual(Object.fromEntries(Object.keys(hits[0][1]).map(key => [key, hits[0][1][key]])), expected)
  assert.deepEqual(query(context + '-wrong-method', router, 'POST', '/alpha/12'), [])
  assert.deepEqual(query(context + '-regexp-miss', router, 'GET', '/alpha/no'), [])
}
const empty = new TrieRouter()
assert.deepEqual(query('no-routes', empty, 'GET', '/alpha/12'), [])
assert.deepEqual(query('no-routes-empty-path', empty, 'GET', ''), [])

console.log(JSON.stringify({
  revision, runtime: 'bun', version: Bun.version, checkedPinnedBlobs,
  verified: false, nativeTypeScriptLoadingVerified: false,
  scope: 'Finite pinned TrieRouter observations; constructor capture is not a new baseline divergence or whole-router theorem.',
  primaryPattern, constructorSecondIsObjectFunction: true, constructorJsonOmitted: true,
  reverseOrderPositive: true, repeatedQueriesKeepEarlierReturnedMap: true,
  queryCount: records.length, records
}))
