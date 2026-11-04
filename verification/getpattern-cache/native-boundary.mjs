// Native-only future cache frontier. Run once per fresh Bun process/order.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

assert.equal(typeof Bun, 'object')
assert.equal(Bun.version, '1.4.0')
const checkout = resolve(process.argv[2])
const order = process.argv[3]
assert(['plain-first', 'invalid-first'].includes(order))
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
const source = readFileSync(resolve(checkout, 'src/utils/url.ts'))
const sourceSha256 = createHash('sha256').update(source).digest('hex')
assert.equal(sourceSha256, 'd1f85f414ed8fd3682000499e74e8723139810fd612e1e1a1b4075a52ef91248')
const cacheBlockSha256 = createHash('sha256').update(source.subarray(1461, 1901)).digest('hex')
assert.equal(cacheBlockSha256, '6708db3236d21830f5b739727a68a100a8125297ee4deb25c5f4b3bcea77ab18')
// No prior Hono module is imported in this process. Bun's TS loading is unverified.
const { getPattern } = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
const plainLabel = ':id', plainNext = '{(}#undefined', invalidLabel = ':id#{(}'
const expectedRawKey = ':id#{(}#undefined'
assert.equal(`${plainLabel}#${plainNext}`, expectedRawKey)
assert.equal(`${invalidLabel}#${undefined}`, expectedRawKey)
let observations
if (order === 'plain-first') {
  const first = getPattern(plainLabel, plainNext)
  const second = getPattern(invalidLabel)
  assert.deepEqual(first, [':id', 'id', true])
  assert.deepEqual(second, [':id', 'id', true])
  assert.equal(first, second)
  observations = { first, second, sameIdentity: first === second }
} else {
  let first
  try { first = { ok: true, result: getPattern(invalidLabel) } }
  catch (error) { first = { ok: false, errorName: error.name } }
  assert.deepEqual(first, { ok: false, errorName: 'SyntaxError' })
  const second = getPattern(plainLabel, plainNext)
  assert.deepEqual(second, [':id', 'id', true])
  observations = { first, second }
}
console.log(JSON.stringify({
  id: 'GETPATTERN-RAW-CACHE-COLLISION-1', revision,
  runtime: 'bun', version: Bun.version, checkedPinnedBlobs, sourceSha256,
  cacheBlockBytes: 440, cacheBlockSha256, order, expectedRawKey,
  cacheKeyNativeObserved: false, freshProcessRequired: true,
  verified: false, nativeOnly: true, nativeTypeScriptLoadingVerified: false,
  formalCacheTheorem: null, baselineAllowlistChanged: false, observations,
  scope: 'Actual pinned getPattern in a fresh Bun process. Raw key equality is an independent source-formula expectation; private cache storage is not instrumented. Finite values/identity/error outcomes only. No cache/cold-regex/full-router/native-frontend adequacy theorem or D1 compatibility allowance.'
}))
