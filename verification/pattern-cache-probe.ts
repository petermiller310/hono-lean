// A finite exported-utility/router sharing observation, not a source theorem.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
const checkout = resolve(Bun.argv[2])
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(Bun.version, '1.4.0')
assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
}
const { getPattern } = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
const { TrieRouter } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/router.ts')).href)
const label = ':scopeAlias'
const first = getPattern(label)
assert(Array.isArray(first))
const shared = first === getPattern(label)
const originalName = first[1]
first[1] = 'renamed'
const repeated = getPattern(label)
assert(Array.isArray(repeated))
const renamedCacheName = repeated[1]
const router = new TrieRouter()
router.add('GET', '/' + label, 'alias')
const renamedRaw = router.match('GET', '/alpha')
let reads = 0
Object.defineProperty(first, '1', { configurable: true, enumerable: true,
  get() { reads++; return 'getterName' } })
const getterRouter = new TrieRouter()
getterRouter.add('GET', '/' + label, 'getter')
const getterReadsAfterAdd = reads
const getterRaw = getterRouter.match('GET', '/beta')
const getterReadsAfterMatch = reads
const existingRawAfterMutation = router.match('GET', '/alpha')
const existingParams = existingRawAfterMutation[0][0][1]
console.log(JSON.stringify({ runtime: Bun.version, revision: pin, cachedArrayShared: shared,
  originalName, renamedCacheName, renamedRaw, getterReadsAfterAdd, getterReadsAfterMatch, getterRaw,
  existingRawAfterMutation, existingOwnKeys: Object.keys(existingParams),
  existingRenamedIsUndefined: Object.hasOwn(existingParams, 'renamed') && existingParams.renamed === undefined,
  sameCachedArrayAfterGetter: first === getPattern(label) }))
