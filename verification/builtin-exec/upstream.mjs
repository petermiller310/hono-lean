// Finite constructor/cache/tuple and whole pinned-router observations. These
// do not establish those source connections or full TrieRouter/native adequacy.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

assert.equal(Bun.version, '1.4.0')
const checkout = resolve(Bun.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(git('rev-parse', 'HEAD').trim(), revision); assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), entry.slice(0, tab).split(' ')[2]); checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs, 315)
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url))), bytes = readFileSync(resolve(checkout, metadata.sourcePath))
const source = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8'), span = metadata.fragments.full
const sha = value => createHash('sha256').update(value).digest('hex')
assert.equal(metadata.revision, revision); assert.equal(sha(bytes), metadata.sourceSha256); assert.equal(sha(source), span.sha256)
assert.equal(span.sha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(bytes.subarray(span.startByte, span.endByteExclusive).toString(), source)
const { getPattern } = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
const { TrieRouter } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/router.ts')).href)
const units = value => Array.from({ length: value.length }, (_, index) => value.charCodeAt(index))
const profiles = [
  { name: 'rangeDigits', raw: '[0-9]+', hit: '12', cases: [['12', true], ['0', true], ['', false], ['12\n', false], ['１２', false], ['\ud800', false]] },
  { name: 'rangeLetters', raw: '[A-z]+', hit: 'Az', cases: [['Az', true], ['[\\]^_`', true], ['', false], ['09', false], ['é', false], ['\r\n', false]] },
  { name: 'rangePunctuation', raw: '[9-A]+', hit: '9:@A', cases: [['9:@A', true], ['@', true], ['', false], ['8', false], ['B', false], ['\ud800', false]] }
]
const matcherRecords = [], routerRecords = []
for (const profile of profiles) {
  const label = `:${profile.name}{${profile.raw}}`, tuple = getPattern(label), repeated = getPattern(label)
  assert.equal(tuple, repeated); assert.equal(tuple[2], repeated[2])
  assert.equal(tuple[0], label); assert.equal(tuple[1], profile.name)
  const matcher = tuple[2]
  assert(matcher instanceof RegExp); assert.equal(matcher.source, '^' + profile.raw + '$'); assert.equal(matcher.flags, '')
  for (const [index, [input, expected]] of profile.cases.entries()) {
    const lastIndex = [-7, 0, 17, Number.MAX_SAFE_INTEGER][index % 4]
    matcher.lastIndex = lastIndex
    const first = matcher.exec(input), second = matcher.exec(input)
    assert.equal(first !== null, expected); assert.equal(second !== null, expected); assert.equal(matcher.lastIndex, lastIndex)
    if (expected) {
      assert.equal(first[0], input); assert.equal(first.length, 1); assert.equal(first.index, 0); assert.equal(first.input, input)
      assert.equal(Object.hasOwn(first, 'groups'), true); assert.equal(first.groups, undefined); assert.notEqual(first, second)
    }
    matcherRecords.push({ label, source: matcher.source, flags: matcher.flags, input: units(input), matched: first ? units(first[0]) : null,
      lastIndex, lastIndexKept: matcher.lastIndex === lastIndex, freshOnRepeatedHit: expected ? first !== second : null, sameCachedTuple: tuple === repeated })
  }
  const router = new TrieRouter(), route = `/:id/${label}`
  router.add('GET', route, 'get'); router.add('ALL', route, 'all')
  for (const [method, tail, expectedHandlers] of [
    ['GET', profile.hit, ['get', 'all']], ['POST', profile.hit, ['all']], ['GET', profile.hit, ['get', 'all']],
    ['GET', profile.hit + '\n', []], ['GET', '', []]
  ]) {
    const path = '/alpha/' + tail, hits = router.match(method, path)[0]
    assert.deepEqual(hits.map(hit => hit[0]), expectedHandlers)
    const observed = hits.map(([handler, params]) => {
      assert.equal(Object.getPrototypeOf(params), null); assert.equal(params.id, 'alpha'); assert.equal(params[profile.name], tail)
      return { handler, nullPrototype: true, entries: Object.keys(params).sort().map(key => [key, units(params[key])]) }
    })
    routerRecords.push({ route, method, path: units(path), hits: observed })
  }
}
console.log(JSON.stringify({ revision, runtime: 'bun', version: Bun.version, checkedPinnedBlobs, verified: false, nativeTypeScriptLoadingVerified: false,
  sourceSha256: sha(source), matcherQueryCount: matcherRecords.length, routerQueryCount: routerRecords.length, matcherRecords, routerRecords,
  scope: 'Finite actual getPattern and TrieRouter evidence; constructor/cache/tuple/frontend/native links and full regex/search remain proof obligations. No baseline D1 change.' }))
