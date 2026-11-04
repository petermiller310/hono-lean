// Planned-frontier observations only. No formal source connection, proof or
// native-language adequacy claim; this does not change the existing baseline D1.
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
const nodeBytes = readFileSync(resolve(checkout, 'src/router/trie-router/node.ts'))
const source = nodeBytes.toString('utf8').match(/[^\n]*\n|[^\n]+$/g)[155]
const sourceSha256 = createHash('sha256').update(source).digest('hex')
assert.equal(source, '            const m = matcher.exec(restPathString)\n')
assert.equal(sourceSha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
const { getPattern } = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)

// Distinct names isolate cache entries. Undefined and its string spelling
// nevertheless produce the same label#next cache key within each pair.
const terminalLabel = ':frontierTerminalFirst{[0-9]+}'
const terminal = getPattern(terminalLabel, undefined)
const terminalAgain = getPattern(terminalLabel, 'undefined')
assert.equal(terminal, terminalAgain)
assert.equal(terminal[2], terminalAgain[2])
assert.equal(terminal[2].source, '^[0-9]+$')
assert.equal(terminal[2].exec('12')?.[0], '12')
assert.equal(terminal[2].exec('12/undefined'), null)
const lookaheadLabel = ':frontierLookaheadFirst{[0-9]+}'
const lookahead = getPattern(lookaheadLabel, 'undefined')
const lookaheadAgain = getPattern(lookaheadLabel, undefined)
assert.equal(lookahead, lookaheadAgain)
assert.equal(lookahead[2], lookaheadAgain[2])
assert.equal(lookahead[2].source, '^[0-9]+(?=\\/undefined)')
assert.equal(lookahead[2].exec('12'), null)
assert.equal(lookahead[2].exec('12/undefined')?.[0], '12')

const malformedLabel = ':frontierMalformedNext{[0-9]+}'
let malformedError
try {
  getPattern(malformedLabel, '(')
  assert.fail('Expected malformed generated regex to throw')
} catch (error) {
  assert(error instanceof SyntaxError)
  malformedError = error.name
}
const recovery = getPattern(malformedLabel, undefined)
assert.equal(recovery[2].source, '^[0-9]+$')

// Exact line156 is already plain JavaScript. This manual observation wrapper
// adds return m; it performs no TS erasure. Bun loading upstream TS is separate
// unverified tooling. All mutations below are process-local native objects.
const mutableLabel = ':frontierCurrentExec{[0-9]+}'
const mutable = getPattern(mutableLabel)
const mutableAgain = getPattern(mutableLabel)
const matcher = mutable[2], events = [], sentinel = ['custom-result']
matcher.exec = function (input) {
  events.push({ sameReceiver: this === matcher, input })
  return sentinel
}
const invoke = new Function('matcher', 'restPathString', source + '\nreturn m')
assert.equal(invoke(mutableAgain[2], 'not-digits'), sentinel)
assert.deepEqual(events, [{ sameReceiver: true, input: 'not-digits' }])
matcher.exec = 0
assert.throws(() => invoke(matcher, '12'), TypeError)

console.log(JSON.stringify({
  revision, runtime: 'bun', version: Bun.version, checkedPinnedBlobs,
  verified: false, plannedFrontier: true,
  nativeTypeScriptLoadingVerified: false, manualFragmentWrapperVerified: false,
  source156: { bytes: Buffer.byteLength(source), sha256: sourceSha256 },
  boundaries: {
    cacheOrder: [
      { firstNext: { kind: 'undefined' }, secondNext: 'undefined',
        cacheKey: terminalLabel + '#undefined', tupleKey: terminal[0],
        source: terminal[2].source, sameTuple: terminal === terminalAgain, sameMatcher: terminal[2] === terminalAgain[2],
        match12: '12', match12SlashUndefined: null },
      { firstNext: 'undefined', secondNext: { kind: 'undefined' },
        cacheKey: lookaheadLabel + '#undefined', tupleKey: lookahead[0],
        source: lookahead[2].source, sameTuple: lookahead === lookaheadAgain, sameMatcher: lookahead[2] === lookaheadAgain[2],
        match12: null, match12SlashUndefined: '12' }
    ],
    malformedNext: { next: '(', error: malformedError, recoverySource: recovery[2].source },
    currentExec: { sameTuple: mutable === mutableAgain, sameMatcher: matcher === mutableAgain[2],
      events, returned: sentinel, noncallableThrowsWithoutBuiltinFallback: true }
  },
  scope: 'Finite native-only planned-frontier evidence; no source/proof/native adequacy claim and no baseline D1 change.'
}))
