// Native-only boundaries around ordinary member invocation. These observations
// do not enlarge the admitted method/argument grammar, establish RegExp
// semantics, or assign partial failure states to the Except-based model.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
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
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const bytes = readFileSync(resolve(checkout, metadata.sourcePath)), span = metadata.fragments.full
const source = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
const sha = value => createHash('sha256').update(value).digest('hex')
assert.equal(metadata.revision, revision)
assert.equal(sha(bytes), metadata.sourceSha256)
assert.equal(sha(source), span.sha256)
assert.equal(span.sha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(bytes.subarray(span.startByte, span.endByteExclusive).toString(), source)
// The original line is plain JS and is pasted unchanged. Only the return below
// is fixture observation code; no TS erasure is used.
const invoke = new Function('matcher', 'restPathString', '"use strict";\n' + source + '\nreturn m')

const getterEvents = []
const getterTarget = Object.defineProperty({}, 'exec', { get() {
  getterEvents.push('get-exec')
  return function (input) { getterEvents.push('call'); assert.equal(this, getterTarget); return input }
} })
assert.equal(invoke(getterTarget, 'input'), 'input')
assert.deepEqual(getterEvents, ['get-exec', 'call'])
const proxyEvents = []
const proxyTarget = { exec(input) { proxyEvents.push('call'); assert.equal(this, proxy); return input } }
const proxy = new Proxy(proxyTarget, { get(target, key, receiver) {
  proxyEvents.push('get:' + String(key)); return Reflect.get(target, key, receiver)
} })
assert.equal(invoke(proxy, 'input'), 'input')
assert.deepEqual(proxyEvents, ['get:exec', 'call'])

// This argument assignment is OUTSIDE admitted source156's argument grammar.
// Native member-call evaluation nevertheless saves the old function before it.
const duringEvents = []
const changing = { exec(input) { duringEvents.push('old'); assert.equal(this, changing); return input } }
function next(input) { duringEvents.push('new'); assert.equal(this, changing); return input }
const during = changing.exec((duringEvents.push('argument-write'), changing.exec = next, 'first'))
assert.equal(during, 'first')
assert.deepEqual(duringEvents, ['argument-write', 'old'])
assert.equal(invoke(changing, 'second'), 'second')
assert.deepEqual(duringEvents, ['argument-write', 'old', 'new'])

const noncallableEvents = []
assert.throws(() => ({ exec: 0 }).exec((noncallableEvents.push('argument'), 'input')), TypeError)
assert.deepEqual(noncallableEvents, ['argument'])
const nullEvents = []
assert.throws(() => (null).exec((nullEvents.push('argument'), 'input')), TypeError)
assert.deepEqual(nullEvents, [])
const getterThrowEvents = []
const throwingGetter = Object.defineProperty({}, 'exec', { get() { getterThrowEvents.push('get'); throw new Error('getter') } })
assert.throws(() => throwingGetter.exec((getterThrowEvents.push('argument'), 'input')), Error)
assert.deepEqual(getterThrowEvents, ['get'])

// A native failure may retain earlier effects. Main finite failures deliberately
// expose only {ok:false}; there is no comparison of error class/state/rollback.
const partial = [], box = { value: 'before' }
const throwing = { exec(input) { partial.push(input); box.value = 'changed'; throw new Error('body') } }
assert.throws(() => invoke(throwing, 'effect'), Error)
assert.deepEqual(partial, ['effect']); assert.equal(box.value, 'changed')

const boxed = new String('boxed')
boxed.exec = function (input) { 'use strict'; return this === boxed && input === 'input' }
assert.equal(invoke(boxed, 'input'), true)
const boundReceiver = {}, bound = { exec: function (input) { 'use strict'; return this === boundReceiver && input === 'input' }.bind(boundReceiver) }
assert.equal(invoke(bound, 'input'), true)
const applyEvents = []
const callable = { exec: new Proxy(function () {}, { apply(target, thisArg, args) {
  applyEvents.push({ sameReceiver: thisArg === callable, argument: args[0] }); return null
} }) }
assert.equal(invoke(callable, 'input'), null)
assert.deepEqual(applyEvents, [{ sameReceiver: true, argument: 'input' }])

// Actual builtin regex execution is a distinct future proof obligation. These
// native observations do not label a callable as builtin merely by its name.
const regex = /^[0-9]+$/
regex.lastIndex = 17
const match = invoke(regex, '12')
assert.equal(match[0], '12'); assert.equal(match.index, 0); assert.equal(match.input, '12')
assert.equal(match.groups, undefined); assert.equal(regex.lastIndex, 17)
assert.equal(invoke(regex, 'x'), null); assert.equal(regex.lastIndex, 17)
assert.throws(() => invoke({ exec: RegExp.prototype.exec }, '12'), TypeError)
regex.exec = function (input) { assert.equal(this, regex); return 42 }
assert.equal(invoke(regex, 'not-digits'), 42)
regex.exec = 0
assert.throws(() => invoke(regex, '12'), TypeError)

console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs, verified: false,
  sourceBytes: Buffer.byteLength(source), sourceSha256: sha(source), plainJavaScript: true, typescriptErasure: false,
  wrapperVerified: false, nativeOnly: true,
  outsideDomain: { getterEvents, proxyEvents, duringArgumentExecWrite: duringEvents,
    noncallableArgumentEvents: noncallableEvents, nullBaseArgumentEvents: nullEvents,
    throwingGetterEvents: getterThrowEvents, partialFailure: { effects: partial, boxValue: box.value },
    boxedReceiver: true, boundCallable: true, callableProxy: applyEvents,
    builtinRegex: { match: match[0], index: match.index, input: match.input, groups: { kind: 'undefined' },
      lastIndex: 17, miss: null, wrongBrandThrows: true, customExecPrimitive: 42, noncallableHasNoFallback: true } },
  scope: 'Native-only boundaries; no full regex, source/frontend/native adequacy, error-class or partial-state correspondence.'
}))
