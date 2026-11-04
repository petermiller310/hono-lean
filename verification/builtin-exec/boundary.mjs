// Native-only builtin exec boundaries. Unsupported flags/coercions/proxies and
// full Array/RegExp behavior remain outside this milestone's formal domain.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun', version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(git('rev-parse', 'HEAD').trim(), revision); assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), entry.slice(0, tab).split(' ')[2]); checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs, 315)
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url))), raw = readFileSync(resolve(checkout, metadata.sourcePath))
const source = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8'), span = metadata.fragments.full
const sha = value => createHash('sha256').update(value).digest('hex')
assert.equal(metadata.revision, revision); assert.equal(sha(raw), metadata.sourceSha256); assert.equal(sha(source), span.sha256)
assert.equal(span.sha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString(), source)
const invoke = new Function('matcher', 'restPathString', '"use strict";\n' + source + '\nreturn m')
const exec = RegExp.prototype.exec, sourceGetter = Object.getOwnPropertyDescriptor(RegExp.prototype, 'source').get
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype), regexpBefore = Object.getOwnPropertyDescriptors(RegExp.prototype)
const brandEvents = [], argument = { toString() { brandEvents.push('input-ToString'); return '12' } }
const forged = Object.create(RegExp.prototype)
assert.throws(() => invoke(forged, argument), TypeError)
assert.deepEqual(brandEvents, [])
const coercionEvents = [], regex = /^[0-9]+$/
const input = { toString() { coercionEvents.push('input-ToString'); return '12' } }
const indexObject = { valueOf() { coercionEvents.push('lastIndex-valueOf'); return 17 } }
regex.lastIndex = indexObject
assert.equal(invoke(regex, input)[0], '12')
assert.deepEqual(coercionEvents, ['input-ToString', 'lastIndex-valueOf'])
assert.equal(regex.lastIndex, indexObject)
assert.equal(invoke(regex, new String('12'))[0], '12')

const numeric = []
for (const value of [-7, 3.75, Infinity, NaN, -0]) {
  const current = /^[0-9]+$/; current.lastIndex = value
  assert.equal(invoke(current, '12')[0], '12'); assert(Object.is(current.lastIndex, value))
  numeric.push({ input: Number.isNaN(value) ? 'NaN' : Object.is(value, -0) ? '-0' : String(value), kept: true })
}
const symbol = /^[0-9]+$/; symbol.lastIndex = Symbol('index')
assert.throws(() => invoke(symbol, '12'), TypeError)
const readOnly = /^[0-9]+$/
Object.defineProperty(readOnly, 'lastIndex', { value: 17, writable: false })
assert.equal(invoke(readOnly, '12')[0], '12'); assert.equal(invoke(readOnly, 'x'), null); assert.equal(readOnly.lastIndex, 17)
const frozen = Object.freeze(/^[0-9]+$/)
assert.equal(invoke(frozen, '12')[0], '12'); assert.equal(invoke(frozen, 'x'), null)

const publicReads = [], hidden = /^[0-9]+$/
Object.defineProperty(hidden, 'source', { value: '^x$', configurable: true })
for (const property of ['flags', 'global', 'sticky', 'unicode', 'unicodeSets', 'hasIndices', 'ignoreCase', 'multiline', 'dotAll'])
  Object.defineProperty(hidden, property, { get() { publicReads.push(property); throw new Error('public flag must not be read') }, configurable: true })
assert.equal(invoke(hidden, '12')[0], '12'); assert.deepEqual(publicReads, [])
assert.equal(sourceGetter.call(hidden), '^[0-9]+$')
const proxyEvents = [], proxy = new Proxy(/^[0-9]+$/, { get(target, key, receiver) {
  proxyEvents.push('get:' + String(key)); return Reflect.get(target, key, receiver)
} })
assert.throws(() => invoke(proxy, argument), TypeError)
assert.deepEqual(proxyEvents, ['get:exec']); assert.deepEqual(brandEvents, [])

const global = /[0-9]+/g; global.lastIndex = 1
const globalHit = invoke(global, 'a12'); assert.equal(globalHit[0], '12'); assert.equal(globalHit.index, 1); assert.equal(global.lastIndex, 3)
assert.equal(invoke(global, 'xx'), null); assert.equal(global.lastIndex, 0)
const sticky = /[0-9]+/y; sticky.lastIndex = 1
assert.equal(invoke(sticky, 'a12')[0], '12'); assert.equal(sticky.lastIndex, 3)
assert.equal(invoke(sticky, 'xx'), null); assert.equal(sticky.lastIndex, 0)
assert.throws(() => invoke(Object.freeze(/[0-9]+/g), '12'), TypeError)
const borrowed = { other: exec }
assert.throws(() => borrowed.other('12'), TypeError)
const replaced = /^[0-9]+$/; replaced.lastIndex = Symbol('unused-by-ordinary-callee')
replaced.exec = function (value) { assert.equal(this, replaced); return value }
assert.equal(invoke(replaced, 42), 42)
replaced.exec = 7; assert.throws(() => invoke(replaced, '12'), TypeError)

const result = invoke(/^[0-9]+$/, '12')
assert.equal(Object.getPrototypeOf(result), Array.prototype)
const describe = object => Object.fromEntries(['0', 'length', 'index', 'input', 'groups'].map(key => {
  const d = Object.getOwnPropertyDescriptor(object, key)
  assert(d && 'value' in d)
  return [key, { value: d.value === undefined ? { kind: 'undefined' } : d.value, writable: d.writable, enumerable: d.enumerable, configurable: d.configurable }]
}))
const descriptors = describe(result)
assert.equal(Object.hasOwn(result, 'groups'), true); assert.equal(result.groups, undefined)
assert.deepEqual([descriptors.length.writable, descriptors.length.enumerable, descriptors.length.configurable], [true, false, false])
for (const key of ['0', 'index', 'input', 'groups']) assert.deepEqual([descriptors[key].writable, descriptors[key].enumerable, descriptors[key].configurable], [true, true, true])
const prior = exec.call(/^prior$/, 'prior'); prior.shift()
assert.equal(Object.hasOwn(prior, '0'), false); assert.equal(prior.length, 0)
assert.equal(prior.index, 0); assert.equal(prior.input, 'prior'); assert.equal(Object.hasOwn(prior, 'groups'), true); assert.equal(prior.groups, undefined)
assert.throws(() => new RegExp('^[9-0]+$'), SyntaxError)
assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype), rootBefore)
assert.deepEqual(Object.getOwnPropertyDescriptors(RegExp.prototype), regexpBefore)
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs, verified: false, nativeOnly: true, plainJavaScript: true, typescriptErasure: false,
  sourceBytes: Buffer.byteLength(source), sourceSha256: sha(source),
  boundaries: { brandBeforeInputCoercion: brandEvents, inputThenLastIndexCoercion: coercionEvents.slice(0, 2),
    numericLastIndexControls: numeric, symbolIndexThrows: true, readonlyAndFrozenNonglobal: true,
    spoofSourceAndThrowingPublicFlagsIgnored: publicReads, proxyBrandFailure: proxyEvents,
    globalSticky: { matched: globalHit[0], index: globalHit.index, finalIndex: 0, frozenGlobalThrows: true },
    borrowedWrongBrandThrows: true, ordinaryReplacementSkipsBuiltinChecks: true, noncallableHasNoFallback: true,
    descriptors, resultPrototypeIsArrayPrototype: true, priorCurrentProjection: { length: 0, zeroOwn: false, index: 0, input: 'prior', groupsOwnUndefined: true }, reversedRangeConstructorThrows: true },
  scope: 'Native-only interpretation boundaries; no full grammar/flags/coercion/array/frontend/native adequacy or partial-error-state theorem.' }))
