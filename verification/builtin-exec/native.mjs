// Plain-JS exact source156 with real RegExp instances and the actual builtin
// function identity. Construction, wrapper, identity/name observer and engines
// remain unverified; this is a bounded finite comparison, not native adequacy.
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
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath)), span = metadata.fragments.full
const original = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
assert.equal(sha(original), span.sha256)
assert.equal(span.sha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString(), original)
assert.equal(Buffer.byteLength(original), 51)
const packet = JSON.parse(readFileSync(0, 'utf8'))
const source = packet.source ?? original
// This closed-fixture observer is intentionally not a verified JS parser.
const header = /^\s*const\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*(matcher|alternate)\.([A-Za-z_$][A-Za-z0-9_$]*)\s*\(/.exec(source)
const declaredName = header?.[1]
const wrapper = `"use strict";
const m = caller, priorMatcher = matcher, priorInput = restPathString;
let observed;
{
${source}
  observed = {declaredName:${JSON.stringify(declaredName)},declaredValue:${declaredName ?? 'undefined'},m};
}
return {...observed,scope:this===caller && m===caller && alternate===caller && priorMatcher===matcher && priorInput===restPathString && alternateInput==="x"};`
let invoke
try { if (!header) throw new SyntaxError('Outside fixture observer'); invoke = new Function('matcher', 'restPathString', 'alternate', 'alternateInput', 'caller', wrapper) }
catch { /* Failure-only projection, not an exception/frontend correspondence. */ }
const unitString = values => values.map(value => String.fromCharCode(value)).join('')
const units = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))
const builtin = RegExp.prototype.exec
const sourceGetter = Object.getOwnPropertyDescriptor(RegExp.prototype, 'source').get
const flagGetters = ['hasIndices', 'global', 'ignoreCase', 'multiline', 'dotAll', 'unicode', 'unicodeSets', 'sticky']
  .map(name => Object.getOwnPropertyDescriptor(RegExp.prototype, name).get)
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype)
const regexpPrototypeBefore = Object.getOwnPropertyDescriptors(RegExp.prototype)
const functions = new Function('"use strict"; return {3:{exec(input){return input}}.exec,4:{exec(input){return [input]}}.exec}')()
// Handle0 is a real callable old-function control. The model's new dispatcher
// deliberately refuses that table range; it is NOT a native noncallable value.
functions[0] = new Function('"use strict"; return function old(){return 0}')()
functions[5] = builtin
const results = (packet.cases ?? []).map(input => {
  const failure = () => ({ parsed: true, ok: false })
  if (!invoke) return failure()
  const originalPattern = unitString(input.pattern), argument = unitString(input.input)
  let matcher
  try { matcher = input.brand === false ? Object.create(RegExp.prototype) : new RegExp(originalPattern) }
  catch { return failure() }
  const branded = input.brand !== false
  const intrinsicSource = branded ? sourceGetter.call(matcher) : null
  const intrinsicFlags = branded ? flagGetters.map(getter => getter.call(matcher)) : null
  const caller = Object.create(null)
  Object.defineProperty(caller, 'exec', { value: functions[3], writable: true, enumerable: true, configurable: true })
  const objects = [Object.prototype, matcher, RegExp.prototype, caller]
  const prior = builtin.call(/^prior$/, 'prior')
  const arrays = [prior]
  const priorDescriptors = Object.getOwnPropertyDescriptors(prior), priorPrototype = Object.getPrototypeOf(prior), priorExtensible = Object.isExtensible(prior)
  const lastIndex = input.lastIndex ?? 0
  assert(Number.isSafeInteger(lastIndex))
  Object.defineProperty(matcher, 'lastIndex', { value: lastIndex, writable: input.writable ?? true, enumerable: false, configurable: false })
  Object.defineProperty(matcher, 'other', { value: functions[3], writable: true, enumerable: true, configurable: true })
  Object.defineProperty(matcher, 'borrowed', { value: builtin, writable: true, enumerable: true, configurable: true })
  const handle = input.handle ?? 5
  assert([0, 3, 4, 5].includes(handle))
  if (input.ownExec || handle !== 5 || input.calleeKind === 'number')
    Object.defineProperty(matcher, 'exec', { value: input.calleeKind === 'number' ? 0 : functions[handle], writable: true, enumerable: true, configurable: true })
  if (input.spoofSource !== undefined)
    Object.defineProperty(matcher, 'source', { value: unitString(input.spoofSource), writable: true, enumerable: false, configurable: true })
  if (input.extensible === false) Object.preventExtensions(matcher)
  // Pure DATA lookup in the closed fixture only. It does not wrap/proxy the
  // builtin or alter its identity/brand. Effectful Get/arguments are boundaries.
  const selectedReceiver = header[2] === 'matcher' ? matcher : caller
  const selectedCallee = selectedReceiver[header[3]]
  let observed
  try { observed = invoke.call(caller, matcher, argument, caller, 'x', caller) }
  catch { return failure() }
  if (Array.isArray(observed.declaredValue) && !arrays.includes(observed.declaredValue)) arrays.push(observed.declaredValue)
  const encode = value => {
    if (value === undefined) return { kind: 'undefined' }
    if (value === null) return { kind: 'null' }
    if (value === Object) return { kind: 'constructor' }
    if (typeof value === 'boolean') return { kind: 'bool', value }
    if (typeof value === 'number') return { kind: 'number', value }
    if (typeof value === 'string') return { kind: 'string', units: units(value) }
    if (arrays.includes(value)) return { kind: 'array', ref: arrays.indexOf(value) }
    if (objects.includes(value)) return { kind: 'object', ref: objects.indexOf(value) }
    for (const handle of [0, 3, 4, 5]) if (value === functions[handle]) return { kind: 'function', ref: handle }
    throw new Error('Outside bounded native observer value domain')
  }
  const descriptor = property => {
    assert(property && 'value' in property)
    return { kind: 'data', value: encode(property.value), writable: property.writable, enumerable: property.enumerable, configurable: property.configurable }
  }
  const view = array => Object.fromEntries([['zero', '0'], ['length', 'length'], ['index', 'index'], ['input', 'input'], ['groups', 'groups']]
    .map(([name, key]) => [name, descriptor(Object.getOwnPropertyDescriptor(array, key))]))
  const builtinHit = selectedCallee === builtin && Array.isArray(observed.declaredValue) && observed.declaredValue !== prior
  if (builtinHit) {
    assert.equal(Object.getPrototypeOf(observed.declaredValue), Array.prototype)
    assert.equal(Object.getOwnPropertySymbols(observed.declaredValue).length, 0)
    assert.deepEqual(Object.getOwnPropertyNames(observed.declaredValue).sort(), ['0', 'groups', 'index', 'input', 'length'])
  }
  const objectView = object => ({
    own: Object.getOwnPropertyNames(object).map(key => ({ key: units(key), ...descriptor(Object.getOwnPropertyDescriptor(object, key)) })),
    prototype: Object.getPrototypeOf(object) === null ? null : objects.indexOf(Object.getPrototypeOf(object)),
    extensible: Object.isExtensible(object)
  })
  let brandsKept
  if (branded) brandsKept = sourceGetter.call(matcher) === intrinsicSource && flagGetters.every((getter, i) => getter.call(matcher) === intrinsicFlags[i])
  else {
    brandsKept = false
    try { sourceGetter.call(matcher) } catch (error) { brandsKept = error instanceof TypeError }
  }
  const priorKept = Object.getPrototypeOf(prior) === priorPrototype && Object.isExtensible(prior) === priorExtensible &&
    (() => { try { assert.deepEqual(Object.getOwnPropertyDescriptors(prior), priorDescriptors); return true } catch { return false } })()
  assert(arrays.length <= 2)
  for (const array of arrays) for (let index = 0; index < array.length; index++) assert(Object.hasOwn(array, index))
  assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype), rootBefore)
  assert.deepEqual(Object.getOwnPropertyDescriptors(RegExp.prototype), regexpPrototypeBefore)
  return { parsed: true, ok: true, declaredName: observed.declaredName, declaredValue: encode(observed.declaredValue), m: encode(observed.m), guard: Boolean(observed.m),
    heap: arrays.map(array => array.map(encode)), view: builtinHit ? view(observed.declaredValue) : null, priorView: view(prior),
    objects: [{ intrinsic: 'Object.prototype' }, objectView(matcher), { intrinsic: 'RegExp.prototype' }, objectView(caller)],
    scope: observed.scope, brandsKept, priorKept }
})
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs, verified: false, plainJavaScript: true, typescriptErasure: false,
  sourceSha256: sha(original), executedSourceSha256: sha(source), wrapperInputSha256: sha(wrapper), observerVerified: false,
  observation: 'Pure-DATA identity attribution; five own match descriptors only, old prior view retained, one visible fresh array; no physical/unreachable allocation, key-order, constructor/cache/tuple/native adequacy or failure-state claim.', results }))
