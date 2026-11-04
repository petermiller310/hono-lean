// Exact51B source156 in a plain-JS strict fixture with genuine ordinary methods.
// Transport/observer/source wrappers and native engines are unverified. No TS
// erasure, RegExp builtin dispatch, lexical serialization or failure rollback.
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
const span = metadata.fragments.full
const nodeBytes = readFileSync(resolve(checkout, metadata.sourcePath))
const originalSource = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(metadata.revision, revision)
assert.equal(sha(nodeBytes), metadata.sourceSha256)
assert.equal(sha(originalSource), span.sha256)
assert.equal(span.sha256, 'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(nodeBytes.subarray(span.startByte, span.endByteExclusive).toString(), originalSource)
assert.equal(Buffer.byteLength(originalSource), 51)
const packet = JSON.parse(readFileSync(0, 'utf8'))
const source = packet.source ?? originalSource
const methodSource = packet.methodSource ?? 'exec(input) { return [input] }'
// Fixture name extraction is deliberately not a verified JS parser. Source
// and method text are inserted intact; no text is rewritten into builtin exec.
const declaredName = /^\s*const\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=/.exec(source)?.[1]
const methodName = /^\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*\(/.exec(methodSource)?.[1]
const methodWrapper = `"use strict";
const input = "captured parameter shadow";
return class Fixture {
  #secret = 7;
  ${methodSource}
  static readSecret(instance) { return instance.#secret }
}`
const callerWrapper = `"use strict";
return class Caller {
  #caller = 17;
  run(matcher, restPathString) {
    const box = this, m = this, input = "caller parameter shadow";
    let observed;
    {
${source}
      observed = {declaredName:${JSON.stringify(declaredName)},declaredValue:${declaredName ?? 'undefined'},m};
    }
    return {...observed,scope:this===callerReference.current && box===callerReference.current && m===callerReference.current && input==="caller parameter shadow" && this.#caller===17};
  }
}`
let createMethod, createCaller
try {
  if (!declaredName || !methodName) throw new SyntaxError('Outside fixture name transport')
  createMethod = new Function('box', methodWrapper)
  createCaller = new Function('callerReference', callerWrapper)
} catch {
  // Compilation/domain failures are projected to the same bounded failure
  // observation as call failures, without an exception-class correspondence.
}
const units = value => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))
const string = values => values.map(value => String.fromCharCode(value)).join('')
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype)
const results = (packet.cases ?? []).map(input => {
  if (!createMethod || !createCaller) return { ok: false }
  const arrays = [[]]
  const prototype = Object.create(null)
  const box = Object.create(null)
  let matcher, callerThis, Fixture, functions
  const objects = [Object.prototype, null, prototype, box, null]
  const decode = tag => {
    switch (tag.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': return tag.value
      case 'number': return tag.value
      case 'string': return string(tag.units)
      case 'array': assert.equal(tag.ref, 0); return arrays[0]
      case 'object': assert(objects[tag.ref] !== null && objects[tag.ref] !== undefined); return objects[tag.ref]
      case 'function': assert([3, 4].includes(tag.ref)); return functions[tag.ref]
      case 'constructor': return Object
      default: throw new Error('Unknown fixture value tag')
    }
  }
  // Both are genuine ordinary method functions; fn3 keeps its class-private
  // lexical identity even after the instance's public prototype is replaced.
  Fixture = createMethod(box)
  matcher = new Fixture()
  objects[1] = matcher
  Object.setPrototypeOf(matcher, prototype)
  const other = new Function('"use strict"; return {other(input) { return null }}.other')()
  functions = { 3: Fixture.prototype[methodName], 4: other }
  assert.equal(typeof functions[3], 'function')
  // A native closure observes the actual caller identity. Neither scope nor
  // private-name maps are fabricated from a serialized lexical environment.
  const callerReference = { current: null }
  const ActualCaller = createCaller(callerReference)
  callerThis = new ActualCaller()
  Object.setPrototypeOf(callerThis, null)
  callerReference.current = callerThis
  objects[4] = callerThis
  Object.defineProperties(box, {
    value: { value: decode(input.boxValue ?? { kind: 'string', units: units('captured') }), writable: true, enumerable: true, configurable: true },
    calls: { value: arrays[0], writable: true, enumerable: true, configurable: true }
  })
  if (input.inherited) {
    Object.defineProperty(prototype, 'exec', { value: functions[3], writable: true, enumerable: true, configurable: true })
  } else {
    const kind = input.calleeKind ?? 'method'
    const descriptor = { enumerable: true, configurable: true }
    if (kind === 'missingGetter') Object.assign(descriptor, { get: undefined, set: undefined })
    else if (kind === 'prototypeGetter') Object.assign(descriptor, { get: Object.getOwnPropertyDescriptor(Object.prototype, '__proto__').get, set: undefined })
    else {
      assert(['method', 'undefined', 'number', 'null'].includes(kind))
      const handle = input.methodHandle ?? 3
      assert([3, 4].includes(handle))
      Object.assign(descriptor, { value: kind === 'method' ? functions[handle] : kind === 'undefined' ? undefined : kind === 'number' ? 7 : null, writable: true })
    }
    Object.defineProperty(matcher, 'exec', descriptor)
  }
  Object.defineProperty(matcher, 'other', { value: functions[4], writable: true, enumerable: true, configurable: true })
  let observed
  try { observed = ActualCaller.prototype.run.call(callerThis, matcher, string(input.input ?? [])) }
  catch { return { ok: false } }
  // Only the returned/declaration-visible fresh dense array is tracked. No
  // total physical/unreachable-allocation correspondence is claimed.
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
    if (value === functions[3]) return { kind: 'function', ref: 3 }
    if (value === functions[4]) return { kind: 'function', ref: 4 }
    throw new Error('Outside bounded native observer value domain')
  }
  const objectView = object => ({
    own: Object.getOwnPropertyNames(object).map(name => {
      const descriptor = Object.getOwnPropertyDescriptor(object, name)
      if ('value' in descriptor) return { key: units(name), kind: 'data', value: encode(descriptor.value),
        writable: descriptor.writable, enumerable: descriptor.enumerable, configurable: descriptor.configurable }
      const getter = descriptor.get === undefined ? 'missing' :
        descriptor.get === Object.getOwnPropertyDescriptor(Object.prototype, '__proto__').get ? 'prototype' : null
      assert(getter !== null && descriptor.set === undefined)
      return { key: units(name), kind: 'accessor', getter, setter: 'missing', enumerable: descriptor.enumerable, configurable: descriptor.configurable }
    }),
    prototype: Object.getPrototypeOf(object) === null ? null : objects.indexOf(Object.getPrototypeOf(object)),
    extensible: Object.isExtensible(object)
  })
  assert(arrays.length <= 2)
  for (const array of arrays) for (let i = 0; i < array.length; i++) assert(Object.hasOwn(array, i))
  assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype), rootBefore)
  return { ok: true, declaredName: observed.declaredName, declaredValue: encode(observed.declaredValue),
    m: encode(observed.m), guard: Boolean(observed.m), heap: arrays.map(array => array.map(encode)),
    objects: [{ intrinsic: 'Object.prototype' }, ...objects.slice(1).map(objectView)],
    secret: encode(Fixture.readSecret(matcher)), scope: observed.scope }
})
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs, verified: false,
  sourceSha256: sha(originalSource), executedSourceSha256: sha(source), methodSourceSha256: sha(methodSource),
  plainJavaScript: true, typescriptErasure: false, wrapperVerified: false, observerVerified: false,
  wrapperInputSha256: sha(methodWrapper + callerWrapper),
  observation: 'Bounded current-member invocation; O0 sentinel/read projection, dense visible returned array only; no lexical serialization, builtin regex, native adequacy or failure-state claim.',
  results }))
