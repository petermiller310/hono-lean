// Unverified exact-source controls and separate instrumented clones. Visible
// graph IDs omit unreachable internal match/iterator allocations entirely.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
const sha = data => createHash('sha256').update(data).digest('hex')
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const at = entry.indexOf('\t'), blob = entry.slice(0, at).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(at + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath))
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
const pinned = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8'), span = metadata.fragments.full
assert.equal(sha(pinned), span.sha256)
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString('ascii'), pinned)
const packet = JSON.parse(readFileSync(0, 'utf8')), source = packet.source ?? pinned
const originalMatch = String.prototype.match, originalExec = RegExp.prototype.exec
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index))
const names = ['child', 'params', 'm', 'curNodesQueue']

function run(input, instrumented) {
  const provided = names.filter(name => Object.hasOwn(input.bindings, name))
  const wrapper = `"use strict"; return class Fragment {
    #children; #params; #keep;
    initialize(children, params, keep) { this.#children=children; this.#params=params; this.#keep=keep; }
    read() { return { children: this.#children, params: this.#params, keep: this.#keep }; }
    run(environment, canary) {
      ${provided.map(name => `const ${name} = environment.${name};`).join('\n')}
      const _ = canary, componentCount = canary, targetCurNodes = canary;
${source}
      return _ === canary && componentCount === canary && targetCurNodes === canary;
    }
  }`
  const Fragment = new Function(wrapper)()
  const arrays = input.heap.map(row => new Array(row.length)), objects = input.objects.map(() => Object.create(null))
  const initialLength = arrays.length
  let getterReads = 0
  const decode = value => {
    switch (value.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': return value.value
      case 'number': return value.value
      case 'string': return string(value.units)
      case 'array': assert.ok(value.ref < initialLength, 'No fixture may name a future internal ID'); return arrays[value.ref]
      case 'object': assert.ok(value.ref < objects.length); return objects[value.ref]
      default: throw new Error(`Unsupported input value ${value.kind}`)
    }
  }
  // Allocate the owner before initializing private fields, allowing valid
  // self references. Scaffolding/initialization is outside the source proof.
  const owner = new Fragment()
  const initialize = Fragment.prototype.initialize, actualRunner = Fragment.prototype.run, actualReader = Fragment.prototype.read
  objects[0] = owner
  Object.setPrototypeOf(owner, null)
  Reflect.apply(initialize, owner, [decode(input.private.children), decode(input.private.params), decode(input.private.keep)])
  input.heap.forEach((row, ref) => row.forEach((value, index) => {
    if (value !== null) Object.defineProperty(arrays[ref], index, {
      value: decode(value), writable: true, enumerable: true, configurable: true
    })
  }))
  input.objects.forEach((object, ref) => {
    Object.setPrototypeOf(objects[ref], object.prototype === null ? null : objects[object.prototype])
    for (const property of object.own) {
      const descriptor = { enumerable: property.enumerable, configurable: property.configurable }
      if (property.kind === 'data') Object.assign(descriptor, { value: decode(property.value), writable: property.writable })
      else Object.assign(descriptor, { get() { getterReads++; throw new Error('Enumeration must not read getter values') } })
      Object.defineProperty(objects[ref], string(property.key), descriptor)
    }
  })
  const environment = Object.fromEntries(provided.map(name => [name, decode(input.bindings[name])]))
  const traces = [], seen = new Set()
  let active
  try {
    if (instrumented) {
      RegExp.prototype.exec = function (input) {
        const value = Reflect.apply(originalExec, this, [input])
        if (active?.pattern === this) {
          if (value !== null) active.positions.push(value.index)
          active.lastIndexTrace.push(this.lastIndex)
        }
        return value
      }
      String.prototype.match = function (pattern) {
        assert.equal(pattern.flags, 'g')
        assert.ok(!seen.has(pattern)); seen.add(pattern)
        active = { pattern, positions: [], lastIndexTrace: [pattern.lastIndex] }
        const paramsAtMatch = Reflect.apply(actualReader, owner, []).params
        const value = Reflect.apply(originalMatch, this, [pattern])
        traces.push({ positions: active.positions, lastIndexTrace: active.lastIndexTrace,
          unit: pattern.source === '\\/' ? 47 : pattern.source.charCodeAt(0), lastIndex: pattern.lastIndex,
          match: value === null ? null : value.map(units), paramsAtMatch })
        active = undefined
        return value
      }
    }
    const scope = Reflect.apply(actualRunner, owner, [environment, Symbol('outer lexical canary')])
    const fields = Reflect.apply(actualReader, owner, [])
    // All initial arrays are roots. New arrays receive canonical IDs through
    // visible references, never through an assumed number of internal matches.
    const visible = arrays.slice(), encode = value => {
      if (value === undefined) return { kind: 'undefined' }
      if (value === null) return { kind: 'null' }
      if (typeof value === 'boolean') return { kind: 'bool', value }
      if (typeof value === 'number') return { kind: 'number', value }
      if (typeof value === 'string') return { kind: 'string', units: units(value) }
      if (Array.isArray(value)) {
        if (!visible.includes(value)) visible.push(value)
        return { kind: 'array', ref: visible.indexOf(value) }
      }
      const reference = objects.indexOf(value)
      assert.ok(reference >= 0, 'Unknown visible object')
      return { kind: 'object', ref: reference }
    }
    const privateFields = Object.fromEntries(['children', 'params', 'keep'].map(name => [name, encode(fields[name])]))
    const heap = []
    for (let index = 0; index < visible.length; index++) heap.push(Array.from({ length: visible[index].length }, (_, at) =>
      Object.hasOwn(visible[index], at) ? encode(visible[index][at]) : null))
    const objectOutput = objects.map(object => ({ prototype: Object.getPrototypeOf(object) === null ? null : objects.indexOf(Object.getPrototypeOf(object)),
      own: Object.getOwnPropertyNames(object).map(key => {
        const descriptor = Object.getOwnPropertyDescriptor(object, key)
        return 'value' in descriptor ? { key: units(key), kind: 'data', value: encode(descriptor.value),
          writable: descriptor.writable, enumerable: descriptor.enumerable, configurable: descriptor.configurable }
          : { key: units(key), kind: 'accessor', enumerable: descriptor.enumerable, configurable: descriptor.configurable }
      }) }))
    const result = { ok: true, state: { private: privateFields, heap, objects: objectOutput, scope, getterReads } }
    if (instrumented) result.traces = traces.map(trace => ({ ...trace, paramsAtMatch: encode(trace.paramsAtMatch) }))
    return { result, wrapperSha256: sha(wrapper) }
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof RangeError || error instanceof ReferenceError)) throw error
    return { result: { ok: false }, wrapperSha256: sha(wrapper) }
  } finally {
    String.prototype.match = originalMatch; RegExp.prototype.exec = originalExec
  }
}
const controls = (packet.cases ?? []).map(input => run(input, false))
const instrumented = (packet.cases ?? []).map(input => run(input, true))
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs,
  execution: { verified: false, fragmentTypeErasure: false, sourceBytes: 317,
    sourceOverride: Object.hasOwn(packet, 'source'), graph: 'canonical visible graph; unreachable internal allocations omitted',
    instrumentation: 'separate cloned-fixture match/exec wrappers; controls use standard methods',
    wrapperHashes: controls.map(result => result.wrapperSha256) },
  controls: controls.map(item => item.result), instrumented: instrumented.map(item => item.result) }))
