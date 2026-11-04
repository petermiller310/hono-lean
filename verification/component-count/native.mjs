// Finite, unverified observations: exact-source controls and separately
// instrumented clones. Abstract array IDs reserve an opaque accumulator slot;
// this is not observation of unreachable arrays or native allocation counts.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath))
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
const fragment = (path, span) => {
  const source = readFileSync(new URL(path, import.meta.url), 'utf8')
  assert.equal(sha(source), span.sha256)
  assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString('ascii'), source)
  return source
}
const countSource = fragment('./count.ts.txt', metadata.fragments.count)
const fullSource = fragment('./full.ts.txt', metadata.fragments.full)
const consumer = JSON.parse(readFileSync(new URL('../queue-advance/source.json', import.meta.url)))
const advanceSource = fragment('../queue-advance/source.ts.txt', consumer.fragment)
const packet = JSON.parse(readFileSync(0, 'utf8')), full = packet.full ?? true
const source = packet.source ?? (full ? fullSource : countSource)
const wrapper = `"use strict";
return function selected(m, curNodesQueue, child, shadow) {
  const componentCount = shadow, targetCurNodes = shadow;
  let result;
  {
${source}
    result = { count: componentCount, target: ${full ? 'targetCurNodes' : 'undefined'} };
  }
  return { ...result, shadows: [componentCount, targetCurNodes] };
}`
const selected = new Function(wrapper)()
const advance = new Function(`"use strict";
return function advance(curNodesQueue, tempNodes, initial) {
  let curNodes = initial;
${advanceSource}
  return { shifted, current: curNodes };
}`)()
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index))
const originalMatch = String.prototype.match, originalExec = RegExp.prototype.exec

function run(input, instrumented) {
  const INTERNAL = Symbol('unobserved global accumulator')
  const arrays = input.heap.map(row => new Array(row.length)), opaque = new Set(), objects = new Map()
  const initialLength = arrays.length
  const object = reference => {
    if (!objects.has(reference)) objects.set(reference, Object.create(null))
    return objects.get(reference)
  }
  const decode = value => {
    switch (value.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': return value.value
      case 'number': return value.value
      case 'string': return string(value.units)
      case 'array': assert.ok(value.ref < initialLength, 'Fixtures cannot refer to future internal IDs'); return arrays[value.ref]
      case 'object': return object(value.ref)
      default: throw new Error(`Unsupported fixture value: ${value.kind}`)
    }
  }
  const encode = value => {
    if (value === undefined) return { kind: 'undefined' }
    if (value === null) return { kind: 'null' }
    if (typeof value === 'boolean') return { kind: 'bool', value }
    if (typeof value === 'number') return { kind: 'number', value }
    if (typeof value === 'string') return { kind: 'string', units: units(value) }
    if (Array.isArray(value)) {
      const reference = arrays.indexOf(value)
      assert.ok(reference >= 0, 'Unregistered observed array')
      return { kind: 'array', ref: reference }
    }
    for (const [reference, candidate] of objects) if (candidate === value) return { kind: 'object', ref: reference }
    throw new Error('Unknown observed native object')
  }
  input.heap.forEach((row, reference) => row.forEach((slot, index) => {
    if (slot !== null) Object.defineProperty(arrays[reference], index, {
      value: decode(slot), writable: true, enumerable: true, configurable: true
    })
  }))
  const snapshot = () => arrays.map((array, reference) => opaque.has(reference)
    ? { internalAccumulator: true }
    : Array.from({ length: array.length }, (_, index) => Object.hasOwn(array, index) ? encode(array[index]) : null))
  const register = value => { if (Array.isArray(value) && !arrays.includes(value)) arrays.push(value) }
  const queue = decode(input.queue ?? { kind: 'array', ref: 0 })
  const temp = decode(input.temp ?? { kind: 'array', ref: 2 })
  const shadow = object(3), receiver = object(2), counts = [], schedules = [], advances = [], retained = [], traces = []
  let current = decode(input.current ?? { kind: 'undefined' }), active, accumulatorID
  const seenRegexps = new Set()
  try {
    if (instrumented) {
      // These wrappers change method lookup and are explicitly separate evidence.
      RegExp.prototype.exec = function (input) {
        const result = Reflect.apply(originalExec, this, [input])
        if (active?.pattern === this) {
          if (result !== null) active.positions.push(result.index)
          active.lastIndexTrace.push(this.lastIndex)
        }
        return result
      }
      String.prototype.match = function (pattern) {
        assert.equal(pattern.flags, 'g')
        assert.ok(!seenRegexps.has(pattern), 'Literal must be fresh per evaluation')
        seenRegexps.add(pattern)
        active = { pattern, positions: [], lastIndexTrace: [pattern.lastIndex] }
        const result = Reflect.apply(originalMatch, this, [pattern])
        if (result !== null) arrays[accumulatorID] = result
        traces.push({ positions: active.positions, lastIndexTrace: active.lastIndexTrace,
          unit: pattern.source === '\\/' ? 47 : pattern.source.charCodeAt(0),
          lastIndex: pattern.lastIndex, match: result === null ? null : result.map(units) })
        active = undefined
        return result
      }
    }
    for (const request of input.requests ?? []) {
      const m = decode(request.m ?? { kind: 'array', ref: 1 }), child = decode(request.child ?? { kind: 'object', ref: 0 })
      accumulatorID = arrays.length
      // This slot is an explicitly unobserved projection, never fabricated [].
      opaque.add(accumulatorID); arrays.push(INTERNAL)
      const result = selected.call(receiver, m, queue, child, shadow)
      assert.deepEqual(result.shadows, [shadow, shadow])
      if (Array.isArray(result.count)) arrays[accumulatorID] = result.count
      counts.push(encode(result.count))
      if (full) {
        register(result.target); retained.push(result.target)
        schedules.push({ target: encode(result.target), fresh: Array.isArray(result.target) && arrays.indexOf(result.target) > accumulatorID,
          heap: snapshot() })
      }
    }
    for (let index = 0; index < (input.advances ?? 0); index++) {
      const oldCount = arrays.length
      const result = advance.call(receiver, queue, temp, current)
      current = result.current; register(current)
      advances.push({ shifted: encode(result.shifted), current: encode(current),
        fresh: Array.isArray(current) && arrays.indexOf(current) >= oldCount, heap: snapshot() })
    }
    const result = { ok: true, counts, schedules, advances, retained: retained.map(encode), heap: snapshot() }
    if (instrumented) result.traces = traces
    return result
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof RangeError)) throw error
    return { ok: false }
  } finally {
    String.prototype.match = originalMatch; RegExp.prototype.exec = originalExec
  }
}
const controls = (packet.cases ?? []).map(input => run(input, false))
const instrumented = (packet.cases ?? []).map(input => run(input, true))
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs,
  execution: { verified: false, fragmentTypeErasure: false, countBytes: 70, fullBytes: 191,
    sourceOverride: Object.hasOwn(packet, 'source'), wrapperSha256: sha(wrapper),
    accumulatorIDs: 'opaque projection; not observed native allocations',
    instrumentation: 'separate cloned-fixture match/exec wrappers; controls use standard methods' },
  controls, instrumented }))
