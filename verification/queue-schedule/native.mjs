// Exact-source sparse queue observations. Wrappers/fixtures/engines are unverified.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
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
const scheduleSource = fragment('./source.ts.txt', metadata.fragment)
const advanceSource = fragment('../queue-advance/source.ts.txt', metadata.consumer)
const packet = JSON.parse(readFileSync(0, 'utf8'))
const selectedSchedule = packet.scheduleSource ?? scheduleSource
const selectedAdvance = packet.advanceSource ?? advanceSource
const scheduleWrapper = `"use strict";
return function schedule(curNodesQueue, componentCount, child, shadow) {
  const targetCurNodes = shadow;
  let result;
  {
${selectedSchedule}
    result = targetCurNodes;
  }
  return { target: result, shadow: targetCurNodes };
}`
const advanceWrapper = `"use strict";
return function advance(curNodesQueue, tempNodes, initial, shadow) {
  let curNodes = shadow;
  let result;
  {
    let curNodes = initial;
${selectedAdvance}
    result = { shifted, current: curNodes };
  }
  return { ...result, shadow: curNodes };
}`
const schedule = new Function(scheduleWrapper)(), advance = new Function(advanceWrapper)()
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index))
const results = (packet.cases ?? []).map(input => {
  const arrays = input.heap.map(row => new Array(row.length)), objects = new Map()
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
      case 'array': assert.ok(value.ref < arrays.length); return arrays[value.ref]
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
  input.heap.forEach((row, index) => row.forEach((slot, at) => {
    if (slot !== null) Object.defineProperty(arrays[index], at, {
      value: decode(slot), writable: true, enumerable: true, configurable: true
    })
  }))
  // null in this transport means an absent own index, never JavaScript null.
  const snapshot = () => arrays.map(array => Array.from({ length: array.length }, (_, index) =>
    Object.hasOwn(array, index) ? encode(array[index]) : null))
  const register = value => { if (Array.isArray(value) && !arrays.includes(value)) arrays.push(value) }
  const queue = decode(input.queue), temp = decode(input.temp ?? { kind: 'array', ref: 2 })
  const shadow = object(3), receiver = object(2), schedules = [], advances = [], retained = []
  let current = decode(input.current ?? { kind: 'undefined' })
  try {
    for (const request of input.requests ?? []) {
      const oldCount = arrays.length
      const result = schedule.call(receiver, queue, request.index, decode(request.child), shadow)
      register(result.target); retained.push(result.target)
      assert.equal(result.shadow, shadow)
      schedules.push({ target: encode(result.target), fresh: Array.isArray(result.target) && arrays.indexOf(result.target) >= oldCount,
        heap: snapshot() })
    }
    for (let index = 0; index < (input.advances ?? 0); index++) {
      const oldCount = arrays.length
      const result = advance.call(receiver, queue, temp, current, shadow)
      current = result.current; register(current)
      assert.equal(result.shadow, shadow)
      advances.push({ shifted: encode(result.shifted), current: encode(current),
        fresh: Array.isArray(current) && arrays.indexOf(current) >= oldCount, heap: snapshot() })
    }
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof RangeError)) throw error
    return { ok: false }
  }
  return { ok: true, schedules, advances, retained: retained.map(encode), heap: snapshot() }
})
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs,
  execution: { verified: false, fragmentTypeErasure: false, schedulingBytes: 121, consumingBytes: 109,
    sourceOverrides: ['scheduleSource', 'advanceSource'].filter(name => Object.hasOwn(packet, name)),
    scheduleWrapperSha256: sha(scheduleWrapper), advanceWrapperSha256: sha(advanceWrapper) }, results }))
