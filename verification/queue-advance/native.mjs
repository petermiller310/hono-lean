// Exact plain-JavaScript fragment evidence; this wrapper is not a verified translator.
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
const source = readFileSync(new URL('./source.ts.txt', import.meta.url), 'utf8')
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
assert.equal(sha(source), metadata.fragment.sha256)
assert.equal(raw.subarray(metadata.fragment.startByte, metadata.fragment.endByteExclusive).toString('ascii'), source)
const packet = JSON.parse(readFileSync(0, 'utf8'))
const selected = packet.source ?? source
// The fragment is already JavaScript: it is inserted verbatim, without TS erasure.
const wrapper = `"use strict";
return function step(curNodesQueue, tempNodes, initial, shadow) {
  let curNodes = shadow;
  let result;
  {
    let curNodes = initial;
${selected}
    result = { shifted, current: curNodes };
  }
  return { ...result, shadow: curNodes };
}`
const step = new Function(wrapper)()
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index))
const results = (packet.cases ?? []).map(input => {
  const arrays = input.heap.map(() => []), objects = new Map()
  const object = index => {
    if (!objects.has(index)) objects.set(index, Object.create(null))
    return objects.get(index)
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
      assert.ok(reference >= 0, 'An observed array has not been registered')
      return { kind: 'array', ref: reference }
    }
    for (const [reference, candidate] of objects) if (candidate === value) return { kind: 'object', ref: reference }
    throw new Error('Unknown native object')
  }
  input.heap.forEach((row, index) => arrays[index].push(...row.map(decode)))
  const queue = decode(input.queue), temp = decode(input.temp), shadow = object(3), receiver = object(2)
  let current = decode(input.current ?? { kind: 'undefined' })
  const steps = []
  try {
    for (let index = 0; index < (input.rounds ?? 1); index++) {
      const oldCount = arrays.length
      const result = step.call(receiver, queue, temp, current, shadow)
      current = result.current
      if (Array.isArray(current) && !arrays.includes(current)) arrays.push(current)
      assert.equal(result.shadow, shadow, 'The outer shadowed binding changed')
      steps.push({ shifted: encode(result.shifted), current: encode(current),
        fresh: Array.isArray(current) && arrays.indexOf(current) >= oldCount,
        heap: arrays.map(array => array.map(encode)) })
    }
  } catch (error) {
    if (!(error instanceof TypeError)) throw error
    return { ok: false }
  }
  return { ok: true, steps }
})
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs,
  execution: { verified: false, fragmentTypeErasure: false,
    sourceOverride: Object.hasOwn(packet, 'source'), wrapperSha256: sha(wrapper) }, results }))
