// Finite exact-source evidence. Native TypeScript loading, wrappers and fixture
// transport are unverified; array observations are read-value projections.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

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
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath))
assert.equal(metadata.revision, revision); assert.equal(sha(raw), metadata.sourceSha256)
const fragments = Object.fromEntries(Object.entries(metadata.fragments).map(([name, span]) => {
  const text = readFileSync(new URL(`./${name}.ts.txt`, import.meta.url), 'utf8')
  assert.equal(sha(text), span.sha256)
  assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString('ascii'), text)
  return [name, text]
}))
assert.equal(fragments.prepare + fragments.slice, fragments.full)
const { splitPath } = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
const packet = JSON.parse(readFileSync(0, 'utf8')), prepareOnly = packet.prepareOnly ?? false
const source = packet.source ?? (prepareOnly ? fragments.prepare : fragments.full)
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({ length: text.length }, (_, index) => text.charCodeAt(index))

const results = (packet.cases ?? []).map(input => {
  const arrays = input.heap.map(() => []), initialLength = arrays.length, objects = new Map()
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
      case 'array': assert.ok(value.ref < initialLength, 'No dangling future fixture arrays'); return arrays[value.ref]
      case 'object': return object(value.ref)
      default: throw new Error(`Unsupported fixture value ${value.kind}`)
    }
  }
  input.heap.forEach((row, ref) => { arrays[ref].push(...row.map(decode)) })
  const encode = value => {
    if (value === undefined) return { kind: 'undefined' }
    if (value === null) return { kind: 'null' }
    if (typeof value === 'boolean') return { kind: 'bool', value }
    if (typeof value === 'number') return { kind: 'number', value }
    if (typeof value === 'string') return { kind: 'string', units: units(value) }
    if (Array.isArray(value)) {
      const reference = arrays.indexOf(value)
      assert.ok(reference >= 0, 'Unregistered source-visible array')
      return { kind: 'array', ref: reference }
    }
    for (const [reference, candidate] of objects) if (candidate === value) return { kind: 'object', ref: reference }
    throw new Error('Unknown native observation')
  }
  const path = string(input.path)
  const supplied = {}
  if (input.split) {
    supplied.parts = splitPath(path)
    supplied.len = supplied.parts.length
    arrays.push(supplied.parts)
  } else {
    if (Object.hasOwn(input, 'parts')) supplied.parts = decode(input.parts)
    if (Object.hasOwn(input, 'len')) supplied.len = input.len
  }
  const provided = ['parts', 'len'].filter(name => Object.hasOwn(supplied, name))
  const wrapper = `"use strict"; return function selected(path, initial, supplied, i, canary) {
    let partOffsets = initial;
    ${provided.map(name => `const ${name} = supplied.${name};`).join('\n')}
    const offset = canary, p = canary, restPathString = canary;
    let result;
    {
${source}
      result = { cache: partOffsets${prepareOnly ? '' : ', rest: restPathString'} };
    }
    return { ...result, scope: offset === canary && p === canary && restPathString === canary };
  }`
  const selected = new Function(wrapper)()
  let cache = decode(input.cache)
  const steps = []
  try {
    for (const index of input.indices ?? [0]) {
      const old = cache, oldCount = arrays.length
      const output = selected(path, cache, supplied, index, Symbol('outer locals'))
      cache = output.cache
      if (Array.isArray(cache) && !arrays.includes(cache)) arrays.push(cache)
      const step = { cache: encode(cache), reused: cache === old,
        fresh: Array.isArray(cache) && arrays.indexOf(cache) >= oldCount,
        scope: output.scope, heap: arrays.map(array => Array.from({ length: array.length }, (_, at) => encode(array[at]))) }
      if (!prepareOnly) step.rest = encode(output.rest)
      steps.push(step)
    }
    return { ok: true, steps, importedSplit: Boolean(input.split), wrapperSha256: sha(wrapper) }
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof RangeError || error instanceof ReferenceError)) throw error
    return { ok: false }
  }
})
console.log(JSON.stringify({ revision, runtime, version, checkedPinnedBlobs,
  execution: { verified: false, fragmentTypeErasure: false, sourceBytes: prepareOnly ? 276 : 338,
    importedPinnedSplitModule: true, moduleTypeErasure: 'native Node/Bun TS loading, unverified',
    sourceOverride: Object.hasOwn(packet, 'source'), arrays: 'source-array read values/identities; not own-presence or physical allocation counts' }, results }))
