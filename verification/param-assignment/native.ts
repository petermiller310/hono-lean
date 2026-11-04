// Evaluate the exact pinned assignment in controlled contexts, separately from
// whole-router execution. Symbols, arbitrary accessors and proxies are not modeled here.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
const checkout = resolve(Bun.argv[2])
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
assert.equal(Bun.version, '1.4.0')
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
}
const document = JSON.parse(await Bun.stdin.text())
const meta = await Bun.file(new URL('./source.json', import.meta.url)).json()
const file = Buffer.from(await Bun.file(resolve(checkout, meta.sourcePath)).arrayBuffer())
// Artifact checker binds the selected text and the source metadata before this runs.
const pinned = await Bun.file(new URL('./assignment.ts.txt', import.meta.url)).text()
assert.equal(createHash('sha256').update(file).digest('hex'), meta.sourceSha256)
assert.equal(file.subarray(meta.startByte, meta.endByteExclusive).toString('ascii'), pinned)
const source = document.source ?? pinned
const apply = new Function('handlerSet', 'params', 'i', 'key', 'nodeParams',
  '"use strict";\nreturn (\n' + source + '\n)')
const fromUnits = (units: number[]) => {
  let text = ''
  for (const unit of units) text += String.fromCharCode(unit)
  return text
}
const toUnits = (text: string) => {
  const units = []
  for (let i = 0; i < text.length; i++) units.push(text.charCodeAt(i))
  return units
}
const results = document.cases.map((input: any) => {
  const key = fromUnits(input.key)
  const node = Object.create(Object.prototype)
  const params = Object.create(input.pMode === 'inherited' ? Object.prototype : null)
  const output = Object.create(null)
  if (input.prepopulate) output.seed = 'frame'
  const handler = Object.assign(Object.create(null), { params: output })
  const objects = [Object.prototype, node, params, output, handler]
  const array: unknown[] = []
  const decode = (value: any): any => {
    switch (value.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': case 'number': return value.value
      case 'string': return fromUnits(value.units)
      case 'object': return objects[value.ref]
      case 'array': return array
      case 'constructor': return Object
      default: throw new Error('Unknown packet value')
    }
  }
  const encode = (value: any): any => {
    if (value === undefined) return { kind: 'undefined' }
    if (value === null) return { kind: 'null' }
    if (typeof value === 'boolean') return { kind: 'bool', value }
    if (typeof value === 'number') return { kind: 'number', value }
    if (typeof value === 'string') return { kind: 'string', units: toUnits(value) }
    if (value === Object) return { kind: 'constructor' }
    if (value === array) return { kind: 'array', ref: 0 }
    const ref = objects.indexOf(value)
    if (ref >= 0) return { kind: 'object', ref }
    throw new Error('Unmodeled result')
  }
  if (input.nodeOwn) Object.defineProperty(node, key,
    { value: decode(input.node), writable: true, enumerable: true, configurable: true })
  if (input.pMode === 'own') Object.defineProperty(params, key,
    { value: decode(input.p), writable: true, enumerable: true, configurable: true })
  const optional = input.pMode === 'undefined' ? undefined : input.pMode === 'null' ? null : params
  const watched = [Object.prototype, node, params, handler]
  const snapshots = watched.map(value => Object.getOwnPropertyDescriptors(value))
  const returned = apply(handler, optional, input.index, key, node)
  const descriptor = Object.getOwnPropertyDescriptor(output, key)!
  assert('value' in descriptor)
  const frameKept = watched.every((value, index) => {
    const old = snapshots[index], current = Object.getOwnPropertyDescriptors(value)
    return Reflect.ownKeys(old).length === Reflect.ownKeys(current).length &&
      Reflect.ownKeys(old).every(key => {
        const a = old[key as keyof typeof old], b = current[key as keyof typeof current]
        return b && Object.is(a.value, b.value) && a.get === b.get && a.set === b.set &&
          a.writable === b.writable && a.enumerable === b.enumerable && a.configurable === b.configurable
      })
  }) && array.length === 0
  return { returned: encode(returned), output: encode(output[key]), own: Object.hasOwn(output, key),
    prototype: Object.getPrototypeOf(output), frameKept,
    retainedSeed: encode(output.seed), ownCount: Reflect.ownKeys(output).length,
    descriptor: { writable: descriptor.writable, enumerable: descriptor.enumerable, configurable: descriptor.configurable } }
})
console.log(JSON.stringify({ runtime: Bun.version, results }))
