// Controlled execution of exact Node75–81, not the whole class/method.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const checkout = resolve(Bun.argv[2])
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(Bun.version, '1.4.0')
assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
}
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const file = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
const pinned = await Bun.file(new URL('./loop.ts.txt', import.meta.url)).text()
assert.equal(createHash('sha256').update(file).digest('hex'), metadata.sourceSha256)
assert.equal(file.subarray(metadata.startByte, metadata.endByteExclusive).toString('ascii'), pinned)
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const packet = JSON.parse(await Bun.stdin.text())
const apply = new Function('handlerSet', 'handlerSets', 'params', 'nodeParams', 'createNullObject',
  'i', 'len', 'key', 'Object', '"use strict";\n' + (packet.source ?? pinned) + '\nreturn [i, len, key]')
const fromUnits = (units: number[]) => units.map(unit => String.fromCharCode(unit)).join('')
const toUnits = (text: string) => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i))
const compareKeys = (a: any, b: any) => {
  for (let i = 0; i < Math.min(a.key.length, b.key.length); i++)
    if (a.key[i] !== b.key[i]) return a.key[i] - b.key[i]
  return a.key.length - b.key.length
}
const results = packet.cases.map((input: any) => {
  const keys = input.keys.map(fromUnits)
  const node = Object.create(Object.prototype)
  const params = Object.create(input.parameterMode === 'ordinary' ? Object.prototype : null)
  const oldOutput = Object.assign(Object.create(null), { old: 'untouched' })
  const handler = { possibleKeys: keys, params: oldOutput }
  if (input.oldParamsSelf) handler.params = handler
  const other = Object.assign(Object.create(null), { marker: 'prior' })
  const objects = [Object.prototype, node, params, handler, oldOutput, other]
  const handlerSets = (input.priorHandlers ?? []).map((ref: number) => objects[ref])
  const arrays = [keys, handlerSets]
  const decode = (value: any): any => {
    switch (value.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': case 'number': return value.value
      case 'string': return fromUnits(value.units)
      case 'object': return objects[value.ref]
      case 'array': return arrays[value.ref]
      case 'constructor': return Object
      case 'function': assert.equal(value.ref, 0); return createNullObject
      default: throw new Error('Unknown input value')
    }
  }
  const define = (target: any, entries: any[]) => {
    for (const entry of entries) Object.defineProperty(target, fromUnits(entry.key),
      { value: decode(entry.value), writable: true, enumerable: true, configurable: true })
  }
  define(node, input.nodeEntries ?? [])
  define(params, input.parameterEntries ?? [])
  const parameter = input.parameterMode === 'undefined' ? undefined :
    input.parameterMode === 'null' ? null : input.parameterMode === 'handler' ? handler : params
  const nodeParameter = input.nodeMode === 'handler' ? handler : node
  const watched = objects.map(value => Object.getOwnPropertyDescriptors(value))
  const keySnapshot = [...keys]
  const callerObject = input.shadowObject ? null : Object
  const scope = apply(handler, handlerSets, parameter, nodeParameter, createNullObject, 55, 66, 'outer', callerObject)
  const output = handler.params
  objects.push(output)
  const encode = (value: any): any => {
    if (value === undefined) return { kind: 'undefined' }
    if (value === null) return { kind: 'null' }
    if (typeof value === 'boolean') return { kind: 'bool', value }
    if (typeof value === 'number') return { kind: 'number', value }
    if (typeof value === 'string') return { kind: 'string', units: toUnits(value) }
    if (value === Object) return { kind: 'constructor' }
    if (value === createNullObject) return { kind: 'function', ref: 0 }
    const array = arrays.indexOf(value)
    if (array >= 0) return { kind: 'array', ref: array }
    const ref = objects.indexOf(value)
    if (ref >= 0) return { kind: 'object', ref }
    throw new Error('Value outside controlled observation domain')
  }
  const entries = Reflect.ownKeys(output).map(key => {
    assert.equal(typeof key, 'string')
    const descriptor = Object.getOwnPropertyDescriptor(output, key)!
    assert('value' in descriptor)
    return { key: toUnits(key as string), value: encode(descriptor.value),
      writable: descriptor.writable, enumerable: descriptor.enumerable, configurable: descriptor.configurable }
  }).sort(compareKeys)
  const frameKept = objects.slice(0, 6).every((value, index) => {
    const old = watched[index], current = Object.getOwnPropertyDescriptors(value)
    return Reflect.ownKeys(old).length === Reflect.ownKeys(current).length && Reflect.ownKeys(old).every(key => {
      const a = old[key as keyof typeof old], b = current[key as keyof typeof current]
      if (index === 3 && key === 'params') return b && 'value' in b &&
        b.writable === a.writable && b.enumerable === a.enumerable && b.configurable === a.configurable
      return b && Object.is(a.value, b.value) && a.get === b.get && a.set === b.set &&
        a.writable === b.writable && a.enumerable === b.enumerable && a.configurable === b.configurable
    })
  }) && keys.length === keySnapshot.length && keys.every((key: string, i: number) => key === keySnapshot[i])
  return { output: encode(output), fresh: !objects.slice(0, 6).includes(output),
    nullPrototype: Object.getPrototypeOf(output) === null, entries,
    handlerSets: handlerSets.map(encode), scope: scope.map(encode), frameKept,
    oldOutputIntact: oldOutput.old === 'untouched' && Reflect.ownKeys(oldOutput).length === 1 }
})
console.log(JSON.stringify({ runtime: Bun.version, results }))
