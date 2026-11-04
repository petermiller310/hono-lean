// Finite observations. No server/network call or upstream modification occurs.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
assert.equal(Bun.version, '1.4.0')
const checkout = resolve(Bun.argv[2])
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } }).trim()
assert.equal(git('rev-parse', 'HEAD'), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all'), '')
assert.equal(git('rev-parse', '--show-object-format'), 'sha1')
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t')
  const [mode, kind, blob] = entry.slice(0, tab).split(' ')
  assert(kind === 'blob' && ['100644', '100755'].includes(mode))
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
}
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const { TrieRouter } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/router.ts')).href)
const document = JSON.parse(await Bun.stdin.text())
const fromUnits = (units: number[]) => {
  let value = ''
  for (const unit of units) value += String.fromCharCode(unit)
  return value
}
const toUnits = (value: string) => {
  const result = []
  for (let index = 0; index < value.length; index++) result.push(value.charCodeAt(index))
  return result
}
const tagged = (value: unknown) => {
  if (typeof value === 'string') return { string: toUnits(value) }
  if (value === Object.prototype) return { object: 0 }
  if (value === null) return null
  if (value === undefined) return { undefined: true }
  throw new Error('Unexpected native value')
}
const allocations = document.allocations.map((count: number) => {
  const frame = Array.from({ length: count }, () => createNullObject())
  const first = createNullObject(), second = createNullObject()
  return { first: count, second: count + 1, distinct: first !== second,
    length: count + 2, emptyOwn: Reflect.ownKeys(first).length === 0,
    prototype: Object.getPrototypeOf(first), extensible: Object.isExtensible(first),
    frameKept: frame.every(value => Reflect.ownKeys(value).length === 0 && Object.getPrototypeOf(value) === null) }
})
const transfers = document.transfers.map((input: any) => {
  const key = fromUnits(input.key)
  const temporary: Record<string, unknown> = {}
  temporary[key] = fromUnits(input.contents)
  const temporaryHasOwn = Object.hasOwn(temporary, key)
  const output = createNullObject()
  const readValue = temporary[key]
  output[key] = readValue
  const descriptor = Object.getOwnPropertyDescriptor(output, key)!
  assert('value' in descriptor)
  return { temporaryHasOwn, readValue: tagged(readValue), outputHasOwn: Object.hasOwn(output, key),
    outputValue: tagged(output[key]), outputPrototype: Object.getPrototypeOf(output),
    descriptor: { kind: 'data', value: tagged(descriptor.value), writable: descriptor.writable,
      enumerable: descriptor.enumerable, configurable: descriptor.configurable } }
})
const raw = ['__proto__', 'id', 'constructor'].map(name => {
  const router = new TrieRouter()
  router.add('GET', `/:${name}`, 'capture')
  const result = router.match('GET', '/alpha')
  const params = result[0][0][1]
  return { name, handler: result[0][0][0], own: Object.hasOwn(params, name),
    value: tagged(params[name]), prototype: Object.getPrototypeOf(params) }
})
console.log(JSON.stringify({ runtime: Bun.version, allocations, transfers, raw,
  realm: { legacyAccessor: typeof Object.getOwnPropertyDescriptor(Object.prototype, '__proto__')?.set === 'function',
    prototypeHasOtherProperties: Object.getOwnPropertyNames(Object.prototype).length > 2,
    prototypeEnumerableKeys: Object.keys(Object.prototype), prototypeJSON: JSON.stringify(Object.prototype) } }))
