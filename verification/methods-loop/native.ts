// Exact source loop inside explicit private-class/caller scaffolding.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const checkout = resolve(Bun.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args], { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
const sha = (bytes: string | Buffer) => createHash('sha256').update(bytes).digest('hex')
assert.equal(Bun.version, '1.4.0'); assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob); checkedPinnedBlobs++
}
const meta = await Bun.file(new URL('./source.json', import.meta.url)).json()
const nodeBytes = Buffer.from(await Bun.file(resolve(checkout, meta.sourcePath)).arrayBuffer())
const original = await Bun.file(new URL('./loop.ts.txt', import.meta.url)).text()
assert.equal(sha(nodeBytes), meta.sourceSha256); assert.equal(sha(original), meta.fragmentSha256)
assert.equal(nodeBytes.subarray(meta.startByte, meta.endByteExclusive).toString('ascii'), original)
const packet = JSON.parse(await Bun.stdin.text()), source = packet.source ?? original
const wrapper = `function build(methods) { class Holder { #methods = methods;
  consume(node, handlerSets, method, nodeParams, params, createNullObject, METHOD_NAME_ALL) {
    let i = 'outer-i', len = 'outer-len', m = 'outer-m', handlerSet = 'outer-handler', key = 'outer-key';
    ${source}
    return [i, len, m, handlerSet, key]
  }
  rows() { return this.#methods }
} return new Holder() }`
const emitted = new Bun.Transpiler({ loader: 'ts' }).transformSync(wrapper)
const build = new Function(emitted + '\nreturn build')()
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const { METHOD_NAME_ALL } = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const string = (value: number[]) => value.map(unit => String.fromCharCode(unit)).join('')
const units = (value: string) => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))
const define = (target: object, key: string, value: unknown) => Object.defineProperty(target, key, { value, writable: true, enumerable: true, configurable: true })
const values: Record<string, unknown> = { u: undefined, n: null, f: false, z: 0, empty: '', t: true, one: 1, text: 'x' }
const encode = (value: unknown): unknown => {
  if (value === undefined) return { kind: 'undefined' }; if (value === null) return { kind: 'null' }
  if (typeof value === 'boolean') return { kind: 'bool', value }
  if (typeof value === 'number') return { kind: 'number', value }
  if (typeof value === 'string') return { kind: 'string', units: units(value) }
  throw new Error('Unsupported capture value')
}
const entries = (target: object) => Object.getOwnPropertyNames(target).sort((a, b) => a < b ? -1 : a > b ? 1 : 0).map(key => {
  const d = Object.getOwnPropertyDescriptor(target, key)!
  return { key: units(key), value: encode(d.value), writable: d.writable, enumerable: d.enumerable, configurable: d.configurable }
})
const results = (packet.cases ?? []).map((input: any) => {
  const prior = Object.create(null); define(prior, 'marker', 'prior')
  const records = input.records.map((keys: number[][], index: number) => ({ handler: index, possibleKeys: keys.map(string), score: 100 + index, params: prior }))
  const decode = (code: string) => code.startsWith('r') ? records[Number(code.slice(1))] : values[code]
  const fill = (target: object, fields: any[]) => { for (const [key, value] of fields) define(target, string(key), decode(value)); return target }
  const prototypes: any[] = []
  const methods = input.rows.map((row: any) => {
    const prototype = fill(Object.create(null), row.inherited ?? []); prototypes.push(prototype)
    return fill(Object.create(row.nullPrototype ? null : prototype), row.own ?? [])
  })
  const snapshots = methods.map(Object.getOwnPropertyDescriptors), prototypeSnapshots = prototypes.map(Object.getOwnPropertyDescriptors)
  const keysBefore = records.map((record: any) => record.possibleKeys.slice())
  const collector: any[] = Array(input.priorCount ?? 0).fill(prior), node = build(methods)
  const nodeParams = fill(Object.create(null), input.nodeEntries ?? [])
  const parameterObject = fill(Object.create(null), input.parameterEntries ?? [])
  const params = input.parameterMode === 'null' ? null : input.parameterMode === 'undefined' ? undefined : parameterObject
  const allocations: any[] = []
  const trackedCreate = () => { const value = createNullObject(); allocations.push(value); return value }
  const scope = node.consume(node, collector, string(input.method), nodeParams, params, trackedCreate, METHOD_NAME_ALL)
  const unchanged = (value: object, before: object) => Reflect.ownKeys(value).length === Reflect.ownKeys(before).length && Reflect.ownKeys(before).every(key => {
    const a = Object.getOwnPropertyDescriptor(value, key)!, b = (before as any)[key]
    return a.value === b.value && a.writable === b.writable && a.enumerable === b.enumerable && a.configurable === b.configurable
  })
  return { collector: collector.map(value => value === prior ? -1 : records.indexOf(value)),
    recordParams: records.map((record: any) => allocations.indexOf(record.params)),
    collectorParams: collector.map(value => allocations.indexOf(value.params)),
    allocations: allocations.map(entries), nullPrototypes: allocations.every(value => Object.getPrototypeOf(value) === null),
    methodsKept: node.rows() === methods && methods.length === input.rows.length && methods.every((value: any, index: number) => unchanged(value, snapshots[index]) && unchanged(prototypes[index], prototypeSnapshots[index])),
    keysKept: records.every((record: any, index: number) => record.possibleKeys.length === keysBefore[index].length && record.possibleKeys.every((key: string, at: number) => key === keysBefore[index][at])),
    handlerFieldsKept: records.every((record: any, index: number) => record.handler === index && record.score === 100 + index), scope }
})
let scopeProbes: unknown = null
if (packet.scopeProbes) {
  // These effectful cases deliberately exceed the normal pure-read proof domain.
  const scopeRun = (prepare: (methods: any[], collector: any[], node: any) => void) => {
    const record = { handler: 'x', possibleKeys: [] }, methods: any[] = [], collector: any[] = [], node = build(methods)
    methods.push({ GET: record }); prepare(methods, collector, node)
    try { node.consume(node, collector, 'GET', Object.create(null), undefined, createNullObject, METHOD_NAME_ALL); return { count: collector.length, rows: methods.length, error: false } }
    catch { return { count: collector.length, rows: methods.length, error: true } }
  }
  const appended = scopeRun((methods) => { const row = methods[0]; Object.defineProperty(row, 'GET', { get() { methods.push(row); return { possibleKeys: [] } } }) })
  const replaced = scopeRun((methods) => { methods.push({ GET: { possibleKeys: [] } }); Object.defineProperty(methods[0], 'GET', { get() { methods[1] = { GET: false }; return { possibleKeys: [] } } }) })
  const shrunk = scopeRun((methods) => { methods.push({ GET: { possibleKeys: [] } }); Object.defineProperty(methods[0], 'GET', { get() { methods.length = 0; return { possibleKeys: [] } } }) })
  const truthyInvalid = scopeRun((methods) => { methods[0] = { GET: 17 } })
  const shared: any[] = [{ GET: { possibleKeys: [] } }], aliasNode = build(shared)
  aliasNode.consume(aliasNode, shared, 'GET', Object.create(null), undefined, createNullObject, METHOD_NAME_ALL)
  const aliasedCollector = { length: shared.length, appendedHandler: shared[1] === shared[0].GET }
  const { Node } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/node.ts')).href)
  const real = new Node<string>()
  for (const [method, label] of [['GET', 'get'], ['ALL', 'all'], ['POST', 'post'], ['GET', 'second']]) real.insert(method, '/item/:id', label)
  const actualNode = Object.fromEntries(['GET', 'POST', 'HEAD', 'DELETE'].map(method => [method,
    real.search(method, '/item/42')[0].map(([handler, params]: any) => [handler, params.id])]))
  scopeProbes = { appended, replaced, shrunk, truthyInvalid, aliasedCollector, actualNode }
}
process.stdout.write(JSON.stringify({ revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { verified: false, loader: 'ts', inputSha256: sha(wrapper), emittedSha256: sha(emitted) }, results, scopeProbes }) + '\n')
