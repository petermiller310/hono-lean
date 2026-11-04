// Exact noncontiguous source fragments, with caller/class/activation scaffolding.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const checkout = resolve(Bun.argv[2]), pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args], { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
const sha = (value: string | Buffer) => createHash('sha256').update(value).digest('hex')
assert.equal(Bun.version, '1.4.0'); assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob); checkedPinnedBlobs++
}
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const files: Record<string, Buffer> = {}
for (const [name, info] of Object.entries<any>(metadata.sources)) {
  files[name] = Buffer.from(await Bun.file(resolve(checkout, name)).arrayBuffer()); assert.equal(sha(files[name]), info.sha256)
}
const texts: Record<string, string> = {}
for (const [name, info] of Object.entries<any>(metadata.fragments)) {
  texts[name] = await Bun.file(new URL(`./${name}.ts.txt`, import.meta.url)).text()
  assert.equal(files[info.sourcePath].subarray(info.startByte, info.endByteExclusive).toString('ascii'), texts[name])
  assert.equal(sha(texts[name]), info.sha256)
}
const packet = JSON.parse(await Bun.stdin.text()), transpiler = new Bun.Transpiler({ loader: 'ts' })
const compilations: Record<string, unknown> = {}
const compile = (name: string, source: string, result: string) => {
  const emitted = transpiler.transformSync(source)
  compilations[name] = { inputSha256: sha(source), emittedSha256: sha(emitted) }
  return new Function(emitted + '\nreturn ' + result)()
}
const select = compile('selection', `function select(m, method, METHOD_NAME_ALL) { ${packet.selectionSource ?? texts.selection} return handlerSet }`, 'select')
const selectWithoutAll = compile('lazy', `function select(m, method) { ${texts.selection} return handlerSet }`, 'select')
const collect = compile('collector', `function collect() { ${packet.collectorSource ?? texts.collector} return handlerSets }`, 'collect')
const all = compile('all', `function all() { return (${packet.allSource ?? texts.all}) }`, 'all')()
const { METHOD_NAME_ALL } = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
if (packet.allSource === undefined) assert.equal(all, METHOD_NAME_ALL)
const fromUnits = (value: number[]) => value.map(unit => String.fromCharCode(unit)).join('')
const toUnits = (text: string) => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i))
const results = (packet.cases ?? []).map((input: any) => {
  const inherited = Object.create(Object.prototype), m = Object.create(input.nullPrototype ? null : inherited)
  const direct = Object.create(null), fallback = Object.create(null), array: unknown[] = [], set = new Set()
  const values: Record<string, unknown> = { u: undefined, n: null, f: false, t: true, z: 0, one: 1, empty: '', text: 'x',
    direct, all: fallback, row: m, prototype: Object.prototype, custom: inherited, array, set,
    function: Object.prototype.toString, Object, Set }
  const define = (target: object, entries: any[]) => { for (const [key, code] of entries) Object.defineProperty(target, fromUnits(key), { value: values[code], writable: true, enumerable: true, configurable: true }) }
  define(inherited, input.inherited); define(m, input.own)
  const snapshot = Object.getOwnPropertyDescriptors(m), prototypeSnapshot = Object.getOwnPropertyDescriptors(inherited)
  const value = input.omitAll ? selectWithoutAll(m, fromUnits(input.method)) : select(m, fromUnits(input.method), all)
  const encode = (value: any): any => {
    if (value === undefined) return { tag: 'u' }; if (value === null) return { tag: 'n' }
    if (typeof value === 'boolean') return { tag: 'boolean', value }
    if (typeof value === 'number') return { tag: 'number', value }
    if (typeof value === 'string') return { tag: 'string', value: toUnits(value) }
    for (const code of ['direct', 'all', 'row', 'prototype', 'custom', 'array', 'set', 'function', 'Object', 'Set']) if (value === values[code]) return { tag: code }
    throw new Error('Unobserved value domain')
  }
  const unchanged = (target: object, before: any) => Reflect.ownKeys(target).length === Reflect.ownKeys(before).length && Reflect.ownKeys(before).every(key => {
    const after = Object.getOwnPropertyDescriptor(target, key), old = before[key]
    return after && after.value === old.value && after.writable === old.writable && after.enumerable === old.enumerable && after.configurable === old.configurable
  })
  return { chosen: encode(value), frameKept: unchanged(m, snapshot) && unchanged(inherited, prototypeSnapshot) && array.length === 0 && set.size === 0 }
})
const nodeFile = files['src/router/trie-router/node.ts']
const pushMeta = await Bun.file(new URL('../methods-push/source.json', import.meta.url)).json()
const push = await Bun.file(new URL('../methods-push/source.ts.txt', import.meta.url)).text()
assert.equal(sha(push), pushMeta.fragment.sha256); assert.equal(nodeFile.subarray(pushMeta.fragment.startByte, pushMeta.fragment.endByteExclusive).toString('ascii'), push)
const loopMeta = await Bun.file(new URL('../param-loop/source.json', import.meta.url)).json()
const loop = nodeFile.subarray(loopMeta.startByte, loopMeta.endByteExclusive).toString('ascii'); assert.equal(sha(loop), loopMeta.fragmentSha256)
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const make = compile('integration', `function make(initialOrder) { let order = initialOrder;
  class Holder { #methods; constructor(methods) { this.#methods = methods }
    register(method, handler, possibleKeys) { const curNode = this; return (${push}) }
    consume(node, i, method, METHOD_NAME_ALL, handlerSets, params, nodeParams, createNullObject) {
      ${packet.rowSource ?? texts.row}
      ${packet.selectionSource ?? texts.selection}
      ${loop}
      return { m, handlerSet }
    }
    methods() { return this.#methods }
  }
  return { Holder, order() { return order } }
}`, 'make')
const integrations = (packet.integrations ?? []).map((input: any) => {
  const possibleKeys = new Set<string>(input.names.map(fromUnits)), keys = [...possibleKeys]
  const method = fromUnits(input.method)
  const compiled = make(7), priorHandler = () => null, priorMap = { [method]: { handler: priorHandler, possibleKeys: [], score: -1 } }
  const methods = Array(input.priorCount).fill(priorMap), node = new compiled.Holder(methods), handler = () => null
  node.register(method, handler, possibleKeys)
  const handlerSets = collect(), params = Object.create(null), nodeParams = Object.create(null)
  for (const key of keys) { Object.defineProperty(params, key, { value: 'prior', enumerable: true, writable: true, configurable: true }); Object.defineProperty(nodeParams, key, { value: 'node', enumerable: true, writable: true, configurable: true }) }
  const selected = node.consume(node, input.priorCount, method, all, handlerSets, params, nodeParams, createNullObject)
  const nextCollector = collect(), captured = selected.handlerSet.params
  return { collectorFresh: handlerSets !== methods && handlerSets !== selected.handlerSet.possibleKeys,
    collectorLength: handlerSets.length, selectedStoredRow: selected.m === methods[input.priorCount],
    selectedStoredHandler: selected.handlerSet === Object.getOwnPropertyDescriptor(selected.m, method)?.value,
    collectorHasSelected: handlerSets[0] === selected.handlerSet, handlerKept: selected.handlerSet.handler === handler,
    captures: selected.handlerSet.possibleKeys.map((key: string) => [toUnits(key), toUnits(captured[key])]),
    ownCaptureCount: Reflect.ownKeys(captured).length, nullPrototype: Object.getPrototypeOf(captured) === null,
    descriptors: selected.handlerSet.possibleKeys.every((key: string) => { const d = Object.getOwnPropertyDescriptor(captured, key); return d?.writable && d?.enumerable && d?.configurable }),
    nextCollectorFreshEmpty: nextCollector !== handlerSets && nextCollector.length === 0, firstCollectorKept: handlerSets.length === 1,
    methodsCount: methods.length, prefixKept: methods.slice(0, input.priorCount).every((value: any) => value === priorMap),
    score: selected.handlerSet.score, orderAfter: compiled.order(), privateArrayKept: node.methods() === methods }
})
let scope: unknown = null
if (packet.scopeProbes) {
  const calls: string[] = [], record = {}, repeated: any = {}
  let read = 0
  Object.defineProperty(repeated, 'ALL', { get() { calls.push('ALL'); return read++ === 0 ? 0 : record } })
  const repeatedChosen = select(repeated, 'ALL', all) === record
  let skippedReads = 0
  const lazy = Object.create(null); Object.defineProperty(lazy, 'GET', { value: [] }); Object.defineProperty(lazy, 'ALL', { get() { skippedReads++; throw new Error('must skip') } })
  const skipped = select(lazy, 'GET', all) === lazy.GET
  const falsyFallbacks = [undefined, null, false, 0, ''].map(value => select({ GET: value, ALL: record }, 'GET', all) === record)
  const inheritedMap = { ALL: record }
  const inherited = { constructor: select(inheritedMap, 'constructor', all) === Object,
    toString: select(inheritedMap, 'toString', all) === Object.prototype.toString,
    proto: select(inheritedMap, '__proto__', all) === Object.prototype }
  const castDoesNotGuard = select({ GET: 17 }, 'GET', all) === 17
  const { Node } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/node.ts')).href)
  const real = new Node(), get = () => null, every = () => null
  real.insert('GET', '/item', get); real.insert('ALL', '/item', every)
  const labels = (method: string) => real.search(method, '/item')[0].map((entry: any) => entry[0] === get ? 'get' : 'all')
  scope = { repeatedChosen, repeatedReads: calls, skipped, skippedReads, falsyFallbacks, inherited, castDoesNotGuard,
    actualNode: { GET: labels('GET'), POST: labels('POST'), HEAD: labels('HEAD') } }
}
process.stdout.write(JSON.stringify({ revision: pin, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { loader: 'ts', verified: false, compilations }, all, results, integrations, scope }) + '\n')
