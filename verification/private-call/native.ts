// Exact private method and two actual call entries inside explicit class scaffolding.
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
const originals: Record<string, string> = {}
for (const [name, file] of Object.entries({ method: 'method.ts.txt', four: 'call-four.ts.txt', five: 'call-five.ts.txt' })) {
  const text = await Bun.file(new URL(file, import.meta.url)).text(), span = meta.fragments[name]
  assert.equal(sha(text), span.sha256)
  assert.equal(nodeBytes.subarray(span.startByte, span.endByteExclusive).toString('ascii'), text)
  originals[name] = text
}
assert.equal(sha(nodeBytes), meta.sourceSha256)
const packet = JSON.parse(await Bun.stdin.text())
const methodSource = packet.methodSource ?? originals.method
const fourSource = packet.fourSource ?? originals.four, fiveSource = packet.fiveSource ?? originals.five
const wrapper = `function build(createNullObject, METHOD_NAME_ALL) { class Holder {
  #methods; #params;
  constructor(methods, params) { this.#methods = methods; this.#params = params }
  ${methodSource}
  consume(kind, node, child, handlerSets, method, params) {
    let i = 'outer-i', len = 'outer-len', m = 'outer-m', handlerSet = 'outer-handler', key = 'outer-key';
    const nextNode = child;
    let returned;
    if (kind === 'four') { returned = ${fourSource.trim()} }
    else { returned = ${fiveSource.trim()} }
    return { scope: [i, len, m, handlerSet, key], returned }
  }
  rows() { return this.#methods }
} return Holder }`
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
  const collector: any[] = Array(input.priorCount ?? 0).fill(prior)
  const nodeParams = fill(Object.create(null), input.nodeEntries ?? [])
  const parameterObject = fill(Object.create(null), input.parameterEntries ?? [])
  const params = input.parameterMode === 'null' ? null : input.parameterMode === 'undefined' ? undefined : parameterObject
  const allocations: any[] = []
  const trackedCreate = () => { const value = createNullObject(); allocations.push(value); return value }
  const Holder = build(trackedCreate, METHOD_NAME_ALL)
  const root = new Holder([], undefined), parent = new Holder([], nodeParams), child = new Holder(methods, undefined)
  const { scope, returned } = root.consume(input.callKind ?? 'four', parent, child, collector, string(input.method), params)
  const unchanged = (value: object, before: object) => Reflect.ownKeys(value).length === Reflect.ownKeys(before).length && Reflect.ownKeys(before).every(key => {
    const a = Object.getOwnPropertyDescriptor(value, key)!, b = (before as any)[key]
    return a.value === b.value && a.writable === b.writable && a.enumerable === b.enumerable && a.configurable === b.configurable
  })
  return { collector: collector.map(value => value === prior ? -1 : records.indexOf(value)),
    recordParams: records.map((record: any) => allocations.indexOf(record.params)),
    collectorParams: collector.map(value => allocations.indexOf(value.params)),
    allocations: allocations.map(entries), nullPrototypes: allocations.every(value => Object.getPrototypeOf(value) === null),
    methodsKept: child.rows() === methods && methods.length === input.rows.length && methods.every((value: any, index: number) => unchanged(value, snapshots[index]) && unchanged(prototypes[index], prototypeSnapshots[index])),
    keysKept: records.every((record: any, index: number) => record.possibleKeys.length === keysBefore[index].length && record.possibleKeys.every((key: string, at: number) => key === keysBefore[index][at])),
    returned: encode(returned), handlerFieldsKept: records.every((record: any, index: number) => record.handler === index && record.score === 100 + index), scope }
})
let scopeProbes: unknown = null
if (packet.scopeProbes) {
  let effects: string[] = []
  class Probe {
    #f(a: unknown, b?: unknown) { effects.push('body'); return [this === receiver, a, b] }
    call(target: Probe) { return target.#f((effects.push('arg0'), 7), (effects.push('arg1'), undefined)) }
    omitted() { return this.#f(9) }
    extra() { return this.#f(1, 2, (effects.push('extra'), 3)) }
  }
  const receiver = new Probe(), dispatcher = new Probe()
  let brandFailed = false
  try { dispatcher.call({} as Probe) } catch { brandFailed = true }
  const badBrandEffects = effects.slice(); effects = []
  const normal = dispatcher.call(receiver), normalEffects = effects.slice(); effects = []
  const omitted = receiver.omitted().map(x => x === undefined ? 'undefined' : x)
  effects = []; receiver.extra(); const extraEffects = effects.slice()
  let callableEffects: string[] = []
  class Mutable {
    #f: any = (x: unknown) => { callableEffects.push('old-body'); return x }
    call() { return this.#f((this.#f = () => 99, callableEffects.push('argument'), 17)) }
    noncallable() { this.#f = 0; return this.#f((callableEffects.push('before-rejection'), 1)) }
  }
  const mutable = new Mutable(), capturedResult = mutable.call()
  let noncallableFailed = false
  try { mutable.noncallable() } catch { noncallableFailed = true }
  scopeProbes = { brandFailed, badBrandEffects, normal, normalEffects, omitted, extraEffects,
    capturedResult, noncallableFailed, callableEffects }
}
process.stdout.write(JSON.stringify({ revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { verified: false, loader: 'ts', inputSha256: sha(wrapper), emittedSha256: sha(emitted) }, results, scopeProbes }) + '\n')
