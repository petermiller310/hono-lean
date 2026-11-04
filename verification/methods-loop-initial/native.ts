// Actual registration -> later collector -> full loop, with explicit class/call scaffolding.
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
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const nodeBytes = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
assert.equal(sha(nodeBytes), metadata.sourceSha256)
const fragments: Record<string, string> = {}
for (const [name, entry] of Object.entries<any>(metadata.fragments)) {
  const source = await Bun.file(resolve(import.meta.dir, '../..', entry.sourceCopy)).text()
  assert.equal(sha(source), entry.sha256)
  assert.equal(nodeBytes.subarray(entry.startByte, entry.endByteExclusive).toString('ascii'), source)
  fragments[name] = source
}
const packet = JSON.parse(await Bun.stdin.text())
const wrapper = `function make(createNullObject, METHOD_NAME_ALL, initialOrder = 0) { let order = initialOrder;
  function collect() { ${packet.collectorSource ?? fragments.collector} return handlerSets }
  class Holder { #methods = [];
    register(method, handler, possibleKeys) { const curNode = this; return (${packet.registrationSource ?? fragments.registration}) }
    consume(node, handlerSets, method, nodeParams, params) { ${packet.loopSource ?? fragments.loop} }
    stored() { return this.#methods }
  }
  return { node: new Holder(), collect, order: () => order }
}`
const emitted = new Bun.Transpiler({ loader: 'ts' }).transformSync(wrapper)
const make = new Function(emitted + '\nreturn make')()
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const { METHOD_NAME_ALL } = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const string = (value: number[]) => value.map(unit => String.fromCharCode(unit)).join('')
const units = (value: string) => Array.from({ length: value.length }, (_, i) => value.charCodeAt(i))
const scalar: Record<string, unknown> = { u: undefined, n: null, f: false, z: 0, empty: '', t: true, one: 1, text: 'x' }
const define = (target: object, key: string, value: unknown) => Object.defineProperty(target, key, { value, writable: true, enumerable: true, configurable: true })
const encode = (value: unknown): unknown => {
  if (value === undefined) return { kind: 'undefined' }; if (value === null) return { kind: 'null' }
  if (typeof value === 'boolean') return { kind: 'bool', value }
  if (typeof value === 'number') return { kind: 'number', value }
  if (typeof value === 'string') return { kind: 'string', units: units(value) }
  throw new Error('Unsupported observed capture value')
}
const entries = (target: object) => Object.getOwnPropertyNames(target).sort((a, b) => a < b ? -1 : a > b ? 1 : 0).map(key => {
  const d = Object.getOwnPropertyDescriptor(target, key)!
  return { key: units(key), value: encode(d.value), writable: d.writable, enumerable: d.enumerable, configurable: d.configurable }
})
const sameDescriptors = (target: object, before: any) => Reflect.ownKeys(target).length === Reflect.ownKeys(before).length && Reflect.ownKeys(before).every(key => {
  const a = Object.getOwnPropertyDescriptor(target, key)!, b = before[key]
  return a.value === b.value && a.writable === b.writable && a.enumerable === b.enumerable && a.configurable === b.configurable
})
const results = (packet.cases ?? []).map((input: any) => {
  const allocations: any[] = []
  const fixture = make(() => { const output = createNullObject(); allocations.push(output); return output }, METHOD_NAME_ALL, input.startOrder ?? 0)
  const steps: any[] = []
  const handlerValue = (registration: any, index: number) => registration.handlerCode === undefined ? index : scalar[registration.handlerCode]
  for (const [index, registration] of input.registrations.entries()) {
    const before = fixture.node.stored(), priorRows = before.slice()
    const priorRecords = priorRows.map((row: any, at: number) => Object.getOwnPropertyDescriptor(row, string(input.registrations[at].method))!.value)
    const rowDescriptors = priorRows.map(Object.getOwnPropertyDescriptors), recordDescriptors = priorRecords.map(Object.getOwnPropertyDescriptors)
    const priorKeys = priorRecords.map((record: any) => record.possibleKeys.slice()), oldKeyArrays = priorRecords.map((record: any) => record.possibleKeys)
    const returned = fixture.node.register(string(registration.method), handlerValue(registration, index), new Set(registration.names.map(string)))
    if (packet.observePrefixes) {
      const current = fixture.node.stored(), row = current.at(-1), record = Object.getOwnPropertyDescriptor(row, string(registration.method))!.value
      steps.push({ returned, count: current.length, order: fixture.order(), score: record.score,
        method: registration.method, handler: encode(record.handler), keys: record.possibleKeys.map(units),
        oldRowsKept: priorRows.every((value: any, at: number) => current[at] === value && sameDescriptors(value, rowDescriptors[at])),
        oldRecordsKept: priorRecords.every((value: any, at: number) => sameDescriptors(value, recordDescriptors[at])),
        oldKeysKept: priorRecords.every((value: any, at: number) => value.possibleKeys === oldKeyArrays[at] && value.possibleKeys.length === priorKeys[at].length && value.possibleKeys.every((key: string, k: number) => key === priorKeys[at][k])),
        rowFresh: row !== record && !priorRows.includes(row) && !priorRecords.includes(row),
        recordFresh: !priorRows.includes(record) && !priorRecords.includes(record),
        keysFresh: record.possibleKeys !== current && !oldKeyArrays.includes(record.possibleKeys), privateArrayKept: current === before })
    }
  }
  const methods = fixture.node.stored()
  const records = methods.map((row: any, index: number) => Object.getOwnPropertyDescriptor(row, string(input.registrations[index].method))!.value)
  const keyArrays = records.map((record: any) => record.possibleKeys), keyOrder = keyArrays.map((keys: string[]) => keys.map(units))
  const fill = (fields: any[]) => { const value = Object.create(null); for (const [key, code] of fields ?? []) define(value, string(key), scalar[code]); return value }
  const nodeParams = fill(input.nodeEntries), parameterObject = fill(input.parameterEntries)
  const params = input.parameterMode === 'null' ? null : input.parameterMode === 'undefined' ? undefined : parameterObject
  const collectors: any[][] = []
  for (const query of input.queries) { const collector = fixture.collect(); collectors.push(collector); fixture.node.consume(fixture.node, collector, string(query), nodeParams, params) }
  return { ...(packet.observePrefixes ? { registrationSteps: steps } : {}), collectors: collectors.map(collector => collector.map(record => records.indexOf(record))),
    recordParams: records.map((record: any) => allocations.indexOf(record.params)),
    collectorParams: collectors.map(collector => collector.map(record => allocations.indexOf(record.params))),
    allocations: allocations.map(entries), nullPrototypes: allocations.every(value => Object.getPrototypeOf(value) === null),
    keyOrder, scores: records.map((record: any) => record.score), order: fixture.order(),
    collectorsFresh: collectors.every((collector, index) => collector !== methods && !keyArrays.includes(collector) && !collectors.slice(0, index).includes(collector)),
    storedShape: fixture.node.stored() === methods && methods.length === input.registrations.length && methods.every((row: any, index: number) => {
      const key = string(input.registrations[index].method), record = records[index], descriptor = Object.getOwnPropertyDescriptor(row, key)
      return Object.getPrototypeOf(row) === Object.prototype && Object.getOwnPropertyNames(row).length === 1 && descriptor?.value === record &&
        descriptor.writable && descriptor.enumerable && descriptor.configurable && Object.getPrototypeOf(record) === Object.prototype &&
        record.handler === handlerValue(input.registrations[index], index) && record.possibleKeys === keyArrays[index]
    }) }
})
let scopeProbes: unknown = null
if (packet.scopeProbes) {
  const runReserved = (query: string) => {
    const fixture = make(createNullObject, METHOD_NAME_ALL); fixture.node.register('ALL', 'all', new Set(['id']))
    const collector = fixture.collect()
    try { fixture.node.consume(fixture.node, collector, query, Object.create(null), undefined); return { error: false, appended: collector.length } }
    catch { return { error: true, appended: collector.length } }
    finally { delete (Object as any).params; delete (Object.prototype.toString as any).params; delete (Object.prototype as any).params }
  }
  let setterCalls = 0
  const fixture = make(createNullObject, METHOD_NAME_ALL); fixture.node.register('GET', 'get', new Set(['id']))
  const collector = fixture.collect()
  Object.defineProperty(Object.prototype, 'params', { set() { setterCalls++ }, configurable: true })
  let inheritedSetterError = false
  try { fixture.node.consume(fixture.node, collector, 'GET', Object.create(null), undefined) } catch { inheritedSetterError = true }
  finally { delete (Object.prototype as any).params }
  scopeProbes = { constructor: runReserved('constructor'), toString: runReserved('toString'), proto: runReserved('__proto__'),
    inheritedSetter: { calls: setterCalls, error: inheritedSetterError, appended: collector.length } }
}
let historyScope: unknown = null
if (packet.historyScope) {
  const unsafe = make(createNullObject, METHOD_NAME_ALL, 9007199254740991)
  unsafe.node.register('GET', 'same', new Set()); unsafe.node.register('GET', 'same', new Set())
  const unsafeRecords = unsafe.node.stored().map((row: any) => row.GET)
  const effects = make(createNullObject, METHOD_NAME_ALL)
  effects.node.register('GET', 'first', new Set(['id']))
  const first = effects.node.stored()[0].GET, oldScore = first.score
  const supplied: any = new Set(['name'])
  supplied[Symbol.iterator] = function* () { first.score = -1; yield 'name' }
  effects.node.register('POST', 'second', supplied)
  const { Node } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/node.ts')).href)
  const real = new Node(), same = () => null
  for (const method of ['GET', 'ALL', 'POST']) real.insert(method, '/item/:id', same)
  const firstResult = real.search('GET', '/item/one')[0], secondResult = real.search('GET', '/item/two')[0]
  historyScope = { unsafeScores: unsafeRecords.map((record: any) => record.score), unsafeOrder: unsafe.order(),
    sameUserHandlerDistinctRecords: unsafeRecords[0] !== unsafeRecords[1] && unsafeRecords[0].handler === unsafeRecords[1].handler,
    iteratorEffects: { oldScore, changedScore: first.score, secondScore: effects.node.stored()[1].POST.score, count: effects.node.stored().length },
    actualNode: { counts: [firstResult.length, secondResult.length], sameHandler: firstResult.every(([handler]: any) => handler === same),
      distinctFirstParams: firstResult[0][1] !== firstResult[1][1], freshNextParams: secondResult[0][1] !== firstResult[0][1],
      priorIds: firstResult.map(([, params]: any) => params.id), nextIds: secondResult.map(([, params]: any) => params.id) } }
}
process.stdout.write(JSON.stringify({ revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { verified: false, loader: 'ts', inputSha256: sha(wrapper), emittedSha256: sha(emitted) }, results, scopeProbes, historyScope }) + '\n')
