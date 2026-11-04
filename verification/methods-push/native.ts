// Exact private push expression in a declared class/caller context. The wrapper
// stages private initialization; it is not the complete upstream Node class.
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
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const file = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
const original = await Bun.file(new URL('./source.ts.txt', import.meta.url)).text()
assert.equal(createHash('sha256').update(file).digest('hex'), metadata.sourceSha256)
assert.equal(file.subarray(metadata.fragment.startByte, metadata.fragment.endByteExclusive).toString('ascii'), original)
assert.equal(createHash('sha256').update(original).digest('hex'), metadata.fragment.sha256)
const packet = JSON.parse(await Bun.stdin.text())
const source = packet.source ?? original
const makeClass = (text: string, initialOrder: number) => new Function('initialOrder', `let order = initialOrder;
  class Holder {
    #methods; #patterns;
    constructor(methods, patterns = []) { this.#methods = methods; this.#patterns = patterns }
    run(method, handler, possibleKeys) { const curNode = this; return (${text}) }
    methods() { return this.#methods }
    patterns() { return this.#patterns }
    replaceMethods(value) { this.#methods = value }
  }
  return { Holder, order() { return order } }`)(initialOrder)
const fromUnits = (units: number[]) => units.map(unit => String.fromCharCode(unit)).join('')
const toUnits = (text: string) => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i))
const ownData = (object: any, key: string) => {
  const found = object == null ? undefined : Object.getOwnPropertyDescriptor(object, key)
  return found && 'value' in found && found.writable && found.enumerable && found.configurable ? found : undefined
}
const same = (left: any[], right: any[]) => left.length === right.length && left.every((value, index) => Object.is(value, right[index]))
const results = packet.cases.map((input: any) => {
  const method = fromUnits(input.method)
  const possibleKeys = new Set<string>(input.names.map(fromUnits)), oldSet = new Set(['frame-set'])
  const frameObject = Object.assign(Object.create(null), { marker: 23 }), priorMap = {}, handlerObject = Object.create(null)
  const prior = Array(input.priorCount).fill(priorMap), methods = [...prior], patterns: any[] = []
  const frameArray = ['frame-array'], handlerArray = ['handler-array'], handlerFunction = () => null
  const compiled = makeClass(source, input.order), owner = new compiled.Holder(methods, patterns)
  // An ordinary same-spelling property must not satisfy or redirect private get.
  owner['#methods'] = frameArray
  const handlers: Record<string, unknown> = { object: handlerObject, array: handlerArray, set: possibleKeys,
    function: handlerFunction, undefined, null: null, boolean: false, number: 17, string: 'handler',
    'methods-array': methods, owner }
  const handler = handlers[input.handler]
  const oldObjects = [Object.prototype, frameObject, priorMap, handlerObject, compiled.Holder.prototype, owner]
  const oldArrays = [methods, patterns, frameArray, handlerArray]
  const observe = (outer: any, priorObjects = oldObjects, priorArrays = oldArrays) => {
    const inner = ownData(outer, method)?.value, keys = ownData(inner, 'possibleKeys')?.value
    return { outerOwnCount: outer == null ? 0 : Reflect.ownKeys(outer).length,
      outerHasMethod: !!ownData(outer, method), outerPrototypeStandard: outer != null && Object.getPrototypeOf(outer) === Object.prototype,
      outerExtensible: outer != null && Object.isExtensible(outer), innerOwnCount: inner == null ? 0 : Reflect.ownKeys(inner).length,
      innerPrototypeStandard: inner != null && Object.getPrototypeOf(inner) === Object.prototype,
      innerExtensible: inner != null && Object.isExtensible(inner),
      handlerKept: !!ownData(inner, 'handler') && Object.is(ownData(inner, 'handler')?.value, handler),
      paramsAbsent: inner != null && !Object.hasOwn(inner, 'params'),
      freshObjects: outer != null && inner != null && outer !== inner && !priorObjects.includes(outer) && !priorObjects.includes(inner),
      freshKeys: Array.isArray(keys) && !priorArrays.includes(keys), keys: Array.isArray(keys) ? keys.map(toUnits) : null,
      score: typeof ownData(inner, 'score')?.value === 'number' ? ownData(inner, 'score')?.value : null }
  }
  const setBefore = [...possibleKeys]
  const firstReturn = owner.run(method, handler, possibleKeys), first = methods[input.priorCount]
  const firstObservation = observe(first), firstSetKept = same([...possibleKeys], setBefore)
  for (const name of input.later) possibleKeys.add(fromUnits(name))
  const extendedSet = [...possibleKeys]
  const secondReturn = owner.run(method, handler, possibleKeys), second = methods[input.priorCount + 1]
  const firstInner = ownData(first, method)?.value, firstKeys = ownData(firstInner, 'possibleKeys')?.value
  return { firstReturn, secondReturn, methodCount: methods.length,
    prefixKept: prior.every((value, index) => Object.is(methods[index], value)),
    first: firstObservation, second: observe(second, [...oldObjects, first, firstInner], [...oldArrays, firstKeys]),
    firstUnchanged: JSON.stringify(observe(first)) === JSON.stringify(firstObservation), distinctStoredMaps: first !== second,
    privateSlotsKept: owner.methods() === methods && owner.patterns() === patterns,
    publicShadowKept: owner['#methods'] === frameArray, orderAfter: compiled.order(),
    setKept: firstSetKept && same([...possibleKeys], extendedSet),
    frameKept: frameObject.marker === 23 && Object.keys(priorMap).length === 0 && Object.keys(handlerObject).length === 0 &&
      patterns.length === 0 && same(frameArray, ['frame-array']) && same(handlerArray, ['handler-array']) && same([...oldSet], ['frame-set']) }
})

let scope: unknown = null
if (packet.scopeProbes) {
  const run = (configure: (owner: any, methods: any[], compiled: any) => any) => {
    const compiled = makeClass(original, 0), methods: any[] = [], owner = new compiled.Holder(methods)
    const setup = configure(owner, methods, compiled) ?? {}
    let error = '', returned: unknown
    try { returned = compiled.Holder.prototype.run.call(setup.receiver ?? owner, 'GET', 'handler', setup.iterable ?? new Set(['id'])) }
    catch (failure: any) { error = failure.message === 'lookup' || failure.message === 'push' ? failure.message : failure.name }
    return { error, order: compiled.order(), length: methods.length, returned: returned ?? null,
      ownZero: Object.hasOwn(methods, '0'), privateArrayChanged: owner.methods() !== methods, ...setup.observation?.() }
  }
  const brand = [
    run(() => ({ receiver: { '#methods': [] } })),
    run((_owner, _methods, compiled) => ({ receiver: Object.create(compiled.Holder.prototype) })),
    run(owner => ({ receiver: Object.create(owner) })),
    run(owner => ({ receiver: new Proxy(owner, {}) })),
    run(() => { const foreign = makeClass(original, 0); return { receiver: new foreign.Holder([]) } })
  ]
  const nullSlot = run(owner => { owner.replaceMethods(null) })
  const noncallable = run((_owner, methods) => { Object.defineProperty(methods, 'push', { value: 17 }) })
  const throwingLookup = run((_owner, methods) => { Object.defineProperty(methods, 'push', { get() { throw new Error('lookup') } }) })
  const throwingPush = run((_owner, methods) => { Object.defineProperty(methods, 'push', { value() { throw new Error('push') } }) })
  const frozen = run((_owner, methods) => { Object.freeze(methods) })
  const captureEvents: string[] = []
  const capturedReceiver = run((owner, methods) => {
    Object.defineProperty(methods, 'push', { get() { captureEvents.push('lookup'); owner.replaceMethods([]); return Array.prototype.push } })
    return { iterable: { *[Symbol.iterator]() { captureEvents.push('iterate'); yield 'id' } } }
  })
  const iteratorRebind = run(owner => ({ iterable: { *[Symbol.iterator]() { owner.replaceMethods([]); yield 'id' } } }))
  const argumentMutation = run((_owner, methods) => ({ iterable: { *[Symbol.iterator]() {
    Object.defineProperty(methods, 'push', { value: 17, configurable: true })
    Array.prototype.push.call(methods, 'sentinel')
    yield 'id'
  } }, observation: () => ({ firstIsSentinel: methods[0] === 'sentinel', tailScore: methods[1]?.GET?.score ?? null }) }))
  let inheritedSetterCalls = 0, capturedRecord: any
  const inheritedIndex = run((_owner, methods) => {
    const prototype = Object.create(Array.prototype)
    Object.defineProperty(prototype, '0', { set(value) { inheritedSetterCalls++; capturedRecord = value } })
    Object.setPrototypeOf(methods, prototype)
    return { observation: () => ({ capturedRecordScore: capturedRecord?.GET?.score ?? null }) }
  })
  // Smoke observations through the actual exported Node class; these do not
  // expose its private arrays or replace the conditional expression theorem.
  const { Node } = await import(pathToFileURL(resolve(checkout, 'src/router/trie-router/node.ts')).href)
  const actualNode = new Node()
  const handler = () => null
  actualNode.insert('GET', '/:id', handler)
  const actual = actualNode.search('GET', '/alpha')
  let outOfScopeSyntax = ''
  try { new Function('curNode', 'method', 'handler', 'possibleKeys', `let order = 0; return (${original})`) }
  catch (error: any) { outOfScopeSyntax = error.name }
  scope = { brand, nullSlot, noncallable, throwingLookup, throwingPush, frozen, capturedReceiver, iteratorRebind, argumentMutation,
    captureEvents, inheritedIndex, inheritedSetterCalls,
    outOfScopeSyntax,
    actualNode: { matches: actual[0].length, handlerKept: actual[0][0][0] === handler, id: actual[0][0][1].id } }
}
process.stdout.write(JSON.stringify({ revision: pin, runtime: Bun.version, checkedPinnedBlobs,
  sourceScope: 'exact private push expression; supplied class/entry; constructor and traversal unproved', results, scope }) + '\n')
