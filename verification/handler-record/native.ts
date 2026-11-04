// Exact object argument in supplied caller states; not the private push call.
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
// This expression contains only ordinary JavaScript. No type-erasure pass is
// used; Function/evaluation and the engine remain finite-evidence boundaries.
const factory = new Function('method', 'handler', 'possibleKeys', 'initialOrder',
  `let order = initialOrder; return { build() { return (${source}) }, order() { return order }, bindings() { return [method, handler, possibleKeys] } }`)
const fromUnits = (units: number[]) => units.map(unit => String.fromCharCode(unit)).join('')
const toUnits = (text: string) => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i))
const descriptor = (object: any, key: string) => object == null ? undefined : Object.getOwnPropertyDescriptor(object, key)
const ownData = (object: any, key: string) => {
  const found = descriptor(object, key)
  return found && 'value' in found && found.writable && found.enumerable && found.configurable ? found : undefined
}
const results = packet.cases.map((input: any) => {
  const method = fromUnits(input.method)
  const possibleKeys = new Set<string>(input.names.map(fromUnits))
  const oldSet = new Set(['frame-set'])
  const oldArray = ['frame-array'], handlerArray = ['handler-array']
  const oldObject = Object.assign(Object.create(null), { frame: 23 })
  const handlerObject = Object.create(null), handlerFunction = () => null
  const handlers: Record<string, unknown> = { object: handlerObject, array: handlerArray, set: possibleKeys,
    function: handlerFunction, undefined, null: null, boolean: false, number: 17, string: 'handler' }
  const handler = handlers[input.handler]
  const called = factory(method, handler, possibleKeys, input.order)
  const oldObjects = [Object.prototype, oldObject, handlerObject, handlerArray, possibleKeys, handlerFunction]
  const oldArrays = [oldArray, handlerArray]
  const observe = (outer: any, priorObjects = oldObjects, priorArrays = oldArrays) => {
    const inner = ownData(outer, method)?.value
    const keys = ownData(inner, 'possibleKeys')?.value
    return { outerOwnCount: outer == null ? 0 : Reflect.ownKeys(outer).length,
      outerHasMethod: !!ownData(outer, method), outerPrototypeStandard: outer != null && Object.getPrototypeOf(outer) === Object.prototype,
      outerExtensible: outer != null && Object.isExtensible(outer),
      innerOwnCount: inner == null ? 0 : Reflect.ownKeys(inner).length,
      innerPrototypeStandard: inner != null && Object.getPrototypeOf(inner) === Object.prototype,
      innerExtensible: inner != null && Object.isExtensible(inner),
      handlerKept: !!ownData(inner, 'handler') && Object.is(ownData(inner, 'handler')?.value, handler),
      paramsAbsent: inner != null && !Object.hasOwn(inner, 'params'),
      freshObjects: outer != null && inner != null && outer !== inner && !priorObjects.includes(outer) && !priorObjects.includes(inner),
      freshKeys: Array.isArray(keys) && !priorArrays.includes(keys),
      keys: Array.isArray(keys) ? keys.map(toUnits) : null,
      score: typeof ownData(inner, 'score')?.value === 'number' ? ownData(inner, 'score')?.value : null }
  }
  const setBefore = [...possibleKeys]
  const first = called.build(), firstObservation = observe(first)
  const firstSetKept = JSON.stringify([...possibleKeys]) === JSON.stringify(setBefore)
  for (const name of input.later) possibleKeys.add(fromUnits(name))
  const setExtended = [...possibleKeys]
  const second = called.build()
  const savedInner = ownData(first, method)?.value, savedKeys = ownData(savedInner, 'possibleKeys')?.value
  const currentBindings = called.bindings()
  return { first: firstObservation, second: observe(second, [...oldObjects, first, savedInner], [...oldArrays, savedKeys]),
    firstUnchanged: JSON.stringify(observe(first)) === JSON.stringify(firstObservation),
    orderAfter: called.order(), distinctOuter: first !== second,
    otherBindingsKept: Object.is(currentBindings[0], method) && Object.is(currentBindings[1], handler) && Object.is(currentBindings[2], possibleKeys),
    setKept: firstSetKept && JSON.stringify([...possibleKeys]) === JSON.stringify(setExtended),
    frameKept: oldObject.frame === 23 && oldArray.length === 1 && oldArray[0] === 'frame-array' &&
      handlerArray.length === 1 && handlerArray[0] === 'handler-array' && [...oldSet].join() === 'frame-set' }
})

let scope: unknown
if (packet.scopeProbes) {
  const runScope = new Function('method', 'handler', 'possibleKeys', `let order = 0;
    try { const result = (${original}); return { result, order } } catch (error) { return { order, error: error.message } }`)
  const effects: string[] = []
  const method = { [Symbol.toPrimitive]() { effects.push('key'); return '__proto__' } }
  const iterable = { *[Symbol.iterator]() { effects.push('iterate'); yield 'id' } }
  const observed = runScope(method, 'handler', iterable)
  const throwing = runScope('GET', 'handler', { [Symbol.iterator]() { throw new Error('iterator') } })
  const afterPush = new Function('method', 'handler', 'possibleKeys', `let order = 0;
    const receiver = { get push() { return () => { throw new Error('push') } } };
    try { receiver.push(${original}) } catch (error) { return { order, error: error.message } }`)
    ('GET', 'handler', new Set(['id']))
  const calls: string[] = []
  const inherited = Object.getOwnPropertyDescriptor(Object.prototype, 'possibleKeys')
  let inheritedSetterCalls = 0
  try {
    Object.defineProperty(Object.prototype, 'possibleKeys', { configurable: true, set() { inheritedSetterCalls++ } })
    const built = runScope('GET', 'handler', new Set(['id']))
    assert(Object.hasOwn(built.result.GET, 'possibleKeys'))
  } finally {
    if (inherited) Object.defineProperty(Object.prototype, 'possibleKeys', inherited)
    else delete (Object.prototype as any).possibleKeys
  }
  const callOrder = new Function('method', 'handler', 'possibleKeys', 'events', `let order = 0;
    const receiver = { get push() { events.push('lookup'); return (value) => events.push('push') } };
    receiver.push(${original}); return order`)
    ({ [Symbol.toPrimitive]() { calls.push('key'); return 'GET' } }, 'handler',
      { *[Symbol.iterator]() { calls.push('iterate'); yield 'id' } }, calls)
  const precision = factory('GET', 'handler', new Set(['id']), Number.MAX_SAFE_INTEGER)
  const precisionScores = [precision.build().GET.score, precision.build().GET.score]
  const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
  // Execute the actual earlier checked source block with an explicit polluted
  // root. This is a native precondition witness, not a whole Node execution.
  const loopSource = file.toString('ascii').split('\n').slice(74, 81).join('\n')
  const consume = new Function('handlerSet', 'handlerSets', 'params', 'nodeParams', 'createNullObject', loopSource)
  const inheritedParams = Object.getOwnPropertyDescriptor(Object.prototype, 'params')
  let paramsSetterCalls = 0, consumerError = '', ownParamsAfterReset = false, appendedHandlers = 0
  try {
    Object.defineProperty(Object.prototype, 'params', { configurable: true, set() { paramsSetterCalls++ } })
    const built = runScope('GET', 'handler', new Set(['id']))
    const handlerSet = built.result.GET, handlerSets: unknown[] = []
    try { consume(handlerSet, handlerSets, undefined, { id: 'value' }, createNullObject) }
    catch (error: any) { consumerError = error.name }
    ownParamsAfterReset = Object.hasOwn(handlerSet, 'params')
    appendedHandlers = handlerSets.length
  } finally {
    if (inheritedParams) Object.defineProperty(Object.prototype, 'params', inheritedParams)
    else delete (Object.prototype as any).params
  }
  scope = { computedKeyEffects: effects, computedProtoIsOwnData: !!ownData(observed.result, '__proto__'),
    prototypeUnchanged: Object.getPrototypeOf(observed.result) === Object.prototype,
    iteratorFailureOrder: throwing.order, iteratorFailure: throwing.error,
    pushFailureOrder: afterPush.order, pushFailure: afterPush.error,
    inheritedSetterCalls, fullCallEffects: calls, fullCallOrder: callOrder,
    precisionScores, paramsSetterCalls, consumerError, ownParamsAfterReset, appendedHandlers }
}
process.stdout.write(JSON.stringify({ revision: pin, runtime: Bun.version, checkedPinnedBlobs,
  scope: scope ?? null, sourceScope: 'exact object argument; supplied caller states; private push excluded', results }) + '\n')
