// Native-only interpretation controls. These successes do not widen the
// ordinary-data theorem, its O0 projection, or the existing baseline D1.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { createRequire } from 'node:module'
import { resolve } from 'node:path'

const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
const checkout = resolve(process.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs, 315)
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const fragment = (folder, name, file) => {
  const metadata = JSON.parse(readFileSync(new URL(`../${folder}/source.json`, import.meta.url)))
  const span = metadata.fragments[name]
  const bytes = readFileSync(resolve(checkout, metadata.sourcePath))
  const text = readFileSync(new URL(`../${folder}/${file}`, import.meta.url), 'utf8')
  assert.equal(metadata.revision, revision)
  assert.equal(sha(bytes), metadata.sourceSha256)
  assert.equal(sha(text), span.sha256)
  assert.equal(bytes.subarray(span.startByte, span.endByteExclusive).toString(), text)
  return text
}
const source = fragment('capture-collect', 'full', 'full.ts.txt')
const method = fragment('private-call', 'method', 'method.ts.txt')
const ts = createRequire(import.meta.url)(process.env.HONO_TYPESCRIPT ?? 'typescript')
assert.equal(ts.version, '6.0.3')
const wrapper = `function build(createNullObject, METHOD_NAME_ALL) {
  return class Holder {
    #params; #methods;
    constructor(params, rows=[]) { this.#params=params; this.#methods=rows }
${method}
    run(node, child, handlerSets, method, params, name, m) {
${source}
      return params
    }
    withoutMatch(node, child, handlerSets, method, params, name) {
${source}
      return params
    }
  }
}`
const emitted = ts.transpileModule(wrapper, { compilerOptions: {
  target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.None
} }).outputText
const build = new Function(emitted + '\nreturn build')()
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype)
assert.equal(Object.hasOwn(globalThis, 'm'), false)
let allocations = 0
const Holder = build(() => { allocations++; return Object.create(null) }, 'ALL')
const run = (parent, params, keys, name, matches, missing = false) => {
  const record = { handler: 'handler', possibleKeys: keys, score: 1 }
  const child = new Holder(undefined, [{ GET: record }])
  const node = new Holder(parent), receiver = new Holder(undefined), collector = []
  const countBefore = allocations
  const result = missing ? receiver.withoutMatch(node, child, collector, 'GET', params, name) :
    receiver.run(node, child, collector, 'GET', params, name, matches)
  assert.equal(result, params)
  assert.deepEqual(collector, [record])
  assert.equal(Object.getPrototypeOf(record.params), null)
  assert.equal(allocations, countBefore + 1)
  return record.params
}

// O0 formally projects constructor and __proto__, not these other native
// intrinsics. Each is an ordinary inherited DATA function in the native realm.
const inheritedNames = ['toString', 'valueOf', 'hasOwnProperty', 'isPrototypeOf', 'propertyIsEnumerable', 'toLocaleString']
const inheritedMethods = []
for (const name of inheritedNames) {
  const parent = { id: 'alpha' }, params = { ...parent }
  const output = run(parent, params, ['id', name], name, ['12'])
  assert.equal(params[name], '12')
  assert.equal(Object.hasOwn(params, name), true)
  assert.equal(output[name], Object.prototype[name])
  assert.equal(typeof output[name], 'function')
  assert.equal(Object.hasOwn(output, name), true)
  assert.equal(JSON.stringify(output), '{"id":"alpha"}')
  const nullParent = Object.assign(Object.create(null), { id: 'alpha' })
  const ordinary = run(nullParent, { ...nullParent }, ['id', name], name, ['12'])
  assert.equal(ordinary[name], '12')
  inheritedMethods.push({ name, captured: { intrinsic: 'Object.prototype.' + name }, json: JSON.stringify(output), nullPrototypeParentCapture: ordinary[name] })
}

// Own-presence suppression does not require evaluating m, even for undefined
// or falsy values. This also separates JSON omission of undefined from function.
const ownSkips = []
for (const value of [undefined, false, 0, '']) {
  const parent = { id: 'alpha', tail: value }, params = { ...parent }
  const output = run(parent, params, ['id', 'tail'], 'tail', undefined, true)
  assert.equal(Object.hasOwn(output, 'tail'), true)
  assert.equal(output.tail, value)
  ownSkips.push({ value: value === undefined ? { kind: 'undefined' } : value, noMatchBinding: true, json: JSON.stringify(output) })
}

// Native getter effects are deliberately outside the pure-DATA read domain.
// The exact helper reads truthy index0 optional input twice; later keys consult
// parent first after their optional truthiness probe.
const events = []
let idReads = 0
const params = Object.defineProperties({}, {
  id: { get() { events.push('q:id'); return ++idReads === 1 ? 'first' : 'second' } },
  tail: { get() { events.push('q:tail'); return 'local' } }
})
const parent = Object.defineProperty({}, 'tail', { get() { events.push('parent:tail'); return 'parent' } })
const getterOutput = run(parent, params, ['id', 'tail'], 'tail', undefined, true)
assert.deepEqual(events, ['q:id', 'q:id', 'q:tail', 'parent:tail'])
assert.equal(getterOutput.id, 'second')
assert.equal(getterOutput.tail, 'parent')
const fallbackEvents = []
let tailReads = 0
const fallbackQ = Object.defineProperties({}, {
  id: { value: 'alpha' }, tail: { get() { fallbackEvents.push('q:tail'); return ++tailReads === 1 ? 'before' : 'after' } }
})
const fallbackParent = Object.defineProperty({}, 'tail', { get() { fallbackEvents.push('parent:tail'); return undefined } })
const fallbackOutput = run(fallbackParent, fallbackQ, ['id', 'tail'], 'tail', undefined, true)
assert.deepEqual(fallbackEvents, ['q:tail', 'parent:tail', 'q:tail'])
assert.equal(fallbackOutput.tail, 'after')

// General native call-order control, not an extra modeled callback facility.
const callEvents = []
const receiver = { get collect() {
  callEvents.push('method')
  return function (...args) { callEvents.push('call'); assert.equal(this, receiver); assert.deepEqual(args, ['left', 'right']) }
} }
const base = () => { callEvents.push('base'); return receiver }
base().collect((callEvents.push('left'), 'left'), (callEvents.push('right'), 'right'))
assert.deepEqual(callEvents, ['base', 'method', 'left', 'right', 'call'])
const noncallableEvents = []
assert.throws(() => ({ get method() { noncallableEvents.push('method'); return 0 } }).method(
  (noncallableEvents.push('argument'), 1)), TypeError)
assert.deepEqual(noncallableEvents, ['method', 'argument'])
assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype), rootBefore)
console.log(JSON.stringify({
  revision, runtime, version, checkedPinnedBlobs, verified: false,
  sourceBytes: Buffer.byteLength(source), methodBytes: Buffer.byteLength(method),
  transpilation: { verified: false, compiler: ts.version, inputSha256: sha(wrapper), emittedSha256: sha(emitted) },
  outsideDomain: { inheritedMethods, getterEvents: events, nullishFallbackGetterEvents: fallbackEvents,
    getterResults: { id: getterOutput.id, tail: getterOutput.tail, fallbackTail: fallbackOutput.tail },
    methodReceiverAndArgumentOrder: callEvents, noncallableStillEvaluatesArgument: noncallableEvents },
  ownSkips, source161KeepsParentFourthAndLocalFifth: true, rootDescriptorsUnchanged: true,
  allocationCount: allocations,
  scope: 'Native-only controls; unsupported O0 methods/accessors and general calls do not enlarge the formal domain or baseline D1.'
}))
