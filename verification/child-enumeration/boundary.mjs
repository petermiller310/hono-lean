// Finite native observations outside and inside the selected normal domain.
// The class wrapper and match-call instrumentation are unverified scaffolding.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'

const source = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(createHash('sha256').update(source).digest('hex'),
  'fce614b83a4e70c4b00d6f4e8e609d20109770daf866b281b2677862be5168c2')
const original = String.prototype.match
function probe(children, readonly = false) {
  const factory = new Function('children', 'm', 'curNodesQueue', 'params', `"use strict";
    return new class {
      #children=children; ${readonly ? '#params() {}' : '#params=17;'}
      run() { const child=this; const _=99, componentCount=98, targetCurNodes=97;
${source}
        return [_===99,componentCount===98,targetCurNodes===97]; }
      read() { return this.#params; }
    }`)
  const queue = [], params = Object.create(null)
  const holder = factory(children, ['a/b'], queue, params)
  let calls = 0, error = null, scope
  try {
    String.prototype.match = function (pattern) {
      calls++
      assert.equal(holder.read(), params, 'Params write must precede match')
      return Reflect.apply(original, this, [pattern])
    }
    try { scope = holder.run() } catch (caught) { error = caught.name }
  } finally { String.prototype.match = original }
  return { calls, error, scope: scope ?? null, changed: holder.read() === params,
    queued: queue[1]?.length ?? 0 }
}
const own = (key, enumerable = true) => Object.defineProperty(Object.create(null), key,
  { value: false, enumerable, writable: true, configurable: true })
let getterReads = 0
const getter = Object.defineProperty(Object.create(null), 'x', { enumerable: true,
  get() { getterReads++; throw new Error('Must not read value') } })
const inherited = Object.create(own('x'))
const shadowed = Object.defineProperty(Object.create(own('x')), 'x', { value: 0, enumerable: false })
const symbolOnly = own(Symbol('x'))
const cases = [
  ['empty', Object.create(null), false, 0], ['nonEnumerable', own('x', false), false, 0],
  ['emptyStringKey', own(''), false, 1], ['getter', getter, false, 1],
  ['multipleKeys', Object.assign(Object.create(null), { x: false, y: 0, z: undefined }), false, 1],
  ['inheritedOutsideDomain', inherited, false, 1], ['shadowedOutsideDomain', shadowed, false, 0],
  ['symbolOnlyOutsideDomain', symbolOnly, false, 0], ['nullOutsideDomain', null, false, 0],
  ['undefinedOutsideDomain', undefined, false, 0], ['readonlyEmpty', Object.create(null), true, 0],
  ['readonlyEntered', own('x'), true, 0]
]
const observations = cases.map(([name, children, readonly, calls]) => {
  const value = probe(children, readonly)
  assert.equal(value.calls, calls, name)
  assert.equal(value.error, name === 'readonlyEntered' ? 'TypeError' : null, name)
  if (value.error === null) assert.deepEqual(value.scope, [true, true, true], name)
  assert.equal(value.queued, calls, name)
  assert.equal(value.changed, calls === 1, name)
  return { name, ...value }
})
assert.equal(getterReads, 0)
console.log(JSON.stringify({ runtime: typeof Bun === 'undefined' ? 'node' : 'bun',
  version: typeof Bun === 'undefined' ? process.versions.node : Bun.version,
  verified: false, getterReads, observations }))
