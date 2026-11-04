// Executable native boundary witnesses; none is a language-adequacy proof.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
const source = readFileSync(new URL('./source.ts.txt', import.meta.url), 'utf8')
const run = new Function('curNodesQueue', 'tempNodes', `"use strict"; let curNodes;
${source}
return { shifted, curNodes };`)

// Every Array is truthy, including an empty one: equal contents still get a
// fresh concat identity rather than selecting the reuse branch.
const temp = ['temp'], scheduled = []
const empty = run([scheduled], temp)
assert.equal(empty.shifted, scheduled)
assert.deepEqual(empty.curNodes, temp)
assert.notEqual(empty.curNodes, temp)

// Default concat flattens arrays once; strings/ordinary objects are one value.
for (const scalar of ['xy', 3, true, Object.create(null)]) {
  const result = run([scalar], temp)
  assert.equal(result.curNodes.length, 2)
  assert.equal(result.curNodes[1], scalar)
}

// Source177 can create holes in the outer pending queue. They read as undefined
// but remain distinguishable by own-property observations after native shift.
const sparseQueue = []; sparseQueue[2] = ['later']
const sparse = run(sparseQueue, temp)
assert.equal(sparse.shifted, undefined)
assert.equal(sparse.curNodes, temp)
assert.equal(sparseQueue.length, 2)
assert.equal(Object.hasOwn(sparseQueue, 0), false)
assert.equal(Object.hasOwn(sparseQueue, 1), true)

const sparseTemp = ['first']; sparseTemp.length = 2
const sparseCopy = run([['last']], sparseTemp).curNodes
assert.equal(sparseCopy.length, 3)
assert.equal(Object.hasOwn(sparseCopy, 1), false)

// Symbol.isConcatSpreadable is deliberately outside the dense default model.
const blocked = ['scheduled']; blocked[Symbol.isConcatSpreadable] = false
assert.equal(run([blocked], temp).curNodes[1], blocked)
const spreadable = { 0: 'custom', length: 1, [Symbol.isConcatSpreadable]: true }
assert.deepEqual(run([spreadable], temp).curNodes, ['temp', 'custom'])

const events = []
class CustomArray extends Array {
  static get [Symbol.species]() {
    events.push('species')
    return class Output {
      constructor(length) { events.push(`construct:${length}`); this.length = length }
    }
  }
}
const custom = new CustomArray(); custom.push('temp')
const customCopy = run([['scheduled']], custom).curNodes
assert.deepEqual(events, ['species', 'construct:0'])
assert.equal(Array.isArray(customCopy), false)
assert.equal(customCopy.length, 2)
assert.equal(customCopy[0], 'temp')
assert.equal(customCopy[1], 'scheduled')

// Native shift is effectful and may fail after earlier getter effects. The
// compact Except model does not advertise a matching partial exception trace.
const getterEvents = []
const queue = [['a'], ['b']]
Object.defineProperty(queue, 0, { configurable: true, get() { getterEvents.push('first'); return ['a'] } })
assert.throws(() => run(queue, temp), TypeError)
assert.deepEqual(getterEvents, ['first'])

// Reference resolution precedes RHS, but unresolved/const PutValue failures
// occur afterward. Const/live-cell behavior is outside the new mutable entry.
const assignmentEvents = []
const missing = '__honoLeanQueueMissingBinding__'
assert.equal(Object.hasOwn(globalThis, missing), false)
assert.throws(() => new Function('events', `"use strict"; ${missing} = events.push('missing RHS');`)(assignmentEvents), ReferenceError)
assert.equal(Object.hasOwn(globalThis, missing), false)
assert.throws(() => new Function('events', '"use strict"; const fixed = 0; fixed = events.push("const RHS");')(assignmentEvents), TypeError)
assert.deepEqual(assignmentEvents, ['missing RHS', 'const RHS'])

console.log(JSON.stringify({ emptyArrayFresh: true, scalarAppend: true,
  sparsePendingAndTemp: true, spreadabilityChanges: true,
  speciesEvents: events, shiftFailureEffects: getterEvents, assignmentEvents }))
