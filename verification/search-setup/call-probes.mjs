// Native boundary observations, not Lean proofs or a general engine audit.
import assert from 'node:assert/strict'

const trace = []
const old = (first) => { trace.push('old-body'); return first }
const newer = () => { trace.push('new-body'); return 'wrong' }
let current = old
const choose = () => { trace.push('callee'); return current }
const first = () => { trace.push('first'); current = newer; return 'kept' }
const extra = () => { trace.push('extra'); return 'ignored' }
assert.equal(choose()(first(), extra()), 'kept')
assert.deepEqual(trace, ['callee', 'first', 'extra', 'old-body'])

trace.length = 0
const nonCallable = 42
assert.throws(() => nonCallable((trace.push('first'), 1), (trace.push('extra'), 2)), TypeError)
assert.deepEqual(trace, ['first', 'extra'])

const one = (value) => value
assert.equal(one(), undefined)
assert.equal(one('first', 'extra'), 'first')
const lexicalThis = () => this
assert.equal(lexicalThis.call({wrong: true}), this)
const moduleThis = this === undefined ? 'undefined' : this === null ? 'null' : typeof this

let cell = 0
const liveCapture = () => ++cell
assert.equal(liveCapture(), 1)
assert.equal(liveCapture(), 2)
assert.equal(cell, 2)

trace.length = 0
const receiver = {get fn() { trace.push('get'); return function () { return this } }}
assert.equal(receiver.fn((trace.push('arg'), 0)), receiver)
assert.deepEqual(trace, ['get', 'arg'])
process.stdout.write(JSON.stringify({groups: 6, result: 'passed', moduleThis,
  scope: 'saved callee, extra argument effects, callability order, omitted formal, module arrow this, live cells and receiver references',
  limits: 'live cells and receiver-reference dispatch are outside the selected call extension; errors expose no model partial state'}) + '\n')
