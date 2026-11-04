// Native boundary witnesses. These expose limits; they are not adequacy proofs.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
const source = readFileSync(new URL('./source.ts.txt', import.meta.url), 'utf8')
const run = new Function('curNodesQueue', 'componentCount', 'child', `"use strict";
${source}
return targetCurNodes;`)
const node = Object.create(null)

// Real holes differ from own undefined. The selected property becomes own;
// intervening gaps remain absent, and a repeat reuses the retained target.
const pending = []
const fresh = run(pending, 3, node)
assert.equal(pending.length, 4)
assert.deepEqual([0, 1, 2, 3].map(index => Object.hasOwn(pending, index)), [false, false, false, true])
assert.equal(run(pending, 3, node), fresh)
assert.equal(fresh.length, 2)
const ownUndefined = [undefined]
assert.equal(Object.hasOwn(ownUndefined, 0), true)
assert.notEqual(run(ownUndefined, 0, node), fresh)

// One Get and no Put on a truthy slot, even if its setter would throw.
let gets = 0, sets = 0
const retained = [], accessorQueue = []
Object.defineProperty(accessorQueue, 0, { configurable: true,
  get() { gets++; return retained }, set() { sets++; throw new Error('No Put allowed') } })
assert.equal(run(accessorQueue, 0, node), retained)
assert.equal(gets, 1)
assert.equal(sets, 0)

// Falsy accessor: assignment returns the fresh RHS, not another getter result.
let received
const falsy = []
Object.defineProperty(falsy, 2, { configurable: true,
  get() { gets++; return undefined }, set(value) { sets++; received = value } })
const selected = run(falsy, 2, node)
assert.equal(received, selected)
assert.equal(selected[0], node)
assert.equal(gets, 2)
assert.equal(sets, 1)

// Numeric prototype entries can supply a target without creating an own slot.
const inherited = [], prototype = Object.create(Array.prototype), withPrototype = []
Object.defineProperty(prototype, 1, { value: inherited, writable: true, configurable: true })
Object.setPrototypeOf(withPrototype, prototype)
assert.equal(run(withPrototype, 1, node), inherited)
assert.equal(Object.hasOwn(withPrototype, 1), false)
assert.equal(withPrototype.length, 0)

// The highest array index changes length; 2^32-1 is an ordinary named key.
// These probes inspect a few own keys, never iterate billions of holes.
const highest = [], named = []
run(highest, 4294967294, node)
run(named, 4294967295, node)
assert.equal(highest.length, 4294967295)
assert.equal(named.length, 0)
assert.equal(Object.hasOwn(named, '4294967295'), true)

// Base/index expressions run once. An OBJECT key can be coerced separately
// by GetValue and PutValue; the formal entry only admits primitive indices.
const events = [], keyQueue = []
const base = () => { events.push('base'); return keyQueue }
const key = { toString() { events.push('key'); return '2' } }
const index = () => { events.push('index'); return key }
const rhs = () => { events.push('RHS'); return [] }
const target = (base()[index()] ||= rhs())
assert.equal(target, keyQueue[2])
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
// Preserve the observed engine difference outside our numeric-key domain.
assert.deepEqual(events, runtime === 'bun'
  ? ['base', 'index', 'key', 'RHS'] : ['base', 'index', 'key', 'RHS', 'key'])
const pinnedEvents = [], pinnedQueue = []
Object.defineProperty(pinnedQueue, 2, { configurable: true,
  get() { pinnedEvents.push('Get'); return undefined },
  set() { pinnedEvents.push('Put') } })
const pinnedKey = { toString() { pinnedEvents.push('key'); return '2' } }
run(pinnedQueue, pinnedKey, node)
assert.deepEqual(pinnedEvents, runtime === 'bun'
  ? ['key', 'Get', 'Put'] : ['key', 'Get', 'key', 'Put'])
const redirectEvents = [], redirectQueue = []
let redirectCalls = 0, setterTarget
Object.defineProperty(redirectQueue, 2, { configurable: true,
  get() { redirectEvents.push('Get2'); return 0 },
  set(value) { redirectEvents.push('Put2'); setterTarget = value } })
const redirectKey = { toString() {
  redirectEvents.push('key'); return String(++redirectCalls === 1 ? 2 : 3)
} }
const redirected = run(redirectQueue, redirectKey, node)
const redirect = { events: redirectEvents, coercions: redirectCalls,
  queueLength: redirectQueue.length, own3: Object.hasOwn(redirectQueue, 3),
  targetIsSetterValue: redirected === setterTarget }
assert.deepEqual(redirect, runtime === 'bun'
  ? { events: ['key', 'Get2', 'Put2'], coercions: 1, queueLength: 3, own3: false, targetIsSetterValue: true }
  : { events: ['key', 'Get2', 'key'], coercions: 2, queueLength: 4, own3: true, targetIsSetterValue: false })

// A custom push getter/call changes the observable behavior outside frozen
// standard method interpretation. No global Array prototype is modified.
const customEvents = [], custom = []
Object.defineProperty(custom, 'push', { configurable: true,
  get() { customEvents.push('get push'); return function (value) {
    assert.equal(this, custom); customEvents.push(value); return 123
  } } })
assert.equal(run([custom], 0, node), custom)
assert.deepEqual(customEvents, ['get push', node])

console.log(JSON.stringify({ runtime, version, holesAndOwnUndefined: true, retainedReuse: true,
  getOnceAndPutShortCircuit: true, inheritedNumericTarget: true,
  arrayIndexBoundary: true, coercionEvents: events, pinnedCoercionEvents: pinnedEvents,
  redirectedKey: redirect, customPush: true }))
