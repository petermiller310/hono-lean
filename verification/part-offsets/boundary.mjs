// Native-only finite boundary observations; no engine adequacy theorem.
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'

const source = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(createHash('sha256').update(source).digest('hex'),
  '25d15d9b81bc22ba038dea387a703528896940949ae50f9f2f1163c0be9a65c9')
// parts and len are genuinely absent, not undefined formal parameters.
const cached = new Function('path', 'partOffsets', 'i', `"use strict";
${source}
return {cache:partOffsets,rest:restPathString};`)
const empty = [], wrong = [2], hole = new Array(1)
assert.equal(cached('abc/def', empty, 0).rest, 'abc/def')
assert.equal(cached('abc/def', empty, 0).cache, empty)
assert.equal(cached('abc/def', wrong, 0).rest, 'c/def')
assert.equal(cached('abc/def', hole, 0).rest, 'abc/def')
assert.equal(Object.hasOwn(hole, 0), false)
assert.equal(cached('abc/def', [-3], 0).rest, 'def')
assert.equal(cached('abc/def', [999], 0).rest, '')
assert.equal(cached('abc/def', [undefined], 0).rest, 'abc/def')
let offset = 1
offset += (offset = 100, 2)
assert.equal(offset, 3)
let rounded = 2 ** 53
rounded += 1
assert.equal(rounded, 2 ** 53)
let concatenated = '1'
concatenated += 2
assert.equal(concatenated, '12')
console.log(JSON.stringify({runtime: typeof Bun === 'undefined' ? 'node' : 'bun',
  version: typeof Bun === 'undefined' ? process.versions.node : Bun.version, verified:false,
  cached:{emptyReused:true,emptyRest:'abc/def',wrongRest:'c/def',holeReadUndefined:true,holeOwn0:false,
    negativeRest:'def',largeRest:'',ownUndefinedRest:'abc/def'},
  outsideNumericDomain:{capturedBeforeRHS:offset,roundedBeyondSafe:rounded,stringConcatenation:concatenated}}))
