// Finite native probes of the declared boundary; no native adequacy theorem.
import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'

const source = readFileSync(new URL('./count.ts.txt', import.meta.url), 'utf8')
assert.equal(createHash('sha256').update(source).digest('hex'),
  '8f93b148e6dc2f2cf67003adc4e5791a8c5c7132dcab0fd7c566599201ed9c54')
const count = new Function('m', `"use strict"; ${source}\nreturn componentCount;`)
const regexp = /\//g
regexp.lastIndex = 999
assert.deepEqual('a/b//'.match(regexp), ['/', '/', '/'])
assert.equal(regexp.lastIndex, 0)
regexp.lastIndex = 999
assert.equal('abc'.match(regexp), null)
assert.equal(regexp.lastIndex, 0)
assert.equal(count(['\uD800/\uDC00/']), 2)
assert.equal(count(['']), 0)

// These are counterexamples to removing the primitive/frozen-method premises.
assert.equal(count([{ match: () => ({ length: 77 }) }]), 77)
const original = String.prototype.match
let customExecCount
try {
  String.prototype.match = function (rx) {
    rx.exec = () => null
    return Reflect.apply(original, this, [rx])
  }
  customExecCount = count(['a/b'])
} finally {
  String.prototype.match = original
}
assert.equal(customExecCount, 0)
console.log(JSON.stringify({ runtime: typeof Bun === 'undefined' ? 'node' : 'bun',
  version: typeof Bun === 'undefined' ? process.versions.node : Bun.version,
  standard: { incomingLastIndex: 999, slashMatchLength: 3, noHit: null, finalLastIndex: 0, rawUTF16Count: 2, emptyCount: 0 },
  outsideDomain: { objectReceiverCustomMatchCount: 77, replacedExecCount: customExecCount },
  unreachableAccumulatorObserved: false, verified: false }))
