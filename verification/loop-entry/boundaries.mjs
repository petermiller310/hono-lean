// Native observations with fixture bodies; no whole-Hono or engine proof.
import assert from 'node:assert/strict'
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const metadata = JSON.parse(readFileSync(new URL('./source.json',import.meta.url),'utf8'))
const headers = {}
for (const name of ['outer','inner']) {
  const text = readFileSync(new URL(`./${name}.ts.txt`,import.meta.url),'utf8')
  assert.equal(createHash('sha256').update(text).digest('hex'),metadata.fragments[name].sha256)
  headers[name] = text
}
const outer = new Function('len',`let i = 'outside'; const seen=[]; ${headers.outer}
  seen.push(i); break; } return {seen,i}`)
assert.deepEqual(outer(0),{seen:[],i:'outside'})
assert.deepEqual(outer(2),{seen:[0],i:'outside'})

let reads = 0
const nodes = {get length() {reads++;return 1}}
const inner = new Function('curNodes',`let j=99,len2=88;const seen=[]; ${headers.inner}
  seen.push([j,len2]); } return {seen,j,len2}`)
assert.deepEqual(inner(nodes),{seen:[[0,1]],j:99,len2:88})
assert.equal(reads,1)

assert.throws(() => new Function(headers.inner.replace('j++','j\n++')+'}'),SyntaxError)
assert.doesNotThrow(() => new Function(headers.inner.replace('j++','j++\n')+'}'))
for (const initializer of ['let j = len2, len2 = 1','let j = 0, len2 = len2']) {
  const run = new Function(`let len2 = 8; for (${initializer};j < len2;j++) {} `)
  assert.throws(run,ReferenceError)
}

let counter = 4294967294
assert.equal(counter++,4294967294)
assert.equal(counter,4294967295)
assert.equal(counter < 4294967295,false)

counter = Number.MAX_SAFE_INTEGER
counter++
assert.equal(Number.isSafeInteger(counter),false)
const unsafe = counter
counter++
assert.equal(counter,unsafe) // Native rounding stalls outside the modeled safe domain.

counter = -0
assert.equal(Object.is(counter++,-0),true)
assert.equal(counter,1)
counter = '0'
assert.equal(counter++,0)
assert.equal(counter,1)
process.stdout.write(JSON.stringify({groups:6,
  runtime:typeof Bun === 'undefined' ? 'node' : 'bun',
  version:typeof Bun === 'undefined' ? process.versions.node : Bun.version,
  facts:['outer false guard','single length read and lexical shadowing','postfix newline and TDZ',
    'UInt32 terminal counter','unsafe Number stalls','signed zero and ToNumeric'],
  boundary:'Fixture bodies/closures/getters and unsafe/coerced numbers do not establish selected-loop/native adequacy'})+'\n')
