// Planned next frontier: native-only actual138 iterator/destructuring probes.
// No completed model/source proof is registered by this file.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
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
const raw=readFileSync(resolve(checkout,'src/router/trie-router/node.ts'))
const source=raw.subarray(4205,4249).toString()
const sourceSha256=createHash('sha256').update(source).digest('hex')
assert.equal(Buffer.byteLength(source),44)
assert.equal(sourceSha256,'4bd90c878a3496b7a05edc1a3a90ba0e83afc24484b15acd1e600d5aff95a2a1')
// ENGINE-ELISION-1: the SAME source/callbacks run on each engine. Expected
// records below preserve the discovered difference; no conformance allowlist
// or Hono baseline is changed. This remains native-only frontier evidence.
const bind=new Function('pattern',source+'\nreturn {name,matcher}')
function run(throwOnZero){
  const events=[];let cursor=0
  const pattern={ [Symbol.iterator](){events.push('iterator');return {
    next(){const index=cursor++;events.push('next'+index);return {done:false,get value(){
      events.push('value'+index)
      if(throwOnZero&&index===0)throw new Error('elided-value')
      return index
    }}},
    return(){events.push('return');return {}}
  }}}
  try{return {ok:true,result:bind(pattern),events}}
  catch(error){return {ok:false,message:error.message,events}}
}
const normal=run(false),throwing=run(true)
const nodeTrace=['iterator','next0','next1','value1','next2','value2','return']
const bunTrace=['iterator','next0','value0','next1','value1','next2','value2','return']
assert.deepEqual(normal,{ok:true,result:{name:1,matcher:2},events:runtime==='bun'?bunTrace:nodeTrace})
assert.deepEqual(throwing,runtime==='bun'?{ok:false,message:'elided-value',events:['iterator','next0','value0']}:
  {ok:true,result:{name:1,matcher:2},events:nodeTrace})
console.log(JSON.stringify({id:'ENGINE-ELISION-1',revision,runtime,version,checkedPinnedBlobs,sourceBytes:44,sourceSha256,
  verified:false,nativeOnly:true,plannedFrontier:true,formalBindingTheorem:null,plainJavaScript:true,typescriptErasure:false,
  normal,throwing,
  referenceEdition:'ECMA-262 2025 Elision uses IteratorStep without IteratorValue',
  referenceUrl:'https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-iterator-destructuring-assignment-evaluation',
  interpretation:runtime==='node'?'Observed skip agrees with selected edition':'Observed extra value0 Get is an outside-domain native discrepancy',
  baselineAllowlistChanged:false,
  scope:'Exact actual138 statement with custom iterator/result accessors; no general engine adequacy or default-DATA tuple counterexample. Preserve both native outcomes.'}))
