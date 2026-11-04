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
const bind=new Function('pattern','"use strict";\n'+source+'\nreturn {name,matcher}')
const regex=/^[0-9]+$/
const basic=bind(['label','named',regex]);assert.equal(basic.name,'named');assert.equal(basic.matcher,regex)
const events=[],iterator={},values=['elided','named',regex];let cursor=0
Object.defineProperty(iterator,'next',{configurable:true,get(){
  events.push('getNext')
  return function(){
    assert.equal(this,iterator)
    const index=cursor++;events.push('next'+index)
    if(index===0)Object.defineProperty(iterator,'next',{value(){throw new Error('next method was not saved')},configurable:true})
    if(index===2)Object.defineProperty(iterator,'return',{configurable:true,get(){
      events.push('getReturn');return function(){assert.equal(this,iterator);events.push('return');return {}}
    }})
    return {get done(){events.push('done'+index);return false},get value(){
      events.push('value'+index)
      return values[index]
    }}
  }
}})
const custom=Object.create(null)
Object.defineProperty(custom,Symbol.iterator,{get(){events.push('getIterator');return function(){assert.equal(this,custom);events.push('iterator');return iterator}}})
const actual=bind(custom)
assert.equal(actual.name,'named');assert.equal(actual.matcher,regex)
const expectedEvents=['getIterator','iterator','getNext','next0','done0',...(runtime==='bun'?['value0']:[]),'next1','done1','value1','next2','done2','value2','getReturn','return']
assert.deepEqual(events,expectedEvents)
assert.equal(cursor,3)
const arrayEvents=[],data=['label','named',regex]
Object.defineProperty(data,'0',{configurable:true,enumerable:true,get(){arrayEvents.push('array0');return 'label'}})
const actualArray=bind(data);assert.equal(actualArray.matcher,regex);assert.deepEqual(arrayEvents,['array0'])
const prototype=Object.getPrototypeOf([][Symbol.iterator]())
const before=Object.getOwnPropertyDescriptors(prototype),oldNext=before.next,oldReturn=before.return
assert.equal(oldReturn,undefined)
assert.equal(Reflect.get(prototype,'return'),undefined)
const closeEvents=[];let active=false
try{
  Object.defineProperty(prototype,'next',{...oldNext,value:function(){if(active)closeEvents.push('next');return oldNext.value.call(this)}})
  Object.defineProperty(prototype,'return',{configurable:true,get(){
    if(active)closeEvents.push('getReturn')
    return function(){if(active)closeEvents.push('return');return {}}
  }})
  active=true
  const result=bind(['label','named',regex])
  active=false
  assert.equal(result.matcher,regex)
}finally{
  active=false;Object.defineProperty(prototype,'next',oldNext)
  if(oldReturn)Object.defineProperty(prototype,'return',oldReturn);else delete prototype.return
}
assert.deepEqual(Object.getOwnPropertyDescriptors(prototype),before)
assert.deepEqual(closeEvents,['next','next','next','getReturn','return'])
const missing=bind(['only-one'])
assert.equal(missing.name,undefined);assert.equal(missing.matcher,undefined)
const shortEvents=[]
const short={ [Symbol.iterator](){let n=0;return {next(){shortEvents.push('next'+n);return n++===0?{done:false,value:'ignored'}:{done:true}},return(){shortEvents.push('return');return {}}}}}
bind(short);assert.deepEqual(shortEvents,['next0','next1'])
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,sourceBytes:44,sourceSha256,
  verified:false,nativeOnly:true,plannedFrontier:true,formalBindingTheorem:null,plainJavaScript:true,typescriptErasure:false,
  observations:{customEvents:events,customNextCalls:cursor,elidedIteratorResultValueWasNotRead:!events.includes('value0'),engineDifference:'ENGINE-ELISION-1',
    standardArrayIndexZeroGet:arrayEvents,defaultReturnMissing:true,prototypeChangedClose:closeEvents,
    prototypeRestored:true,shortExhaustion:shortEvents,shortMissingBindingsUndefined:true},
  elisionDifferenceReproducer:'verification/pattern-binding/elision-difference.mjs',
  scope:'Planned actual138 frontier only. Pinned Bun additional value0 Get retained as ENGINE-ELISION-1; no baseline allowlist change. Custom iterator/prototype changes and native allocation/lexical/effect semantics are not formal source adequacy. Default standard-array protocol is the next implementation, not three index reads.'}))
