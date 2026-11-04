// Complete pinned post-wildcard body; explicit caller-owned persistent cache fixture.
// Hidden regex literals and capture arrays are not native observations.
import assert from 'node:assert/strict'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime=typeof Bun==='undefined'?'node':'bun',version=runtime==='bun'?Bun.version:process.versions.node
assert.equal(version,runtime==='bun'?'1.4.0':'22.22.2')
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision);assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)){
 const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
 assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs,315)
const sha=bytes=>createHash('sha256').update(bytes).digest('hex')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url))),raw=readFileSync(resolve(checkout,metadata.sourcePath)),sources={}
assert.equal(sha(raw),metadata.sourceSha256);assert.equal(metadata.revision,revision)
for(const[name,span]of Object.entries(metadata.fragments)){
 const text=readFileSync(new URL('./'+name+'.ts.txt',import.meta.url),'utf8');assert.equal(sha(text),span.sha256)
 assert.equal(raw.subarray(span.startByte,span.endByteExclusive).toString(),text);sources[name]=text
}
assert.equal(sha(sources.full),'0ce62880eb018a718c7d3f32bb413e31bf5b8c42e31bba1e289d280529a47cf5')

const make=(cache,constructor=RegExp)=>new Function('patternCache','RegExp',`return function(label,next){"use strict";\n${sources.full}\n}`)(cache,constructor)
const results=[]
{
 const trace=[],cache={},key=':id{(}#undefined'
 Object.defineProperty(cache,key,{get(){trace.push('get');return trace.length===1?'guard':'return'},configurable:true})
 const result=make(cache,0)(':id{(}')
 assert.equal(result,'return');assert.deepEqual(trace,['get','get'])
 results.push({id:'current-second-get',result,trace})
}
{
 const trace=[],key=':id#undefined';let retained
 const parent={};Object.defineProperty(parent,key,{get(){trace.push('get');return retained},set(value){trace.push('set');retained=value}})
 const cache=Object.create(parent),result=make(cache,0)(':id')
 assert.deepEqual(result,[':id','id',true]);assert.equal(result,retained);assert.equal(Object.hasOwn(cache,key),false)
 assert.deepEqual(trace,['get','set','get'])
 results.push({id:'inherited-custom-setter',result,trace,returnedSameAsStored:true,ownCacheKey:false})
}
{
 const trace=[],key=':id#undefined';let retained,outcome
 const parent={};Object.defineProperty(parent,key,{get(){trace.push('get');return undefined},set(value){trace.push('set');retained=value;throw Error('setter-threw')}})
 const cache=Object.create(parent)
 try{make(cache,0)(':id');outcome={ok:true}}catch(error){outcome={ok:false,message:error.message}}
 assert.deepEqual(outcome,{ok:false,message:'setter-threw'});assert.deepEqual(retained,[':id','id',true]);assert.deepEqual(trace,['get','set'])
 results.push({id:'setter-escapes-RHS-then-throws',outcome,retained,trace,rollbackClaim:false})
}
{
 const trace=[],cache={},key=':id{(}#X';let current='before'
 Object.defineProperty(cache,key,{get(){trace.push('get');return current}})
 const next={[Symbol.toPrimitive](hint){trace.push('coerce:'+hint);current='from-coercion';return'X'}}
 const result=make(cache,0)(':id{(}',next)
 assert.equal(result,'from-coercion');assert.deepEqual(trace,['coerce:string','get','get'])
 results.push({id:'effectful-next-coercion-before-cache',result,trace})
}
{
 const cache=[],result=make(cache,0)(':id')
 assert.deepEqual(result,[':id','id',true]);assert.equal(cache[':id#undefined'],result);assert.equal(cache.length,0)
 results.push({id:'array-as-cache-native-success',result,length:cache.length,ownCacheKey:Object.hasOwn(cache,':id#undefined')})
}
{
 const cache={},key=':id#undefined';Object.setPrototypeOf(cache,{})
 Object.defineProperty(Object.getPrototypeOf(cache),key,{set:Object.getOwnPropertyDescriptor(Object.prototype,'__proto__').set})
 const result=make(cache,0)(':id'),prototype=Object.getPrototypeOf(cache)
 assert.equal(result,undefined);assert.deepEqual(prototype,[':id','id',true]);assert.equal(Object.hasOwn(cache,key),false)
 results.push({id:'legacy-prototype-setter-array-RHS',resultUndefined:true,prototype,ownCacheKey:false})
}
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,sourceBytes:533,sourceSha256:sha(sources.full),
 verified:false,nativeOnly:true,observerVerified:false,closureBootstrapVerified:false,typescriptInitializationObserved:false,
 baselineAllowlistChanged:false,results,
 scope:'Exact full533B body with explicit nonstandard fixture caches/coercion callbacks. Separate native-only controls, not admitted DATA-profile/native trace/error-state/rollback theorems. Setter effects and array caches are actual native successes, not model TypeErrors.'}))
