// Unwrapped actual Hono label.match declaration. Temporary literal state is not observed.
import assert from 'node:assert/strict'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'

const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime=typeof Bun==='undefined'?'node':'bun',version=runtime==='bun'?Bun.version:process.versions.node
assert.equal(version,runtime==='bun'?'1.4.0':'22.22.2')
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)){
 const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
 assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs,315)
const sha=bytes=>createHash('sha256').update(bytes).digest('hex')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const raw=readFileSync(resolve(checkout,metadata.sourcePath)),sources={}
assert.equal(sha(raw),metadata.sourceSha256);assert.equal(metadata.revision,revision)
for(const [name,span]of Object.entries(metadata.fragments)){
 const text=readFileSync(new URL('./'+name+'.ts.txt',import.meta.url),'utf8')
 assert.equal(sha(text),span.sha256)
 assert.equal(raw.subarray(span.startByte,span.endByteExclusive).toString(),text);sources[name]=text
}
assert.equal(Buffer.byteLength(sources.full),59)
assert.equal(sha(sources.full),'e1a741ae801aec83c5926a9d2b71e0b2a6dce9ee29406ef602a8d54a862d0207')
const packet=JSON.parse(readFileSync(0,'utf8')),source=packet.source??sources.full,pipeline=packet.mode==='pipeline'
const selected=(file,path,start,end,digest)=>{
 const text=readFileSync(new URL(file,import.meta.url),'utf8')
 assert.equal(sha(text),digest);assert.equal(readFileSync(resolve(checkout,path)).subarray(start,end).toString(),text)
 return text
}
const constructor=selected('../pattern-construct/full.ts.txt','src/utils/url.ts',1733,1779,'b70aef226ab3fc4a7ec886b9d64dbace87107beb4989920d05b48f6bd6b86560')
const binding=selected('../pattern-binding/full.ts.txt','src/router/trie-router/node.ts',4205,4249,'4bd90c878a3496b7a05edc1a3a90ba0e83afc24484b15acd1e600d5aff95a2a1')
const execution=selected('../builtin-exec/full.ts.txt','src/router/trie-router/node.ts',4766,4817,'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
const wrapper=pipeline?
 `"use strict";const match=prior,name='outer-name',matcher=oldRegex,m=caller;let observed,produced;{\n${source}\nproduced=(${constructor});const pattern=produced;\n${binding}\n${execution}\nobserved={match,name,matcher,m};\n}return {observed,produced,outerPreserved:match===prior&&name==='outer-name'&&matcher===oldRegex&&m===caller,thisPreserved:this===caller};`:
 `"use strict";const match=prior;let observed;{\n${source}\nobserved=match;\n}return {observed,outerPreserved:match===prior,thisPreserved:this===caller};`
// RegExp is deliberately shadowed: literal creation must not read this lexical binding.
const lexicalShadow=function(){throw new Error('Regex literal read lexical RegExp')}
const invoke=new Function('label','prior','caller','RegExp','restPathString','oldRegex',wrapper)
const OriginalRegExp=RegExp
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i))
const fromUnits=u=>u.map(n=>String.fromCharCode(n)).join('')
const encode=value=>value===undefined?{kind:'undefined'}:value===null?{kind:'null'}:
 typeof value==='string'?{kind:'string',units:units(value)}:typeof value==='number'?{kind:'number',value}:
 (()=>{throw new Error('Outside label result observation domain')})()
const descriptor=d=>d?{kind:'data',value:encode(d.value),writable:d.writable,enumerable:d.enumerable,configurable:d.configurable}:null
const view=result=>Object.fromEntries([['zero','0'],['one','1'],['two','2'],['length','length'],['index','index'],['input','input'],['groups','groups']]
 .map(([label,key])=>[label,descriptor(Object.getOwnPropertyDescriptor(result,key))]))
const arrayIteratorPrototype=Object.getPrototypeOf([][Symbol.iterator]())
assert.equal(Reflect.get(arrayIteratorPrototype,'return'),undefined)
const intrinsics=[Object.prototype,String.prototype,RegExp.prototype,Array.prototype,arrayIteratorPrototype,Object.getPrototypeOf(arrayIteratorPrototype)]
const intrinsicDescriptors=intrinsics.map(Object.getOwnPropertyDescriptors)
const intrinsicPrototypes=intrinsics.map(Object.getPrototypeOf)
const results=packet.cases.map(test=>{
 const label=fromUnits(test.label),prior=/^prior$/.exec('prior'),caller=Object.create(null),oldRegex=/^[0-9]+$/
 Object.defineProperty(caller,'canary',{value:23})
 Object.preventExtensions(caller)
 Object.defineProperty(oldRegex,'lastIndex',{value:17,writable:false})
 Object.preventExtensions(oldRegex)
 const old=[prior,caller,oldRegex],before=old.map(Object.getOwnPropertyDescriptors),prototypes=old.map(Object.getPrototypeOf),extensible=old.map(Object.isExtensible)
 const returned=invoke.call(caller,label,prior,caller,pipeline?OriginalRegExp:lexicalShadow,fromUnits(test.input??[49,50]),oldRegex)
 const {outerPreserved,thisPreserved}=returned,observed=pipeline?returned.observed.match:returned.observed
 for(let i=0;i<old.length;i++){
  assert.deepEqual(Object.getOwnPropertyDescriptors(old[i]),before[i]);assert.equal(Object.getPrototypeOf(old[i]),prototypes[i]);assert.equal(Object.isExtensible(old[i]),extensible[i])
 }
 if(observed===null)return {result:{kind:'null'},captures:null,view:null,ownNames:null,outerPreserved,thisPreserved,oldFrames:true}
 assert(Array.isArray(observed));assert.notEqual(observed,prior);assert.equal(Object.getPrototypeOf(observed),Array.prototype);assert(Object.isExtensible(observed))
 const result={result:{kind:'array',ref:1},captures:Array.from({length:observed.length},(_,i)=>encode(observed[i])),view:view(observed),
  ownNames:Object.getOwnPropertyNames(observed).sort(),outerPreserved,thisPreserved,oldFrames:true}
 if(pipeline){
  const tuple=returned.produced,rx=tuple[2],m=returned.observed.m
  assert(Array.isArray(tuple));assert.equal(tuple.length,3);assert.equal(Object.getPrototypeOf(tuple),Array.prototype)
  assert.deepEqual(Reflect.ownKeys(tuple).sort(),['0','1','2','length'].sort())
  assert.equal(Object.getPrototypeOf(rx),RegExp.prototype)
  if(m!==null){assert(Array.isArray(m));assert.notEqual(m,observed);assert.notEqual(m,prior);assert.notEqual(m,tuple)}
  const mView=m===null?null:Object.fromEntries(['zero','length','index','input','groups'].map(k=>[k,view(m)[k]]))
  result.pipeline={produced:{tuple:{kind:'array',ref:2},label:encode(tuple[0]),name:encode(tuple[1]),
    source:units(sourceGetter.call(rx)),flags:units(flagsGetter.call(rx)),lastIndex:descriptor(Object.getOwnPropertyDescriptor(rx,'lastIndex'))},
   name:encode(returned.observed.name),matcherSameAsTuple:returned.observed.matcher===rx,
   m:m===null?{kind:'null'}:{kind:'array',ref:3},execCaptures:m===null?null:Array.from(m,encode),execView:mView}
 }
 return result
})
for(let i=0;i<intrinsics.length;i++){
 assert.deepEqual(Object.getOwnPropertyDescriptors(intrinsics[i]),intrinsicDescriptors[i]);assert.equal(Object.getPrototypeOf(intrinsics[i]),intrinsicPrototypes[i])
}
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,observerVerified:false,plainJavaScript:true,
 typescriptErasure:false,sourceSha256:sha(sources.full),executedSourceSha256:sha(source),wrapperInputSha256:sha(wrapper),
 hiddenLiteralObserved:false,protocolTraceNativeObserved:false,mode:pipeline?'pipeline':'label',results,
 scope:'Unwrapped current default operations on actual59B source; optional selected46B construction/44B binding/51B exec. Primitive UTF16 labels, computed capture/null values/descriptors and old-root frames. Hidden temporary literal/iterator identities/records/code/allocation/protocol are not native observations. Handoffs omit actual cache/tree/query production. Source wrapper/observer/transport/frontend/realm/engine adequacy remain unverified.'}))
