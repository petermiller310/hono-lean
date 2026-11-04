// Complete pinned wildcard + cache body; explicit caller-owned persistent cache fixture.
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
assert.equal(sha(sources.body),'f72f8a61edff659809d83048b3b8861b2baf00885682c86943e4e55fdedc7419')
const packet=JSON.parse(readFileSync(0,'utf8')),source=packet.source??sources.body
const factory=new Function('patternCache','RegExp',`return function(label,next){"use strict";\n${source}\n}`)
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i)),text=u=>u.map(n=>String.fromCharCode(n)).join('')
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const intrinsics=[Object.prototype,String.prototype,RegExp.prototype,Array.prototype]
const beforeIntrinsics=intrinsics.map(Object.getOwnPropertyDescriptors)
const results=packet.cases.map(fixture=>{
 const prior=/^prior$/.exec('prior'),empty=[],caller=Object.create(null),oldRegex=/^[0-9]+$/
 Object.defineProperty(caller,'canary',{value:23});Object.preventExtensions(caller)
 Object.defineProperty(oldRegex,'lastIndex',{value:17,writable:false});Object.preventExtensions(oldRegex)
 const cache={},parent=Object.create(null),arrays=[prior,empty],objects=[caller,oldRegex,cache,parent]
 const visible=[['a0',prior],['a1',empty],['caller',caller],['oldRegex',oldRegex],['cache',cache],['parent',parent],['RegExp',RegExp]]
 const decode=v=>{
  if(v.kind==='undefined')return undefined;if(v.kind==='null')return null
  if(v.kind==='string')return text(v.units)
  if(v.kind==='bool'||v.kind==='number')return v.value
  if(v.kind==='array')return arrays[v.ref]
  if(v.kind==='object')return objects[v.ref]
  if(v.kind==='function'&&v.ref===6)return RegExp
  throw Error('Outside fixture input domain')
 }
 const install=(object,fields)=>{for(const f of fields??[])Object.defineProperty(object,text(f.key),{value:decode(f.value),
  writable:f.writable??true,enumerable:f.enumerable??true,configurable:f.configurable??true})}
 install(cache,fixture.seed);install(parent,fixture.inherited)
 if(fixture.inherited?.length)Object.setPrototypeOf(cache,parent)
 if(fixture.extensible===false)Object.preventExtensions(cache)
 const snapshots=[prior,empty,caller,oldRegex,parent].map(x=>[x,Object.getOwnPropertyDescriptors(x),Object.getPrototypeOf(x),Object.isExtensible(x)])
 const f=factory(fixture.cacheKind==='undefined'?undefined:cache,fixture.constructorKind==='number'?0:RegExp)
 let returnedCount=0
 const register=value=>{
  if((typeof value==='object'&&value!==null)||typeof value==='function'){
   if(!visible.some(([_,x])=>x===value))visible.push(['r'+returnedCount++,value])
   if(Array.isArray(value))for(const x of value)if(x instanceof RegExp&&!visible.some(([_,v])=>v===x))visible.push(['r'+(returnedCount-1)+'.regex',x])
  }
 }
 const encode=value=>{
  if(value===undefined)return{kind:'undefined'};if(value===null)return{kind:'null'}
  if(typeof value==='boolean')return{kind:'bool',value};if(typeof value==='number')return{kind:'number',value}
  if(typeof value==='string')return{kind:'string',units:units(value)}
  const found=visible.find(([_,x])=>x===value);if(found)return{kind:'reference',id:found[0]}
  throw Error('Unexposed value in visible observation')
 }
 const descriptor=d=>({kind:'data',value:encode(d.value),writable:d.writable,enumerable:d.enumerable,configurable:d.configurable})
 const cacheView=()=>({own:Object.getOwnPropertyNames(cache).sort().map(k=>({key:units(k),...descriptor(Object.getOwnPropertyDescriptor(cache,k))})),
  prototype:Object.getPrototypeOf(cache)===parent?'parent':Object.getPrototypeOf(cache)===Object.prototype?'Object.prototype':null,extensible:Object.isExtensible(cache)})
 const observations=[]
 for(const step of fixture.steps){
  let value
  try{value=f.call(caller,text(step.label),decode(step.next??{kind:'undefined'}),decode(step.match??{kind:'undefined'}))}
  catch(error){observations.push({ok:false,errorName:error.name});break}
  register(value)
  // Cache properties can expose a fresh value even when a mutated return path
  // returns something else. Assign observer IDs when that graph becomes visible.
  for(const name of Object.getOwnPropertyNames(cache).sort()){
   const property=Object.getOwnPropertyDescriptor(cache,name)
   if('value'in property)register(property.value)
  }
  const graph=visible.filter(([id])=>id.startsWith('r')).map(([id,x])=>Array.isArray(x)?{id,kind:'array',values:Array.from(x,encode)}:
   x instanceof RegExp?{id,kind:'regexp',source:units(sourceGetter.call(x)),flags:units(flagsGetter.call(x)),lastIndex:descriptor(Object.getOwnPropertyDescriptor(x,'lastIndex'))}:
   (()=>{throw Error('Unexpected newly exposed object')})())
  const oldFrames=snapshots.every(([x,d,p,e])=>{assert.deepEqual(Object.getOwnPropertyDescriptors(x),d);return Object.getPrototypeOf(x)===p&&Object.isExtensible(x)===e})
  observations.push({ok:true,value:encode(value),cache:cacheView(),visibleGraph:graph,oldFrames})
 }
 return observations
})
for(let i=0;i<intrinsics.length;i++)assert.deepEqual(Object.getOwnPropertyDescriptors(intrinsics[i]),beforeIntrinsics[i])
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,observerVerified:false,
 plainJavaScriptBody:true,typescriptInitializationObserved:false,closureBootstrapVerified:false,hiddenAllocationsObserved:false,
 sourceBytes:576,sourceSha256:sha(sources.body),executedSourceSha256:sha(source),results,
 scope:'Actual complete576B wildcard+cache body, explicit same caller-owned cache across calls. Visible cache DATA/prototype/extensibility and returned identity graph only; no private module cache observation or hidden literal/capture allocation counts. Init52B TS is not executed here. Wrappers/JSON/realm/frontend/native/closure bootstrap unverified. Stop at first native error, no rollback or failure-state claim.'}))
