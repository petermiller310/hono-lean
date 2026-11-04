// Actual selected TypeScript setup, once per module; observer export appended.
// Module loading/type erasure/observer/native adequacy are NOT kernel verified.
import assert from 'node:assert/strict'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdtempSync, readFileSync, writeFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {resolve, join} from 'node:path'
import {pathToFileURL} from 'node:url'

const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime=typeof Bun==='undefined'?'node':'bun',version=runtime==='bun'?Bun.version:process.versions.node
assert.equal(version,runtime==='bun'?'1.4.0':'22.22.2')
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)){
 const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
 assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob)
 checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs,315)
const sha=bytes=>createHash('sha256').update(bytes).digest('hex')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const setup=readFileSync(new URL('./setup.ts.txt',import.meta.url),'utf8')
const raw=readFileSync(resolve(checkout,metadata.sourcePath)),span=metadata.fragments.setup
assert.equal(metadata.revision,revision);assert.equal(sha(raw),metadata.sourceSha256)
assert.equal(sha(setup),span.sha256)
assert.equal(raw.subarray(span.startByte,span.endByteExclusive).toString(),setup)
assert.equal(Buffer.byteLength(setup),796)
const packet=JSON.parse(readFileSync(0,'utf8')),source=packet.source??setup
const observer='\nexport const __getPatternCacheObserver = () => patternCache\n'
const directory=mkdtempSync(join(tmpdir(),'hono-arrow-native-'))
const NativeRegExp=RegExp,regExpDescriptor=Object.getOwnPropertyDescriptor(globalThis,'RegExp')
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i))
const text=u=>u.map(n=>String.fromCharCode(n)).join('')
const sourceGetter=Object.getOwnPropertyDescriptor(NativeRegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(NativeRegExp.prototype,'flags').get
const intrinsics=[Object.prototype,String.prototype,NativeRegExp.prototype,Array.prototype,Function.prototype]
const beforeIntrinsics=intrinsics.map(Object.getOwnPropertyDescriptors)
const results=[]
// Create the complete fixture graph before either runtime's module resolver
// begins loading; a resolver may cache directory entries during the first import.
for(let index=0;index<packet.cases.length;index++)writeFileSync(join(directory,`case-${index}.ts`),source+observer)
try{
 for(const[caseIndex,fixture]of packet.cases.entries()){
  Object.defineProperty(globalThis,'RegExp',regExpDescriptor)
  const file=join(directory,`case-${caseIndex}.ts`)
  const module=await import(pathToFileURL(file).href)
  const f=module.getPattern,cache=module.__getPatternCacheObserver(),parent=Object.create(null)
  assert.equal(typeof f,'function');assert.equal(Object.getPrototypeOf(cache),Object.prototype)
  const metadataView={name:Object.getOwnPropertyDescriptor(f,'name'),length:Object.getOwnPropertyDescriptor(f,'length'),
   ownPrototype:Object.hasOwn(f,'prototype'),functionPrototype:Object.getPrototypeOf(f)===Function.prototype}
  let nonConstructible=false
  try{Reflect.construct(f,['*'])}catch(error){assert.equal(error.name,'TypeError');nonConstructible=true}
  assert.deepEqual(Object.keys(cache),[])
  const prior=/^prior$/.exec('prior'),empty=[],caller=Object.create(null),oldRegex=/^[0-9]+$/
  Object.defineProperty(caller,'canary',{value:23});Object.preventExtensions(caller)
  Object.defineProperty(oldRegex,'lastIndex',{value:17,writable:false});Object.preventExtensions(oldRegex)
  const arrays=[prior,empty],objects=[caller,oldRegex,cache,parent]
  const visible=[['a0',prior],['a1',empty],['caller',caller],['oldRegex',oldRegex],['cache',cache],['parent',parent],['RegExp',NativeRegExp],['getPattern',f]]
  const decode=v=>{
   if(v.kind==='undefined')return undefined;if(v.kind==='null')return null
   if(v.kind==='string')return text(v.units)
   if(v.kind==='bool'||v.kind==='number')return v.value
   if(v.kind==='array')return arrays[v.ref];if(v.kind==='object')return objects[v.ref]
   if(v.kind==='function'&&v.ref===6)return NativeRegExp
   throw Error('Outside fixture input domain')
  }
  const install=(object,fields)=>{for(const field of fields??[])Object.defineProperty(object,text(field.key),{value:decode(field.value),
   writable:field.writable??true,enumerable:field.enumerable??true,configurable:field.configurable??true})}
  install(cache,fixture.seed);install(parent,fixture.inherited)
  if(fixture.inherited?.length)Object.setPrototypeOf(cache,parent)
  if(fixture.extensible===false)Object.preventExtensions(cache)
  const snapshots=[prior,empty,caller,oldRegex,parent,f].map(x=>[x,Object.getOwnPropertyDescriptors(x),Object.getPrototypeOf(x),Object.isExtensible(x)])
  let returnedCount=0
  const register=value=>{
   if((typeof value==='object'&&value!==null)||typeof value==='function'){
    if(!visible.some(([_,x])=>x===value))visible.push(['r'+returnedCount++,value])
    if(Array.isArray(value))for(const x of value)if(x instanceof NativeRegExp&&!visible.some(([_,v])=>v===x))visible.push(['r'+(returnedCount-1)+'.regex',x])
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
   if(step.constructorKind!==undefined)Object.defineProperty(globalThis,'RegExp',{...regExpDescriptor,value:step.constructorKind==='number'?0:NativeRegExp})
   const args=step.arguments?.map(decode)??[text(step.label),decode(step.next??{kind:'undefined'})]
   let value
   try{value=Reflect.apply(f,caller,args)}catch(error){observations.push({ok:false,errorName:error.name});break}
   register(value)
   for(const name of Object.getOwnPropertyNames(cache).sort()){
    const property=Object.getOwnPropertyDescriptor(cache,name);if('value'in property)register(property.value)
   }
   const graph=visible.filter(([id])=>id.startsWith('r')).map(([id,x])=>Array.isArray(x)?{id,kind:'array',values:Array.from(x,encode)}:
    x instanceof NativeRegExp?{id,kind:'regexp',source:units(sourceGetter.call(x)),flags:units(flagsGetter.call(x)),lastIndex:descriptor(Object.getOwnPropertyDescriptor(x,'lastIndex'))}:
    (()=>{throw Error('Unexpected newly exposed object')})())
   const oldFrames=snapshots.every(([x,d,p,e])=>{assert.deepEqual(Object.getOwnPropertyDescriptors(x),d);return Object.getPrototypeOf(x)===p&&Object.isExtensible(x)===e})
   observations.push({ok:true,value:encode(value),cache:cacheView(),visibleGraph:graph,oldFrames})
  }
  results.push({metadata:metadataView,nonConstructible,sameExport:module.getPattern===f,sameCache:module.__getPatternCacheObserver()===cache,observations})
 }
}finally{
 Object.defineProperty(globalThis,'RegExp',regExpDescriptor)
 rmSync(directory,{recursive:true,force:true})
}
for(let i=0;i<intrinsics.length;i++)assert.deepEqual(Object.getOwnPropertyDescriptors(intrinsics[i]),beforeIntrinsics[i])
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,observerVerified:false,
 typescriptLoaderVerified:false,moduleInstantiationVerified:false,nativeLanguageAdequacyVerified:false,hiddenAllocationsObserved:false,
 sourceBytes:796,sourceSha256:sha(setup),executedPrefixSha256:sha(source),observerSuffixSha256:sha(observer),results,
 scope:'Exact selected796B TypeScript setup plus appended private-cache observer, fresh module per history. Setup creates cache/exportedarrow once, real supplied args via Reflect.apply, current mutable global RegExp between calls. Visible metadata, cache and returned identity graph only. Type erasure, loader, module instantiation, observer and native adequacy unverified. Stop at first native error, no failure-state/rollback claim.'}))
