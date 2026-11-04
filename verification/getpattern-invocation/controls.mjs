// Actual selected TypeScript setup, once per module; observer export appended.
// Module loading/type erasure/observer/native adequacy are NOT kernel verified.
import assert from 'node:assert/strict'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
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
// The entire actual pinned source module is loaded here, independently of the
// selected-setup observer fixture. Loading and runtime semantics remain unverified.
const {getPattern}=await import(pathToFileURL(resolve(checkout,'src/utils/url.ts')).href)
const NativeRegExp=RegExp,savedCtor=Object.getOwnPropertyDescriptor(globalThis,'RegExp')
const savedMatch=Object.getOwnPropertyDescriptor(String.prototype,'match')
const results=[]
try{
 {
  const trace=[],next={[Symbol.toPrimitive](){trace.push('next-coercion');throw Error('next')}}
  Object.defineProperty(String.prototype,'match',{configurable:true,get(){trace.push('match-get');throw Error('match')}})
  Object.defineProperty(globalThis,'RegExp',{configurable:true,get(){trace.push('ctor-get');throw Error('ctor')}})
  const first=Reflect.apply(getPattern,{caller:true},['*',next]),second=getPattern('*',next,17)
  assert.equal(first,'*');assert.equal(second,'*');assert.deepEqual(trace,[])
  results.push({id:'actual-module-arrow-wildcard-skips-getters',first,second,trace})
  Object.defineProperty(String.prototype,'match',savedMatch);Object.defineProperty(globalThis,'RegExp',savedCtor)
 }
 {
  const label=':arrowWarm{[0-9]+}',first=getPattern(label)
  Object.defineProperty(globalThis,'RegExp',{...savedCtor,value:0})
  const second=getPattern(label,undefined,{});let coldError
  try{getPattern(':arrowCold{[0-9]+}')}catch(error){coldError=error.name}
  assert.equal(first,second);assert.equal(coldError,'TypeError')
  results.push({id:'actual-module-current-global-between-calls',sameWarmTuple:first===second,coldError})
  Object.defineProperty(globalThis,'RegExp',savedCtor)
 }
 {
  const first=getPattern(':arrowArgs'),second=getPattern(':arrowArgs',undefined),third=getPattern(':arrowArgs',undefined,{ignored:true})
  assert.equal(first,second);assert.equal(second,third)
  const descriptors=Object.getOwnPropertyDescriptors(getPattern)
  assert.equal(getPattern.name,'getPattern');assert.equal(getPattern.length,2);assert.equal(Object.hasOwn(getPattern,'prototype'),false)
  Object.defineProperty(getPattern,'prototype',{value:{},configurable:true})
  let constructError
  try{Reflect.construct(getPattern,['*'])}catch(error){constructError=error.name}
  assert.equal(constructError,'TypeError');delete getPattern.prototype
  assert.deepEqual(Object.getOwnPropertyDescriptors(getPattern),descriptors)
  results.push({id:'actual-module-arguments-and-arrow-kind',omittedUndefinedExtraSame:first===second&&second===third,
   name:getPattern.name,length:getPattern.length,noOwnPrototype:!Object.hasOwn(getPattern,'prototype'),constructErrorAfterAddingPrototype:constructError})
 }
 {
  // Frontier control: a user-visible callback can change a global DURING a call.
  // The closed intrinsic dispatch in the Lean profiles cannot mutate cell heaps.
  const trace=[],constructor=new Proxy(NativeRegExp,{construct(target,args,newTarget){trace.push('construct');return Reflect.construct(target,args,newTarget)}})
  Object.defineProperty(String.prototype,'match',{...savedMatch,value:function(literal){
   trace.push('match');Object.defineProperty(globalThis,'RegExp',{configurable:true,get(){trace.push('global-read');return constructor}})
   return Reflect.apply(savedMatch.value,this,[literal])
  }})
  const value=getPattern(':arrowDuring{[A-z]+}')
  assert.deepEqual(trace,['match','global-read','construct']);assert.equal(value[2].source,'^[A-z]+$')
  results.push({id:'callback-mutates-global-during-call-frontier',trace,source:value[2].source,formalCallbackTheorem:null})
 }
}finally{
 Object.defineProperty(String.prototype,'match',savedMatch)
 Object.defineProperty(globalThis,'RegExp',savedCtor)
}
assert.deepEqual(Object.getOwnPropertyDescriptor(String.prototype,'match'),savedMatch)
assert.deepEqual(Object.getOwnPropertyDescriptor(globalThis,'RegExp'),savedCtor)
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,sourceBytes:796,sourceSha256:sha(setup),
 verified:false,nativeOnly:true,actualFullModule:true,typescriptLoaderVerified:false,moduleInstantiationVerified:false,
 formalNativeLanguageAdequacyTheorem:null,formalGeneralCallbackTheorem:null,baselineAllowlistChanged:false,results}))
