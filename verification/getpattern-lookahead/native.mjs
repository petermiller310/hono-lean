// Exact selected source60/62/67 fixture. Its wrapper and observation are unverified.
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
assert.equal(git('rev-parse','HEAD').trim(),revision);assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)){
 const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
 assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs,315)
const sha=x=>createHash('sha256').update(x).digest('hex')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const raw=readFileSync(resolve(checkout,metadata.sourcePath));assert.equal(sha(raw),metadata.sourceSha256)
for(const[name,span]of Object.entries(metadata.fragments)){
 const value=readFileSync(new URL('./'+name+'.ts.txt',import.meta.url));assert.equal(sha(value),span.sha256)
 assert.deepEqual(value,raw.subarray(span.startByte,span.endByteExclusive))
}
const body=readFileSync(new URL('../getpattern-body/body.ts.txt',import.meta.url),'utf8')
assert.equal(sha(body),metadata.reusedCompleteBody.sha256)
const packet=JSON.parse(readFileSync(0,'utf8')),executedBody=packet.source??body,lines=executedBody.split('\n')
// Fixed selected locations are an observer convenience, not a general parser.
// The Lean source connection instead projects nodes from the parsed full body.
const labelSource=lines[4],keySource=lines[6],positiveLine=lines[11].trim()
assert.ok(positiveLine.startsWith('? '))
const tupleSource=positiveLine.slice(2)
const selected=new Function('label','next','RegExp',`"use strict";\n${labelSource}\n${keySource}\nreturn ${tupleSource}\n`)
const actualModule=packet.actualModule===true
if(actualModule)assert.equal(executedBody,body)
const actual=actualModule?(await import(pathToFileURL(resolve(checkout,metadata.sourcePath)).href)).getPattern:null
const units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i))
const text=u=>u.map(n=>String.fromCharCode(n)).join('')
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const exec=RegExp.prototype.exec,NativeRegExp=RegExp
const intrinsics=[Object.prototype,String.prototype,RegExp.prototype,Array.prototype]
const snapshots=intrinsics.map(Object.getOwnPropertyDescriptors)
const actualKeys=new Set()
const results=packet.cases.map(fixture=>{
 if(actualModule){
  assert.notEqual(fixture.constructorKind,'number')
  const key=text(fixture.label)+'#'+text(fixture.next)
  assert.equal(actualKeys.has(key),false,'Full-module controls require distinct keys in each packet')
  actualKeys.add(key)
 }
 const caller=Object.create(null);Object.defineProperty(caller,'canary',{value:23});Object.preventExtensions(caller)
 const oldRegex=/^[0-9]+$/;Object.defineProperty(oldRegex,'lastIndex',{value:17,writable:false});Object.preventExtensions(oldRegex)
 const before=[caller,oldRegex].map(x=>[x,Object.getOwnPropertyDescriptors(x),Object.getPrototypeOf(x),Object.isExtensible(x)])
 let tuple
 try{
  tuple=actualModule?Reflect.apply(actual,caller,[text(fixture.label),text(fixture.next)]):
   Reflect.apply(selected,caller,[text(fixture.label),text(fixture.next),fixture.constructorKind==='number'?17:NativeRegExp])
 }catch(error){return{ok:false,errorName:error.name}}
 assert.ok(Array.isArray(tuple));assert.equal(tuple.length,3)
 const regex=tuple[2];assert.ok(regex instanceof NativeRegExp)
 Object.defineProperty(regex,'lastIndex',{value:fixture.lastIndex??0,writable:fixture.writable??true})
 const lastDescriptor=()=>{const d=Object.getOwnPropertyDescriptor(regex,'lastIndex');return{value:d.value,writable:d.writable,enumerable:d.enumerable,configurable:d.configurable}}
 const queries=[]
 for(const query of fixture.queries){
  const value=Reflect.apply(exec,regex,[text(query)])
  queries.push({value:value===null?null:{values:Array.from(value,units),index:value.index,input:units(value.input),groupsUndefined:value.groups===undefined},lastIndex:lastDescriptor()})
 }
 const oldFrames=before.every(([x,d,p,e])=>{assert.deepEqual(Object.getOwnPropertyDescriptors(x),d);return Object.getPrototypeOf(x)===p&&Object.isExtensible(x)===e})
 return{ok:true,tuple:[units(tuple[0]),units(tuple[1])],source:units(sourceGetter.call(regex)),flags:units(flagsGetter.call(regex)),
  ownSource:Object.hasOwn(regex,'source'),ownFlags:Object.hasOwn(regex,'flags'),prototypeStandard:Object.getPrototypeOf(regex)===NativeRegExp.prototype,
  extensible:Object.isExtensible(regex),lastIndex:lastDescriptor(),queries,oldFrames}
})
for(let i=0;i<intrinsics.length;i++)assert.deepEqual(Object.getOwnPropertyDescriptors(intrinsics[i]),snapshots[i])
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,observerVerified:false,typescriptLoaderVerified:false,
 nativeLanguageAdequacyVerified:false,sourceBytes:38,tupleBytes:60,completeBodyBytes:576,executedBodySha256:sha(executedBody),actualModule,
 selectedSourceExtractionVerified:false,ancestorGuardsExecuted:actualModule,hiddenAllocationsObserved:false,results,
 scope:actualModule?'Unmodified full pinned url.ts export, finite observation only; TS/module/closure/cache/native adequacy unverified.':
 'Actual selected60/62/67 snippets in unverified strict wrapper. Ancestor guards/cache/store/source74/lexical bootstrap are NOT executed. Direct saved native RegExp.prototype.exec; no dynamic method-Get theorem. Source getter display is an observation, not internal raw source.'}))
