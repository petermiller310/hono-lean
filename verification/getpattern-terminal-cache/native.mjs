// Exact selected cache body, followed by ordinary native execution of its stored regex.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

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
const metadata=JSON.parse(readFileSync(new URL('../getpattern-cache/source.json',import.meta.url)))
const raw=readFileSync(resolve(checkout,metadata.sourcePath))
assert.equal(metadata.revision,revision);assert.equal(sha(raw),metadata.sourceSha256)
const fragment=metadata.fragments.full
const original=readFileSync(new URL('../getpattern-cache/full.ts.txt',import.meta.url),'utf8')
assert.equal(sha(original),'0ce62880eb018a718c7d3f32bb413e31bf5b8c42e31bba1e289d280529a47cf5')
assert.equal(sha(original),fragment.sha256)
assert.equal(raw.subarray(fragment.startByte,fragment.endByteExclusive).toString(),original)
const packet=JSON.parse(readFileSync(0,'utf8')),source=packet.source??original
const factory=new Function('patternCache','RegExp',`return function(label,next){"use strict";\n${source}\n}`)
const units=text=>Array.from({length:text.length},(_,i)=>text.charCodeAt(i))
const text=units=>String.fromCharCode(...units)
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const results=packet.cases.map(fixture=>{
  const cache={},f=factory(cache,RegExp),label=text(fixture.label)
  const next=fixture.next.kind==='undefined'?undefined:text(fixture.next.units)
  const prior=/^prior$/.exec('prior'),caller=Object.create(null),oldRegex=/^[0-9]+$/
  Object.defineProperty(caller,'canary',{value:23});Object.preventExtensions(caller)
  Object.defineProperty(oldRegex,'lastIndex',{value:17,writable:false});Object.preventExtensions(oldRegex)
  const snapshots=[prior,caller,oldRegex,Object.prototype,RegExp.prototype,String.prototype,Array.prototype].map(object=>[
    object,Object.getOwnPropertyDescriptors(object),Object.getPrototypeOf(object),Object.isExtensible(object)])
  try{
    const first=f.call(caller,label,next)
    const retained=[first,first?.[2],cache].map(object=>[object,Object.getOwnPropertyDescriptors(object),Object.getPrototypeOf(object),Object.isExtensible(object)])
    const second=f.call(caller,label,next)
    if(!Array.isArray(first)||!Array.isArray(second)||!(first[2] instanceof RegExp)||!(second[2] instanceof RegExp))return{ok:false}
    const regex=first[2]
    const queries=fixture.queries.map(query=>{
      const result=regex.exec(text(query))
      return result===null?null:{index:result.index,value:units(result[0]),captures:Array.from(result.slice(1),capture=>capture===undefined?null:units(capture))}
    })
    const last=Object.getOwnPropertyDescriptor(regex,'lastIndex')
    const oldFrames=[...snapshots,...retained].every(([object,descriptors,prototype,extensible])=>{
      assert.deepEqual(Object.getOwnPropertyDescriptors(object),descriptors)
      return Object.getPrototypeOf(object)===prototype&&Object.isExtensible(object)===extensible
    })
    return{ok:true,label:units(first[0]),name:units(first[1]),source:units(sourceGetter.call(regex)),flags:units(flagsGetter.call(regex)),
      lastIndex:{value:last.value,writable:last.writable,enumerable:last.enumerable,configurable:last.configurable},
      sameTuple:first===second,sameRegex:regex===second[2],cacheReturnsSameTuple:cache[`${label}#${next}`]===first,oldFrames,queries}
  }catch{return{ok:false}}
})
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,sourceBytes:533,sourceSha256:sha(original),executedSourceSha256:sha(source),
  verified:false,observerVerified:false,typescriptInitializationObserved:false,closureBootstrapVerified:false,node156SourceExecuted:false,
  scope:'Exact533B selected body with explicit persistent cache; native regex.exec compared to stored compiled model VM. No whole getPattern, node156 source pipeline, module bootstrap, hidden-allocation/protocol or native adequacy theorem.',results}))
