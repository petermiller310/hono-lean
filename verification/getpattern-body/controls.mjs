// Native-only effect controls; body and actual-module evidence are distinct.
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
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const source=readFileSync(new URL('./body.ts.txt',import.meta.url),'utf8')
const hash=createHash('sha256').update(source).digest('hex')
assert.equal(hash,metadata.fragments.body.sha256)
assert.equal(readFileSync(resolve(checkout,metadata.sourcePath)).subarray(1344,1920).toString(),source)
const make=(cache,constructor)=>new Function('patternCache','RegExp',`return function(label,next){"use strict";\n${source}\n}`)(cache,constructor)
const results=[]
{
  const trace=[],target={}
  const cache=new Proxy(target,{get(){trace.push('cache-get');throw Error('cache-get')},set(){trace.push('cache-set');throw Error('cache-set')}})
  const constructor=new Proxy(function(){},{construct(){trace.push('construct');throw Error('construct')},get(){trace.push('ctor-property');throw Error('ctor-property')}})
  const next={[Symbol.toPrimitive](){trace.push('next-coercion');throw Error('next-coercion')},get 0(){trace.push('next-index');throw Error('next-index')}}
  const saved=Object.getOwnPropertyDescriptor(String.prototype,'match')
  const f=make(cache,constructor);let value
  try{
    Object.defineProperty(String.prototype,'match',{configurable:true,get(){trace.push('match-get');throw Error('match-get')}})
    value=f('*',next)
  }finally{Object.defineProperty(String.prototype,'match',saved)}
  assert.equal(value,'*');assert.deepEqual(trace,[]);assert.deepEqual(Object.getOwnPropertyDescriptors(target),{})
  assert.deepEqual(Object.getOwnPropertyDescriptor(String.prototype,'match'),saved)
  results.push({id:'wildcard-skips-all-effects',value,trace,cacheOwnKeys:[]})
}
{
  const trace=[],cache=new Proxy({},{get(){trace.push('cache-get');throw Error('cache-get')}})
  const label={[Symbol.toPrimitive](){trace.push('label-coercion');throw Error('coercion')},match(literal){trace.push('label-match');assert.equal(this,label);assert.equal(Object.prototype.toString.call(literal),'[object RegExp]');return null}}
  const value=make(cache,17)(label)
  assert.equal(value,null);assert.deepEqual(trace,['label-match'])
  results.push({id:'strict-comparison-does-not-coerce-object-label',value,trace})
}
if(runtime==='bun'){
  // Actual pinned TypeScript export and module cache; loader/closure adequacy
  // is explicitly unverified. Import finishes before intrusive getter controls.
  const {getPattern}=await import(pathToFileURL(resolve(checkout,'src/utils/url.ts')).href)
  const trace=[],savedMatch=Object.getOwnPropertyDescriptor(String.prototype,'match'),savedCtor=Object.getOwnPropertyDescriptor(globalThis,'RegExp')
  const next={[Symbol.toPrimitive](){trace.push('next-coercion');throw Error('next-coercion')}}
  let first,second
  try{
    Object.defineProperty(String.prototype,'match',{configurable:true,get(){trace.push('match-get');throw Error('match-get')}})
    Object.defineProperty(globalThis,'RegExp',{configurable:true,get(){trace.push('ctor-get');throw Error('ctor-get')}})
    first=getPattern('*',next);second=getPattern('*',next)
  }finally{
    Object.defineProperty(String.prototype,'match',savedMatch)
    Object.defineProperty(globalThis,'RegExp',savedCtor)
  }
  assert.equal(first,'*');assert.equal(second,'*');assert.deepEqual(trace,[])
  assert.deepEqual(Object.getOwnPropertyDescriptor(String.prototype,'match'),savedMatch)
  assert.deepEqual(Object.getOwnPropertyDescriptor(globalThis,'RegExp'),savedCtor)
  results.push({id:'actual-pinned-bun-module-wildcard',first,second,trace,typescriptLoadingVerified:false,formalInvocationTheorem:null})
}
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,sourceBytes:576,sourceSha256:hash,verified:false,nativeOnly:true,observerVerified:false,
  actualModuleProbe:runtime==='bun',typescriptLoadingVerified:false,formalFunctionInvocationTheorem:null,formalModuleTheorem:null,baselineAllowlistChanged:false,results}))
