// Exact81B source in an unverified private-field wrapper. O0 denotes the real
// realm Object.prototype; its modeled snapshot is an explicit intrinsic
// projection, with a separate full native frame check. No key-order adequacy.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
const sha=bytes=>createHash('sha256').update(bytes).digest('hex')
const runtime=typeof Bun==='undefined'?'node':'bun',version=runtime==='bun'?Bun.version:process.versions.node
assert.equal(version,runtime==='bun'?'1.4.0':'22.22.2')
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)) {
  const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const raw=readFileSync(resolve(checkout,metadata.sourcePath)),span=metadata.fragments.full
const pinned=readFileSync(new URL('./full.ts.txt',import.meta.url),'utf8')
assert.equal(metadata.revision,revision);assert.equal(sha(raw),metadata.sourceSha256)
assert.equal(sha(pinned),span.sha256);assert.equal(raw.subarray(span.startByte,span.endByteExclusive).toString('ascii'),pinned)
const packet=JSON.parse(readFileSync(0,'utf8')),source=packet.source??pinned
const string=units=>{assert(units.every(unit=>Number.isInteger(unit)&&unit>=0&&unit<65536));return units.map(unit=>String.fromCharCode(unit)).join('')}
const units=text=>Array.from({length:text.length},(_,i)=>text.charCodeAt(i))
const legacy=Object.getOwnPropertyDescriptor(Object.prototype,'__proto__')
const intrinsicFrame=Object.getOwnPropertyDescriptors(Object.prototype)
assert.equal(Object.getOwnPropertySymbols(Object.prototype).length,0)
assert(Object.values(intrinsicFrame).every(descriptor=>descriptor.enumerable===false))
const wrapper=`return class Fragment {
  #params;
  static seed(node,value) { node.#params=value; }
  static selected(node,emptyParams,canary) {
    const params=canary, p=canary, offset=canary;
    let result;
    {
${source}
      result=params;
    }
    return {result,slot:node.#params,scope:params===canary&&p===canary&&offset===canary};
  }
}`
const Fragment=new Function(wrapper)()
const results=(packet.cases??[]).map(input=>{
  assert.deepEqual(input.objects[0],{intrinsicPrototype:true});assert(input.node>0&&input.node<input.objects.length)
  assert(input.source>=0&&input.source<input.objects.length);assert(input.emptyParams>=0&&input.emptyParams<input.objects.length)
  const arrays=input.heap.map(()=>[])
  const objects=input.objects.map((_,i)=>i===0?Object.prototype:i===input.node?new Fragment():Object.create(null))
  const decode=value=>{
    switch(value.kind) {
      case 'undefined':return undefined
      case 'null':return null
      case 'bool':case 'number':return value.value
      case 'string':return string(value.units)
      case 'object':assert(value.ref<objects.length);return objects[value.ref]
      case 'array':assert(value.ref<arrays.length);return arrays[value.ref]
      case 'constructor':return Object
      default:throw new Error('Unsupported fixture value')
    }
  }
  const encode=value=>{
    if(value===undefined)return {kind:'undefined'}
    if(value===null)return {kind:'null'}
    if(value===Object)return {kind:'constructor'}
    if(typeof value==='boolean')return {kind:'bool',value}
    if(typeof value==='number')return {kind:'number',value}
    if(typeof value==='string')return {kind:'string',units:units(value)}
    if(objects.includes(value))return {kind:'object',ref:objects.indexOf(value)}
    if(arrays.includes(value))return {kind:'array',ref:arrays.indexOf(value)}
    throw new Error('Unregistered output value')
  }
  let getterCalls=0,setterCalls=0
  const badGetter=()=>{getterCalls++;throw new TypeError('particular fixture getter')}
  const badSetter=()=>{setterCalls++;throw new TypeError('particular fixture setter')}
  const get=name=>name==='missing'?undefined:name==='prototype'?legacy.get:badGetter
  const set=name=>name==='missing'?undefined:name==='prototype'?legacy.set:badSetter
  input.heap.forEach((row,i)=>row.forEach((value,j)=>{arrays[i][j]=decode(value)}))
  input.objects.forEach((object,i)=>{
    if(i===0)return
    for(const field of object.own) {
      const common={enumerable:field.enumerable,configurable:field.configurable}
      Object.defineProperty(objects[i],string(field.key),field.kind==='data'
        ?{...common,value:decode(field.value),writable:field.writable}
        :{...common,get:get(field.getter),set:set(field.setter)})
    }
  })
  input.objects.forEach((object,i)=>{if(i)Object.setPrototypeOf(objects[i],object.prototype===null?null:objects[object.prototype])})
  Fragment.seed(objects[input.node],objects[input.source])
  input.objects.forEach((object,i)=>{if(i&&!object.extensible)Object.preventExtensions(objects[i])})
  try {
    const output=Fragment.selected.call(objects[input.node],objects[input.node],objects[input.emptyParams],Symbol('outer locals'))
    const result=output.result,oldLength=objects.length
    if(result!==null&&typeof result==='object'&&!objects.includes(result)&&!arrays.includes(result))objects.push(result)
    const snapshot=objects.map((object,i)=>{
      if(i===0)return {intrinsicPrototype:true}
      const prototype=Object.getPrototypeOf(object)
      assert(prototype===null||objects.includes(prototype),'Unregistered prototype')
      return {prototype:prototype===null?null:objects.indexOf(prototype),extensible:Object.isExtensible(object),own:Reflect.ownKeys(object).map(key=>{
        assert.equal(typeof key,'string');const field=Object.getOwnPropertyDescriptor(object,key)
        const common={key:units(key),enumerable:field.enumerable,configurable:field.configurable}
        if('value' in field)return {...common,kind:'data',value:encode(field.value),writable:field.writable}
        return {...common,kind:'accessor',getter:field.get===undefined?'missing':field.get===legacy.get?'prototype':'unsupported',
          setter:field.set===undefined?'missing':field.set===legacy.set?'prototype':'unsupported'}
      })}
    })
    assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype),intrinsicFrame)
    return {ok:true,result:encode(result),slot:encode(output.slot),scope:output.scope,objects:snapshot,
      heap:arrays.map(row=>row.map(encode)),fresh:objects.length===oldLength+1&&result===objects[oldLength],
      getterCalls,setterCalls}
  } catch(error) {
    if(!(error instanceof TypeError||error instanceof ReferenceError||error instanceof RangeError))throw error
    assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype),intrinsicFrame)
    return {ok:false}
  }
})
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,fragmentTypeErasure:false,
  sourceBytes:Buffer.byteLength(source),wrapperSha256:sha(wrapper),intrinsicPrototypeProjection:true,
  observation:'Extensional own descriptors/prototype refs and source-visible identities. O0 intrinsic projection plus separate full native root frame; no own-key order or total native-allocation claim.',results}))
