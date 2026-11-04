// Actual44B binding, with optional actual46B constructor and51B exec activations.
// Default DATA-domain observations; hidden protocol state is MODEL ONLY.
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
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath)), span = metadata.fragments.full
const original = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
assert.equal(sha(original), span.sha256)
assert.equal(span.sha256, '4bd90c878a3496b7a05edc1a3a90ba0e83afc24484b15acd1e600d5aff95a2a1')
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString(), original)
assert.equal(Buffer.byteLength(original), 44)
const packet=JSON.parse(readFileSync(0,'utf8')),pipeline=packet.mode==='pipeline'
const expression=packet.source??original
const ctorSource=readFileSync(new URL('../pattern-construct/full.ts.txt',import.meta.url),'utf8')
const execSource=readFileSync(new URL('../builtin-exec/full.ts.txt',import.meta.url),'utf8')
assert.equal(sha(ctorSource),'b70aef226ab3fc4a7ec886b9d64dbace87107beb4989920d05b48f6bd6b86560')
assert.equal(sha(execSource),'dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625')
assert.equal(readFileSync(resolve(checkout,'src/utils/url.ts')).subarray(1733,1779).toString(),ctorSource)
assert.equal(raw.subarray(4766,4817).toString(),execSource)
const wrapper=`"use strict";
const name='outer-name',matcher=previous,m=caller;
const oldPattern=pattern,oldAlternate=alternatePattern,oldInput=restPathString;
let observed;
{
${expression}
${pipeline?execSource:''}
observed={name,matcher,m};
}
return {...observed,scope:this===caller && name==='outer-name' && matcher===previous && m===caller && pattern===oldPattern && alternatePattern===oldAlternate && restPathString===oldInput};`
const invoke=new Function('pattern','alternatePattern','restPathString','previous','caller',wrapper)
const construct=new Function('label','match','RegExp',`"use strict";return (${ctorSource})`)
const OriginalRegExp=RegExp,exec=RegExp.prototype.exec,arrayValues=Array.prototype[Symbol.iterator]
const arrayIteratorPrototype=Object.getPrototypeOf([][Symbol.iterator]())
const iteratorPrototype=Object.getPrototypeOf(arrayIteratorPrototype)
const arrayNext=arrayIteratorPrototype.next
assert.equal(arrayValues,Array.prototype.values)
assert.equal(Reflect.get(arrayIteratorPrototype,'return'),undefined)
const intrinsicObjects=[Object.prototype,RegExp.prototype,Array.prototype,iteratorPrototype,arrayIteratorPrototype]
const intrinsicBefore=intrinsicObjects.map(Object.getOwnPropertyDescriptors)
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const functions={0:function old(){return 0},3:{exec(input){return input}}.exec,4:{exec(input){return[input]}}.exec,
  5:exec,6:OriginalRegExp,7:arrayValues,8:arrayNext}
const unitString=values=>values.map(value=>String.fromCharCode(value)).join('')
const units=value=>Array.from({length:value.length},(_,i)=>value.charCodeAt(i))
const results=packet.cases.map(input=>{
  const prior=exec.call(/^prior$/,'prior'),caller=Object.create(null),previous=/^[p-r]+$/
  Object.defineProperty(caller,'kept',{value:'canary',writable:true,enumerable:true,configurable:true})
  Object.defineProperty(previous,'lastIndex',{value:17,writable:false})
  const objects=[...intrinsicObjects,caller,previous],arrays=[prior,[],[]]
  const decode=value=>{
    switch(value.kind){
      case'undefined':return undefined
      case'null':return null
      case'bool':case'number':return value.value
      case'string':return unitString(value.units)
      case'array':assert(value.ref<arrays.length);return arrays[value.ref]
      case'object':assert(value.ref<objects.length);return objects[value.ref]
      case'function':assert(Object.hasOwn(functions,value.ref));return functions[value.ref]
      case'constructor':return Object
      default:throw new Error('Outside fixture transport')
    }
  }
  if(pipeline){
    arrays[1].push(unitString(input.label),unitString(input.name),unitString(input.body))
  }else arrays[1].push(...input.values.map(decode))
  arrays[2].push(...(input.alternateValues??[{kind:'string',units:units('alternate-label')},{kind:'string',units:units('alternate-name')},{kind:'object',ref:6}]).map(decode))
  let pattern=arrays[1]
  if(input.patternKind==='number')pattern=0
  if(input.patternKind==='undefined')pattern=undefined
  if(input.patternKind==='string')pattern='abc'
  const ownIterator=input.iteratorKind??'inherited'
  if(!pipeline && ownIterator!=='inherited')Object.defineProperty(arrays[1],Symbol.iterator,
    {value:ownIterator==='alias'?arrayValues:ownIterator==='number'?0:undefined,writable:true,enumerable:true,configurable:true})
  const oldArrayDescriptors=arrays.map(Object.getOwnPropertyDescriptors)
  const oldObjectDescriptors=objects.map(Object.getOwnPropertyDescriptors)
  const oldObjectPrototypes=objects.map(Object.getPrototypeOf),oldObjectExtensible=objects.map(Object.isExtensible)
  const previousSource=sourceGetter.call(previous),previousFlags=flagsGetter.call(previous)
  let produced
  if(pipeline){
    try{produced=construct(arrays[1][0],arrays[1],OriginalRegExp)}catch{return {ok:false}}
    assert(Array.isArray(produced)&&produced.length===3)
    assert.equal(Object.getPrototypeOf(produced),Array.prototype)
    assert.deepEqual(Reflect.ownKeys(produced).sort(),['0','1','2','length'].sort())
    arrays.push(produced);objects.push(produced[2]);pattern=produced
  }
  let observed
  try{observed=invoke.call(caller,pattern,arrays[2],unitString(input.input??[49,50]),previous,caller)}catch{return {ok:false}}
  if(pipeline&&Array.isArray(observed.m)&&!arrays.includes(observed.m))arrays.push(observed.m)
  const encode=value=>{
    if(value===undefined)return {kind:'undefined'}
    if(value===null)return {kind:'null'}
    if(value===Object)return {kind:'constructor'}
    if(typeof value==='boolean')return {kind:'bool',value}
    if(typeof value==='number')return {kind:'number',value}
    if(typeof value==='string')return {kind:'string',units:units(value)}
    if(arrays.includes(value))return {kind:'array',ref:arrays.indexOf(value)}
    if(objects.includes(value))return {kind:'object',ref:objects.indexOf(value)}
    for(const [handle,fn]of Object.entries(functions))if(value===fn)return {kind:'function',ref:Number(handle)}
    throw new Error('Outside bounded visible observation domain')
  }
  const descriptor=d=>{
    if(!d)return null
    assert('value'in d)
    return {kind:'data',value:encode(d.value),writable:d.writable,enumerable:d.enumerable,configurable:d.configurable}
  }
  const view=array=>Object.fromEntries([['zero','0'],['length','length'],['index','index'],['input','input'],['groups','groups']].map(([name,key])=>[name,descriptor(Object.getOwnPropertyDescriptor(array,key))]))
  const objectView=value=>({own:Object.getOwnPropertyNames(value).map(key=>({key:units(key),...descriptor(Object.getOwnPropertyDescriptor(value,key))})),
    prototype:Object.getPrototypeOf(value)===null?null:objects.indexOf(Object.getPrototypeOf(value)),extensible:Object.isExtensible(value)})
  const labels=['Object.prototype','RegExp.prototype','Array.prototype','Iterator.prototype','ArrayIterator.prototype']
  const visibleObjects=objects.map((value,index)=>index<5?{intrinsic:labels[index]}:objectView(value))
  const symbols=[{kind:'array',ref:1,descriptor:descriptor(Object.getOwnPropertyDescriptor(arrays[1],Symbol.iterator))},
    {kind:'array',ref:2,descriptor:descriptor(Object.getOwnPropertyDescriptor(arrays[2],Symbol.iterator))},
    {kind:'object',ref:2,descriptor:descriptor(Object.getOwnPropertyDescriptor(Array.prototype,Symbol.iterator))}]
  if(pipeline)symbols.push({kind:'array',ref:3,descriptor:descriptor(Object.getOwnPropertyDescriptor(produced,Symbol.iterator))})
  for(let index=0;index<oldArrayDescriptors.length;index++)assert.deepEqual(Object.getOwnPropertyDescriptors(arrays[index]),oldArrayDescriptors[index])
  for(let index=0;index<oldObjectDescriptors.length;index++){
    assert.deepEqual(Object.getOwnPropertyDescriptors(objects[index]),oldObjectDescriptors[index])
    assert.equal(Object.getPrototypeOf(objects[index]),oldObjectPrototypes[index]);assert.equal(Object.isExtensible(objects[index]),oldObjectExtensible[index])
  }
  const valueView=pipeline&&Array.isArray(observed.m)?view(observed.m):null
  if(valueView){assert.equal(Object.getPrototypeOf(observed.m),Array.prototype);assert.deepEqual(Reflect.ownKeys(observed.m).sort(),['0','length','index','input','groups'].sort())}
  return {ok:true,name:encode(observed.name),matcher:encode(observed.matcher),m:encode(observed.m),
    heap:arrays.map(value=>value.map(encode)),visibleObjects,symbols,view:valueView,priorView:view(prior),
    produced:pipeline?{tuple:encode(produced),regex:encode(produced[2]),source:units(sourceGetter.call(produced[2])),flags:units(flagsGetter.call(produced[2]))}:null,
    scope:observed.scope,oldFrames:true,brandsKept:sourceGetter.call(previous)===previousSource&&flagsGetter.call(previous)===previousFlags}
})
for(let index=0;index<intrinsicObjects.length;index++)assert.deepEqual(Object.getOwnPropertyDescriptors(intrinsicObjects[index]),intrinsicBefore[index])
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,plainJavaScript:true,typescriptErasure:false,
  sourceSha256:sha(original),executedSourceSha256:sha(expression),wrapperInputSha256:sha(wrapper),observerVerified:false,protocolTraceNativeObserved:false,
  mode:pipeline?'pipeline':'binding',results,
  scope:'Visible default-DATA binding and selected constructor→binding→exec activations. No native hidden iterator/result identities/counts/trace, physical allocation, Symbol/prototype/general iterator/frontend/engine or partial-error-state adequacy. Handoff is explicit, not child.#pattern/cache installation.'}))
