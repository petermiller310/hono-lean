// Actual selected terminal tuple expression on genuine RegExp constructor identity.
// Plain-JS wrappers, observer and engine interpretation remain unverified.
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
assert.equal(span.sha256, 'b70aef226ab3fc4a7ec886b9d64dbace87107beb4989920d05b48f6bd6b86560')
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString(), original)
assert.equal(Buffer.byteLength(original), 46)
const packet = JSON.parse(readFileSync(0, 'utf8'))
const expression = packet.source ?? original
const wrapper = `"use strict";
const oldLabel = label, oldMatch = match, oldRegExp = RegExp, oldAlias = Alias, oldThis = this;
const tuple = (${expression});
return {tuple, scope:label===oldLabel && match===oldMatch && RegExp===oldRegExp && Alias===oldAlias && this===oldThis};`
const evaluate = new Function('label', 'match', 'RegExp', 'Alias', 'alternateLabel', 'alternateName', 'alternateBody', wrapper)
const OriginalRegExp = RegExp, builtin = RegExp.prototype.exec
const sourceGetter = Object.getOwnPropertyDescriptor(RegExp.prototype, 'source').get
const flagsGetter = Object.getOwnPropertyDescriptor(RegExp.prototype, 'flags').get
const unitString = values => values.map(value => String.fromCharCode(value)).join('')
const units = value => Array.from({length:value.length}, (_,i)=>value.charCodeAt(i))
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype), prototypeBefore = Object.getOwnPropertyDescriptors(RegExp.prototype)
const constructorBefore = Object.getOwnPropertyDescriptors(OriginalRegExp)
const results = packet.cases.map(input => {
  const label = unitString(input.label), name = unitString(input.name), body = unitString(input.body)
  const argument = unitString(input.input ?? [49,50])
  const prior = builtin.call(/^prior$/, 'prior')
  const match = [label, name, body]
  const caller = Object.create(null)
  Object.defineProperty(caller, 'kept', {value:'canary',writable:true,enumerable:true,configurable:true})
  const previous = /^[p-r]+$/
  Object.defineProperty(previous, 'lastIndex', {value:17,writable:false})
  const arrays = [prior,match], objects = [Object.prototype,RegExp.prototype,caller,previous]
  const oldArrays = arrays.map(value=>Object.getOwnPropertyDescriptors(value))
  const oldObjects = objects.map(value=>Object.getOwnPropertyDescriptors(value))
  const oldPrototypes = objects.map(Object.getPrototypeOf), oldExtensible = objects.map(Object.isExtensible)
  const previousSource = sourceGetter.call(previous), previousFlags = flagsGetter.call(previous)
  const constructor = input.calleeKind === 'number' ? 0 : input.calleeKind === 'undefined' ? undefined : OriginalRegExp
  let tuple, scope
  try { ({tuple,scope}=evaluate.call(caller,label,match,constructor,OriginalRegExp,'alternate-label','alternate-name','[A-Z]+')) }
  catch { return {ok:false} }
  assert(Array.isArray(tuple) && tuple.length===3 && !arrays.includes(tuple))
  assert.equal(Object.getPrototypeOf(tuple),Array.prototype)
  assert.deepEqual(Reflect.ownKeys(tuple).sort(),['0','1','2','length'].sort())
  for(const key of ['0','1','2']){
    const d=Object.getOwnPropertyDescriptor(tuple,key)
    assert(d && 'value' in d);assert.deepEqual([d.writable,d.enumerable,d.configurable],[true,true,true])
  }
  const tupleLength=Object.getOwnPropertyDescriptor(tuple,'length')
  assert.deepEqual(tupleLength,{value:3,writable:true,enumerable:false,configurable:false})
  const regex = tuple[2]
  // Closed normal fixtures retain the constructor in tuple slot2. Other
  // source shapes are separate admission/refusal controls, not observer guesses.
  assert.equal(Object.getPrototypeOf(regex),RegExp.prototype)
  assert.equal(regex.exec,builtin)
  arrays.push(tuple);objects.push(regex)
  const encode = value => {
    if(value===undefined)return {kind:'undefined'}
    if(value===null)return {kind:'null'}
    if(typeof value==='string')return {kind:'string',units:units(value)}
    if(typeof value==='number')return {kind:'number',value}
    if(typeof value==='boolean')return {kind:'bool',value}
    if(value===OriginalRegExp)return {kind:'function',ref:6}
    if(value===builtin)return {kind:'function',ref:5}
    if(arrays.includes(value))return {kind:'array',ref:arrays.indexOf(value)}
    if(objects.includes(value))return {kind:'object',ref:objects.indexOf(value)}
    throw new Error('Outside bounded observer value domain')
  }
  const descriptor = d => {
    assert(d && 'value' in d)
    return {kind:'data',value:encode(d.value),writable:d.writable,enumerable:d.enumerable,configurable:d.configurable}
  }
  const objectView = value => ({own:Object.getOwnPropertyNames(value).map(key=>({key:units(key),...descriptor(Object.getOwnPropertyDescriptor(value,key))})),
    prototype:Object.getPrototypeOf(value)===null?null:objects.indexOf(Object.getPrototypeOf(value)),extensible:Object.isExtensible(value)})
  const matchView = value => Object.fromEntries([['zero','0'],['length','length'],['index','index'],['input','input'],['groups','groups']].map(([name,key])=>[name,descriptor(Object.getOwnPropertyDescriptor(value,key))]))
  const actual = builtin.call(regex,argument)
  if(actual!==null){
    assert.equal(Object.getPrototypeOf(actual),Array.prototype)
    assert.deepEqual(Reflect.ownKeys(actual).sort(),['0','length','index','input','groups'].sort())
    arrays.push(actual)
  }
  for(let index=0;index<oldArrays.length;index++)assert.deepEqual(Object.getOwnPropertyDescriptors(arrays[index]),oldArrays[index])
  for(let index=0;index<oldObjects.length;index++){
    assert.deepEqual(Object.getOwnPropertyDescriptors(objects[index]),oldObjects[index])
    assert.equal(Object.getPrototypeOf(objects[index]),oldPrototypes[index]);assert.equal(Object.isExtensible(objects[index]),oldExtensible[index])
  }
  const brandsKept=sourceGetter.call(previous)===previousSource&&flagsGetter.call(previous)===previousFlags
  return {ok:true,returnedValue:encode(tuple),heap:arrays.map(value=>value.map(encode)),
    objects:[{intrinsic:'Object.prototype'},{intrinsic:'RegExp.prototype'},...objects.slice(2).map(objectView)],
    regexp:{ref:4,source:units(sourceGetter.call(regex)),flags:units(flagsGetter.call(regex)),execIsBuiltin:regex.exec===builtin},
    lookup:encode(actual),view:actual===null?null:matchView(actual),priorView:matchView(prior),
    scope,brandsKept,oldFrames:true}
})
assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype),rootBefore)
assert.deepEqual(Object.getOwnPropertyDescriptors(RegExp.prototype),prototypeBefore)
assert.deepEqual(Object.getOwnPropertyDescriptors(OriginalRegExp),constructorBefore)
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,plainJavaScript:true,typescriptErasure:false,
  sourceSha256:sha(original),executedSourceSha256:sha(expression),wrapperInputSha256:sha(wrapper),observerVerified:false,results,
  scope:'Finite selected46B expression and builtin-query observations; no enclosing branch/cache/labelmatch/node138/native allocation/frontend/engine adequacy or partial-error-state theorem.'}))
