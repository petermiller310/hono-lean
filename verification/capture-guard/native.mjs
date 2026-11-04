// Finite exact-source evidence. The wrapper, fixture transport and native
// engines are unverified; object observations compare descriptors extensionally.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab+1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath))
assert.equal(metadata.revision, revision); assert.equal(sha(raw), metadata.sourceSha256)
const fragments = Object.fromEntries(Object.entries(metadata.fragments).map(([name, span]) => {
  const text = readFileSync(new URL(`./${name}.ts.txt`, import.meta.url), 'utf8')
  assert.equal(sha(text), span.sha256)
  assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString('ascii'), text)
  return [name, text]
}))
assert.equal(fragments.guard+fragments.assignment+fragments.close, fragments.full)
const packet = JSON.parse(readFileSync(0, 'utf8')), source = packet.source ?? fragments.full
assert.equal(Object.hasOwn(globalThis,'m'),false,'Missing-m fixture requires no ambient m')
const string = units => units.map(unit => String.fromCharCode(unit)).join('')
const units = text => Array.from({length:text.length}, (_,i) => text.charCodeAt(i))
const legacy = Object.getOwnPropertyDescriptor(Object.prototype, '__proto__')
const results = (packet.cases ?? []).map(input => {
  const arrays = input.heap.map(() => []), objects = input.objects.map(() => Object.create(null))
  const decode = value => {
    switch (value.kind) {
      case 'undefined': return undefined
      case 'null': return null
      case 'bool': case 'number': return value.value
      case 'string': return string(value.units)
      case 'array': assert(value.ref < arrays.length); return arrays[value.ref]
      case 'object': assert(value.ref < objects.length); return objects[value.ref]
      case 'constructor': return Object
      default: throw new Error('Unsupported fixture value')
    }
  }
  const encode = value => {
    if (value === undefined) return {kind:'undefined'}
    if (value === null) return {kind:'null'}
    if (value === Object) return {kind:'constructor'}
    if (typeof value === 'boolean') return {kind:'bool',value}
    if (typeof value === 'number') return {kind:'number',value}
    if (typeof value === 'string') return {kind:'string',units:units(value)}
    if (arrays.includes(value)) return {kind:'array',ref:arrays.indexOf(value)}
    if (objects.includes(value)) return {kind:'object',ref:objects.indexOf(value)}
    throw new Error('Unregistered native value')
  }
  let getterCalls = 0, setterCalls = 0
  const badGetter = () => {getterCalls++;throw new TypeError('fixture getter')}
  const badSetter = () => {setterCalls++;throw new TypeError('fixture setter')}
  const getter = name => name === 'missing' ? undefined : name === 'prototype' ? legacy.get : badGetter
  const setter = name => name === 'missing' ? undefined : name === 'prototype' ? legacy.set : badSetter
  input.heap.forEach((row,i) => row.forEach((value,j) => {arrays[i][j]=decode(value)}))
  input.objects.forEach((object,i) => {
    for (const descriptor of object.own) {
      const common = {enumerable:descriptor.enumerable,configurable:descriptor.configurable}
      Object.defineProperty(objects[i],string(descriptor.key), descriptor.kind === 'data'
        ? {...common,value:decode(descriptor.value),writable:descriptor.writable}
        : {...common,get:getter(descriptor.getter),set:setter(descriptor.setter)})
    }
  })
  input.objects.forEach((object,i) => Object.setPrototypeOf(objects[i], object.prototype === null ? null : objects[object.prototype]))
  input.objects.forEach((object,i) => {if (!object.extensible) Object.preventExtensions(objects[i])})
  const supplied = {params:objects[input.params],name:string(input.name)}
  if (Object.hasOwn(input,'m')) supplied.m=decode(input.m)
  if (Object.hasOwn(input,'objectBinding')) supplied.Object=decode(input.objectBinding)
  const provided = ['m','Object'].filter(name => Object.hasOwn(supplied,name))
  const wrapper = `"use strict"; return function selected(supplied, canary) {
    const params = supplied.params, name = supplied.name;
    ${provided.map(name => `const ${name} = supplied.${name};`).join('\n')}
    const offset = canary, p = canary, restPathString = canary;
${source}
    return {scope:params===supplied.params && name===supplied.name && offset===canary && p===canary && restPathString===canary};
  }`
  const selected = new Function(wrapper)()
  try {
    const output = selected(supplied,Symbol('outer locals'))
    const snapshot = objects.map(object => ({prototype:Object.getPrototypeOf(object)===null ? null : objects.indexOf(Object.getPrototypeOf(object)),
      extensible:Object.isExtensible(object),own:Reflect.ownKeys(object).map(key => {
        assert.equal(typeof key,'string'); const descriptor=Object.getOwnPropertyDescriptor(object,key)
        const common={key:units(key),enumerable:descriptor.enumerable,configurable:descriptor.configurable}
        if ('value' in descriptor) return {...common,kind:'data',value:encode(descriptor.value),writable:descriptor.writable}
        return {...common,kind:'accessor',getter:descriptor.get===undefined?'missing':descriptor.get===legacy.get?'prototype':'unsupported',
          setter:descriptor.set===undefined?'missing':descriptor.set===legacy.set?'prototype':'unsupported'}
      })}))
    return {ok:true,objects:snapshot,heap:arrays.map(row=>row.map(encode)),scope:output.scope,
      getterCalls,setterCalls,wrapperSha256:sha(wrapper)}
  } catch (error) {
    if (!(error instanceof TypeError || error instanceof ReferenceError || error instanceof RangeError)) throw error
    return {ok:false}
  }
})
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,fragmentTypeErasure:false,
  sourceBytes:Buffer.byteLength(source),observation:'Own descriptors and prototype references, compared extensionally; no getter observations invented; failure is rejection only.',results}))
