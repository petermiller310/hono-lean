// Native-only constructor/coercion/evaluation-order boundaries, not formal adequacy.
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
const OriginalRegExp = RegExp, builtin = RegExp.prototype.exec
const sourceGetter = Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const rootBefore = Object.getOwnPropertyDescriptors(Object.prototype), protoBefore = Object.getOwnPropertyDescriptors(RegExp.prototype)
const ordering = new Function('OriginalRegExp', `
const events=[]; let RegExp=OriginalRegExp; const label='label',match=[];
function First(source){events.push('First');return new OriginalRegExp(source)}
function Second(source){events.push('Second');return new OriginalRegExp(source)}
Object.defineProperty(match,'1',{get(){events.push('name');RegExp=First;return 'id'}});
Object.defineProperty(match,'2',{get(){events.push('body');RegExp=Second;return {toString(){events.push('string');return '[0-9]+'}}}});
const tuple=(${original});return {tuple,events};`)(OriginalRegExp)
assert.deepEqual(ordering.events,['name','body','string','First'])
assert.equal(sourceGetter.call(ordering.tuple[2]),'^[0-9]+$')
const argumentFirst = new Function('OriginalRegExp', `
const events=[],label='label';const RegExp=0,match=[];
Object.defineProperty(match,'1',{get(){events.push('name');return 'id'}});
Object.defineProperty(match,'2',{get(){events.push('body');throw new Error('argument-before-constructor-check')}});
try { const tuple=(${original}); throw new Error('unexpected success') }
catch(error){return {events,message:error.message}};`)(OriginalRegExp)
assert.deepEqual(argumentFirst,{events:['name','body'],message:'argument-before-constructor-check'})
const tdz = new Function('OriginalRegExp', `
const events=[],label='label',match=[];
Object.defineProperty(match,'1',{get(){events.push('name');return 'id'}});
Object.defineProperty(match,'2',{get(){events.push('body');return '[0-9]+'}});
try {const tuple=(${original});let RegExp;return {unexpected:true}}
catch(error){return {events,referenceError:error instanceof ReferenceError}};`)(OriginalRegExp)
assert.deepEqual(tdz,{events:['name'],referenceError:true})
const invoke = new Function('label','match','RegExp',`"use strict";return (${original})`)
const value = {toString(){return '[0-9]+'}}
assert.equal(sourceGetter.call(invoke('label',['label','id',value],OriginalRegExp)[2]),'^[0-9]+$')
assert.throws(()=>invoke('label',['label','id',Symbol('body')],OriginalRegExp),TypeError)
for(const [body,source]of[[42,'^42$'],[null,'^null$'],[undefined,'^undefined$']])
  assert.equal(sourceGetter.call(invoke('label',['label','id',body],OriginalRegExp)[2]),source)
const broader=invoke('label',['label','id','[0-9]*'],OriginalRegExp)[2]
assert.equal(builtin.call(broader,'')[0],'')
assert.throws(()=>invoke('label',['label','id','[9-0]+'],OriginalRegExp),SyntaxError)
const noNew=original.replace('new RegExp','RegExp')
const called=new Function('label','match','RegExp',`return (${noNew})`)('label',['label','id','[0-9]+'],OriginalRegExp)
assert.equal(sourceGetter.call(called[2]),'^[0-9]+$')
function Custom(pattern){this.seen=pattern}
const custom=invoke('label',['label','id','[0-9]+'],Custom)[2]
assert.equal(custom.seen,'^[0-9]+$');assert.equal(Object.getPrototypeOf(custom),Custom.prototype)
assert.throws(()=>builtin.call(custom,'12'),TypeError)
const bound=invoke('label',['label','id','[0-9]+'],OriginalRegExp.bind(null))[2]
assert.equal(sourceGetter.call(bound),'^[0-9]+$')
assert.throws(()=>invoke('label',['label','id','[0-9]+'],()=>{}),TypeError)
const hooks=[]
const literal=new Function('label','match','RegExp','Array',`return (${original})`)(
  'label',['label','id','[0-9]+'],OriginalRegExp,function Array(){hooks.push('Array');throw new Error('not used')})
assert(Array.isArray(literal));assert.deepEqual(hooks,[])
const d=Object.getOwnPropertyDescriptor(literal[2],'lastIndex')
assert.deepEqual(d,{value:0,writable:true,enumerable:false,configurable:false})
assert.deepEqual(Object.getOwnPropertyDescriptors(Object.prototype),rootBefore)
assert.deepEqual(Object.getOwnPropertyDescriptors(RegExp.prototype),protoBefore)
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,nativeOnly:true,plainJavaScript:true,typescriptErasure:false,
  sourceBytes:Buffer.byteLength(original),sourceSha256:sha(original),
  boundaries:{savedConstructorOrder:ordering.events,argumentBeforeNonconstructor:argumentFirst,tdzBeforeBody:tdz,
    objectTemplateCoercionSucceeds:true,symbolTemplateThrows:true,numericNullUndefinedTemplateCoercionSucceeds:true,
    validWiderGrammarSucceeds:true,reversedRangeSyntaxError:true,callWithoutNewSucceeds:true,
    customConstructorSucceedsWithoutRegExpBrand:true,boundBuiltinConstructorSucceeds:true,arrowNotConstructorThrows:true,
    arrayBindingHooks:hooks,lastIndexDescriptor:d},
  scope:'Native-only effectful getters/coercions/TDZ/custom-bound-constructor and wider grammar. No model errorclass/partialstate/literal hidden allocation/native frontend adequacy claim.'}))
