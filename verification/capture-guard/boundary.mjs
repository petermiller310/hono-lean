// Native-only interpretation controls; these do not extend the proved domain.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
const runtime=typeof Bun==='undefined'?'node':'bun'
assert.equal(runtime==='bun'?Bun.version:process.versions.node,runtime==='bun'?'1.4.0':'22.22.2')
const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url)))
const raw=readFileSync(resolve(checkout,metadata.sourcePath))
assert.equal(raw.toString(),git('show',revision+':'+metadata.sourcePath))
const source=readFileSync(new URL('./full.ts.txt',import.meta.url),'utf8')
assert.equal(createHash('sha256').update(source).digest('hex'),metadata.fragments.full.sha256)
assert.equal(raw.subarray(metadata.fragments.full.startByte,metadata.fragments.full.endByteExclusive).toString(),source)
const selected=new Function('params','name','m','"use strict";\n'+source)
const withoutM=new Function('params','name','"use strict";\n'+source)
let getterCalls=0,matchReads=0
const own={};Object.defineProperty(own,'id',{get(){getterCalls++;throw new Error('must not read')}})
withoutM(own,'id')
selected(own,'id',new Proxy([],{get(){matchReads++;throw new Error('must not read')}}))
assert.equal(getterCalls,0);assert.equal(matchReads,0)
const inherited=Object.create({id:0});selected(inherited,'id',['capture'])
assert.equal(Object.hasOwn(inherited,'id'),true);assert.equal(inherited.id,'capture')
const proto=Object.freeze({}),oldPrototype=Object.getPrototypeOf(proto)
selected(proto,'__proto__',['capture'])
assert.equal(Object.hasOwn(proto,'__proto__'),false);assert.equal(Object.getPrototypeOf(proto),oldPrototype)
assert.throws(()=>selected(Object.freeze(Object.create(null)),'id',['capture']),TypeError)
const noSetter=Object.create(Object.defineProperty({},'id',{get(){throw new Error('getter must not run')}}))
assert.throws(()=>selected(noSetter,'id',['capture']),TypeError)
// Object/null setter arguments really mutate a prototype; the string-only
// absent-input contract does not claim this case.
const changed={};selected(changed,'__proto__',[null]);assert.equal(Object.getPrototypeOf(changed),null)
const replacement={},changedObject={};selected(changedObject,'__proto__',[replacement]);assert.equal(Object.getPrototypeOf(changedObject),replacement)
const events=[]
const facade={get hasOwn(){events.push('method');return Object.hasOwn}}
const key={ [Symbol.toPrimitive](){events.push('coerceKey');return 'id'} }
try {facade.hasOwn((events.push('first'),null),(events.push('second'),key))} catch(error){assert(error instanceof TypeError)}
assert.deepEqual(events,['method','first','second'])
assert.equal(Object.hasOwn('abc',0),true)
const longRoot={};let long=longRoot;for(let i=0;i<40;i++)long=Object.create(long)
selected(long,'id',['capture']);assert.equal(long.id,'capture')
console.log(JSON.stringify({verified:false,sourceBytes:Buffer.byteLength(source),
  ownSkip:{getterCalls,matchReads,noM:true},inheritedDataCreatedOwn:true,
  frozenLegacySetterNoOwn:true,frozenNullProtoRejected:true,missingSetterRejected:true,
  outsideDomain:{nullRhsChangesPrototype:true,objectRhsChangesPrototype:true,primitiveReceiverBoxing:true,longNativePrototypeChain:true},
  methodAndArgumentsBeforeNullConversion:events}))
