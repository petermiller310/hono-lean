// Exact pinned fragments in an unverified TS-erased fixture wrapper.
// Finite evidence only: native engines, erasure, transport and observer are outside the proof.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { createRequire } from 'node:module'
import { resolve } from 'node:path'
const checkout=resolve(process.argv[2]), revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime=typeof Bun==='undefined'?'node':'bun', version=runtime==='bun'?Bun.version:process.versions.node
assert.equal(version,runtime==='bun'?'1.4.0':'22.22.2')
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
const sha=bytes=>createHash('sha256').update(bytes).digest('hex')
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)){
  const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
const load=(folder,name,file)=>{
 const meta=JSON.parse(readFileSync(new URL(`../${folder}/source.json`,import.meta.url)))
 const span=meta.fragments[name],bytes=readFileSync(resolve(checkout,meta.sourcePath)),text=readFileSync(new URL(`../${folder}/${file}`,import.meta.url),'utf8')
 assert.equal(meta.revision,revision);assert.equal(sha(bytes),meta.sourceSha256);assert.equal(sha(text),span.sha256)
 assert.equal(bytes.subarray(span.startByte,span.endByteExclusive).toString('ascii'),text);return text
}
const original={source:load('capture-collect','full','full.ts.txt'),init:load('params-init','full','full.ts.txt'),method:load('private-call','method','method.ts.txt')}
const packet=JSON.parse(readFileSync(0,'utf8'))
const source=packet.source??original.source,initializer=packet.initSource??original.init,methodSource=packet.methodSource??original.method
const ts=createRequire(import.meta.url)(process.env.HONO_TYPESCRIPT??'typescript')
assert.equal(ts.version,'6.0.3')
const wrappers=new Map(),transpilation=[]
const buildFor=missing=>{
 if(wrappers.has(missing))return wrappers.get(missing)
 const wrapper=`function build(createNullObject, METHOD_NAME_ALL) { class Holder {
 #methods; #params;
 constructor(methods, params) { this.#methods = methods; this.#params = params }
 ${methodSource}
 consume(node, child, handlerSets, method, emptyParams, name, matchValue) {
 const i='outer-i', len='outer-len', handlerSet='outer-handler', key='outer-key';
 ${missing?'':'const m=matchValue;'}
 ${initializer}
 ${source}
 return {params,scope:[i,len,handlerSet,key]};
 }
 rows(){return this.#methods}
 parameters(){return this.#params}
 } return Holder }`
 const emitted=ts.transpileModule(wrapper,{compilerOptions:{target:ts.ScriptTarget.ES2022,module:ts.ModuleKind.None}}).outputText
 transpilation.push({inputSha256:sha(wrapper),emittedSha256:sha(emitted)})
 const build=new Function(emitted+'\nreturn build')();wrappers.set(missing,build);return build
}
assert.equal(Object.hasOwn(globalThis,'m'),false)
const string=us=>us.map(u=>String.fromCharCode(u)).join(''), units=s=>Array.from({length:s.length},(_,i)=>s.charCodeAt(i))
const rootDescriptors=Object.getOwnPropertyDescriptors(Object.prototype)
const results=(packet.cases??[]).map(input=>{
 const objects=[Object.prototype,Object.create(null),Object.create(null),Object.create(null)]
 const records=input.records.map((keys,index)=>({handler:index,possibleKeys:keys.map(string),score:100+index,params:objects[3]}))
 objects.push(...records)
 const decode=code=>code.startsWith('r')?records[Number(code.slice(1))]:({u:undefined,n:null,f:false,z:0,empty:'',t:true,one:1,text:'x',ctor:Object})[code]
 const define=(o,k,v)=>Object.defineProperty(o,string(k),{value:decode(v),writable:true,enumerable:true,configurable:true})
 const fill=(o,fields)=>{for(const[k,v]of fields??[])define(o,k,v);return o}
 fill(objects[3],input.inheritedNode);Object.defineProperty(objects[3],'marker',{value:'prior',writable:true,enumerable:true,configurable:true})
 const parentProto=input.ordinaryParent?Object.prototype:input.inheritedNode?.length?objects[3]:null
 for(const index of[1,2]){if(index===1||input.shared){Object.setPrototypeOf(objects[index],parentProto);fill(objects[index],input.nodeEntries)}}
 const snapshots=[],prototypes=[]
 const methods=input.rows.map(row=>{
   const proto=fill(Object.create(null),row.inherited),object=fill(Object.create(row.nullPrototype?null:proto),row.own)
   objects.push(proto,object);prototypes.push(proto);snapshots.push(Object.getOwnPropertyDescriptors(object));return object
 })
 const oldFrames=objects.slice(0,4).map(o=>({own:Object.getOwnPropertyDescriptors(o),proto:Object.getPrototypeOf(o),extensible:Object.isExtensible(o)}))
 const rowProtos=methods.map(Object.getPrototypeOf),protoFrames=prototypes.map(Object.getOwnPropertyDescriptors)
 const allocations=[]
 const trackedCreate=()=>{const o=Object.create(null);allocations.push(o);return o}
 const Holder=buildFor(!!input.missingMatch)(trackedCreate,'ALL')
 const child=new Holder(methods,undefined),parent=new Holder([],objects[input.shared?2:1]),root=new Holder([],undefined)
 objects.push(child,parent,root)
 const prefix=[...Array(input.priorCount??0).fill(objects[3]),...(input.priorRecords??[]).map(i=>records[i])],collector=prefix.slice(),keysBefore=records.map(r=>r.possibleKeys.slice())
 const keyRefs=records.map(r=>r.possibleKeys)
 const output=root.consume(parent,child,collector,string(input.method),objects[2],string(input.name),[decode(input.capture??'text')])
 const allocated=[output.params,...allocations];objects.push(...allocated)
 const encode=v=>{
   if(v===undefined)return{kind:'undefined'};if(v===null)return{kind:'null'};if(v===Object)return{kind:'constructor'}
   if(typeof v==='boolean')return{kind:'bool',value:v};if(typeof v==='number')return{kind:'number',value:v}
   if(typeof v==='string')return{kind:'string',units:units(v)}
   if(objects.includes(v))return{kind:'object',ref:objects.indexOf(v)}
   throw new Error('Unregistered native observed value: '+typeof v)
 }
 const entries=o=>Object.getOwnPropertyNames(o).map(k=>{const d=Object.getOwnPropertyDescriptor(o,k);assert('value'in d);return{key:units(k),value:encode(d.value),writable:d.writable,enumerable:d.enumerable,configurable:d.configurable}})
 const unchanged=(o,before)=>{const after=Object.getOwnPropertyDescriptors(o);try{assert.deepEqual(after,before);return true}catch{return false}}
 const recordParams=records.map(r=>allocated.indexOf(r.params)),source=objects[input.shared?2:1]
 return{freshParams:encode(output.params),collector:collector.map(r=>r===objects[3]?-1:records.indexOf(r)),recordParams,
 collectorParams:collector.map(r=>r===objects[3]?-1:allocated.indexOf(r.params)),allocations:allocated.map(entries),
 freshOrdinary:Object.getPrototypeOf(output.params)===Object.prototype&&Object.isExtensible(output.params),
 nullPrototypes:allocations.every(o=>Object.getPrototypeOf(o)===null),
 methodsKept:child.rows()===methods&&parent.parameters()===source&&methods.every((o,i)=>unchanged(o,snapshots[i])&&Object.getPrototypeOf(o)===rowProtos[i]&&unchanged(prototypes[i],protoFrames[i]))&&oldFrames.every((f,i)=>unchanged(objects[i],f.own)&&Object.getPrototypeOf(objects[i])===f.proto&&Object.isExtensible(objects[i])===f.extensible)&&unchanged(Object.prototype,rootDescriptors),
 keysKept:records.every((r,i)=>r.possibleKeys===keyRefs[i]&&Object.getOwnPropertyDescriptor(r,"possibleKeys").writable&&Object.getOwnPropertyDescriptor(r,"possibleKeys").enumerable&&Object.getOwnPropertyDescriptor(r,"possibleKeys").configurable&&r.possibleKeys.length===keysBefore[i].length&&r.possibleKeys.every((k,j)=>k===keysBefore[i][j])),
 handlerFieldsKept:records.every((r,i)=>r.handler===i&&r.score===100+i),scope:output.scope}
})
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,transpilation:{verified:false,compiler:ts.version,wrappers:transpilation},
 observation:'Ordinary data fixtures; O0 is real Object.prototype, represented reads are constructor and __proto__ only unless overridden; wrapper and TS erasure unverified.',results}))
