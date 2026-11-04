// Native-only scope controls; getter/proxy/symbol successes are not model
// rejection claims. The actual81B initializer remains unchanged in the wrapper.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
const runtime=typeof Bun==='undefined'?'node':'bun'
assert.equal(runtime==='bun'?Bun.version:process.versions.node,runtime==='bun'?'1.4.0':'22.22.2')
const checkout=resolve(process.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision);assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
const metadata=JSON.parse(readFileSync(new URL('./source.json',import.meta.url))),span=metadata.fragments.full
const raw=readFileSync(resolve(checkout,metadata.sourcePath)),source=readFileSync(new URL('./full.ts.txt',import.meta.url),'utf8')
assert.equal(raw.toString(),git('show',revision+':'+metadata.sourcePath))
assert.equal(createHash('sha256').update(source).digest('hex'),span.sha256)
assert.equal(raw.subarray(span.startByte,span.endByteExclusive).toString(),source)
const C=new Function(`return class Fragment {
  #params;
  constructor(value){this.#params=value}
  run(node,emptyParams){
${source}
    return params
  }
}`)()
const select=(value,empty)=>{const node=new C(value);return node.run(node,empty)}
let getterCalls=0
const shared=Object.defineProperty({},'bad',{enumerable:true,get(){getterCalls++;throw new Error('must skip')}})
const first=select(shared,shared),second=select(shared,shared)
assert.notEqual(first,second);assert.notEqual(first,shared);assert.deepEqual(Reflect.ownKeys(first),[]);assert.equal(getterCalls,0)
const inherited=Object.create(Object.defineProperty({},'inherited',{enumerable:true,get(){throw new Error('not own')}}))
Object.defineProperty(inherited,'hidden',{enumerable:false,get(){throw new Error('not enumerable')}})
assert.deepEqual(Reflect.ownKeys(select(inherited,shared)),[])
const value=[],readonly=Object.freeze(Object.defineProperty({},'id',{value,writable:false,enumerable:true,configurable:false}))
const copied=select(readonly,shared),descriptor=Object.getOwnPropertyDescriptor(copied,'id')
assert.equal(copied.id,value);assert.deepEqual([descriptor.writable,descriptor.enumerable,descriptor.configurable],[true,true,true])
const protoObject={marker:'object'}
for(const value of [protoObject,null,'string']) {
  const input=Object.create(null);Object.defineProperty(input,'__proto__',{value,enumerable:true})
  const result=select(input,shared)
  assert.equal(Object.hasOwn(result,'__proto__'),true);assert.equal(result.__proto__,value)
  assert.equal(Object.getPrototypeOf(result),Object.prototype)
  const assigned=Object.assign({},input)
  assert.equal(Object.hasOwn(assigned,'__proto__'),false)
  assert.equal(Object.getPrototypeOf(assigned),typeof value==='string'?Object.prototype:value)
}
const self={};self.self=self;self.array=value
const shallow=select(self,shared);assert.equal(shallow.self,self);assert.equal(shallow.array,value)
assert.deepEqual(Reflect.ownKeys(select(Object.prototype,shared)),[])
// These valid native cases require fuller getter/proxy/symbol semantics.
const changing={get a(){delete changing.b;return 'A'},b:'B'}
assert.deepEqual(select(changing,shared),{a:'A'})
const missing=Object.defineProperty({},'id',{enumerable:true,get:undefined})
assert.equal(Object.hasOwn(select(missing,shared),'id'),true)
assert.equal(select(missing,shared).id,undefined)
const legacyGetter=Object.create(null);Object.defineProperty(legacyGetter,'id',{
  enumerable:true,get:Object.getOwnPropertyDescriptor(Object.prototype,'__proto__').get})
assert.equal(select(legacyGetter,shared).id,null)
const symbol=Symbol('copy');const symbols=select({[symbol]:'symbol'},shared);assert.equal(symbols[symbol],'symbol')
const events=[]
const proxy=new Proxy({id:'value'},{ownKeys(target){events.push('keys');return Reflect.ownKeys(target)},
  getOwnPropertyDescriptor(target,key){events.push('descriptor:'+key);return Reflect.getOwnPropertyDescriptor(target,key)},
  get(target,key){events.push('get:'+key);return Reflect.get(target,key)}})
assert.equal(select(proxy,shared).id,'value');assert.deepEqual(events,['keys','descriptor:id','get:id'])
assert.deepEqual(select(null,shared),{})
console.log(JSON.stringify({verified:false,sourceBytes:Buffer.byteLength(source),sharedSkippedGetter:getterCalls===0,
  freshBothCalls:true,hiddenInheritedSkipped:true,readonlyCopiedWEC:true,protoDefinedNotSet:true,shallowAliases:true,
  intrinsicRootEmptyCopy:true,outsideDomain:{getterCanSucceedAndMutate:true,missingGetterReturnsUndefined:true,
    legacyGetterCanSucceed:true,symbolCopied:true,proxyEvents:events},nullishSpreadEmpty:true}))
