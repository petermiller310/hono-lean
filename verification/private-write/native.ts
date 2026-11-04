// Exact private assignments in explicit source-bound class scaffolding.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const checkout = resolve(Bun.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args], { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
const sha = (bytes: string | Buffer) => createHash('sha256').update(bytes).digest('hex')
assert.equal(Bun.version, '1.4.0'); assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob); checkedPinnedBlobs++
}
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const bytes = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
assert.equal(sha(bytes), metadata.sourceSha256)
const fragments: Record<string, string> = {}
for (const [name, entry] of Object.entries<any>(metadata.fragments)) {
  const source = await Bun.file(new URL(`./${name}.ts.txt`, import.meta.url)).text()
  assert.equal(sha(source), entry.sha256)
  assert.equal(bytes.subarray(entry.startByte, entry.endByteExclusive).toString('ascii'), source)
  fragments[name] = source
}
const classMeta = await Bun.file(new URL('../class-installation/source.json', import.meta.url)).json()
const classSource: Record<string,string> = {}
for (const name of ['preamble','fields','method']) {
  const text=await Bun.file(new URL(`../class-installation/${name}.ts.txt`,import.meta.url)).text(),span=classMeta.fragments[name]
  assert.equal(sha(text),span.sha256)
  assert.equal(bytes.subarray(span.startByte,span.endByteExclusive).toString('ascii'),text)
  classSource[name]=text
}
const packet=JSON.parse(await Bun.stdin.text())
const sources=Object.fromEntries(Object.entries(fragments).map(([name,text])=>[name,packet[`${name}Source`]??text]))
const wrapper=`function makeModule(createNullObject,METHOD_NAME_ALL) { ${classSource.preamble}
 function define(){ class Holder {
  ${classSource.fields}
  ${classSource.method}
  static read(owner){return owner.#params}
  static method(owner){return owner.#pushHandlerSets}
  seed(child,params){return __PRIVATE_WRITE_SEED__();}
  perform(kind,nextNode,node,child,params){
    switch(kind){
      case 'reset':return __PRIVATE_WRITE_RESET__();
      case 'propagation':return __PRIVATE_WRITE_PROPAGATION__();
      case 'wildcard':return __PRIVATE_WRITE_WILDCARD__();
      case 'parameter':return __PRIVATE_WRITE_PARAMETER__();
    }
  }
 } return Holder }
 return {define,emptyParams}
}`
// Erase only the typed class scaffolding, then insert the checked plain-JS
// assignments verbatim. This avoids a TS transpiler statically rejecting the
// deliberately faulted method-write control before native PrivateSet runs.
let emitted=new Bun.Transpiler({loader:'ts'}).transformSync(wrapper)
for(const name of ['reset','propagation','wildcard','parameter']){
  const marker=`__PRIVATE_WRITE_${name.toUpperCase()}__()`
  assert.equal(emitted.split(marker).length,2)
  emitted=emitted.replace(marker,`(${sources[name].trim()})`)
}
assert.equal(emitted.split('__PRIVATE_WRITE_SEED__()').length,2)
emitted=emitted.replace('__PRIVATE_WRITE_SEED__()',`(${fragments.parameter.trim()})`)
const makeModule=new Function(emitted+'\nreturn makeModule')()
const {createNullObject}=await import(pathToFileURL(resolve(checkout,'src/router/utils.ts')).href)
const {METHOD_NAME_ALL}=await import(pathToFileURL(resolve(checkout,'src/router.ts')).href)
const units=(text:string)=>Array.from({length:text.length},(_,i)=>text.charCodeAt(i))
const results=(packet.cases??[]).map((input:any)=>{
  const module=makeModule(createNullObject,METHOD_NAME_ALL),First=module.define(),Second=module.define()
  const parent=new First(),child=new First(),foreign=new Second()
  const objectA=Object.create(null),objectB=Object.create(null),array:any[]=[],fn=()=>7,plain=Object.create(null)
  const clone=Object.create(First.prototype),proxy=new Proxy(parent,{})
  const method=First.method(parent)
  const code:Record<string,any>={u:undefined,n:null,f:false,z:0,empty:'',one:1,text:'x',unicode:String.fromCharCode(55296,233),objectA,objectB,array,fn,method,
    parent,child,foreign,plain,clone,proxy,shared:module.emptyParams}
  const owners=[parent,child,foreign],defs=[First,First,Second],perform=First.prototype.perform
  First.prototype.seed.call(parent,parent,code[input.a??'u'])
  First.prototype.seed.call(parent,child,code[input.b??'n'])
  const before=owners.map((o,i)=>defs[i].read(o))
  let setterCalls=0
  for(const owner of [parent,child]){
    Object.defineProperty(owner,'params',{get(){return 'public'},set(){setterCalls++},enumerable:true,configurable:true})
    if(input.frozen)Object.freeze(owner)
  }
  const encode=(value:any):any=>{
    for(const name of ['shared','objectA','objectB','array','fn','method','parent','child','foreign','plain','clone','proxy'])if(value===code[name])return {kind:name}
    if(value===undefined)return {kind:'undefined'}
    if(value===null)return {kind:'null'}
    if(typeof value==='string')return {kind:'string',units:units(value)}
    if(typeof value==='number')return {kind:'number',value}
    if(typeof value==='boolean')return {kind:'bool',value}
    throw new Error('Unknown observation')
  }
  const select=(name:string)=>name==='null'?null:name==='undefined'?undefined:name==='zero'?0:code[name]
  const target=select(input.target??'child'),source=select(input.source??'parent')
  let returned:any
  try{
    returned=perform.call(target,input.op??'propagation',target,source,target,code[input.rhs??'one'])
  }catch(error){if(!(error instanceof TypeError))throw error;return {ok:false}}
  const after=owners.map((o,i)=>defs[i].read(o))
  return {ok:true,returned:encode(returned),before:before.map(encode),after:after.map(encode),setterCalls,
    methodKept:First.method(parent)===method&&First.method(child)===method,
    publicUnchanged:owners.slice(0,2).every(o=>Object.getOwnPropertyDescriptor(o,'params')?.get?.call(o)==='public'),
    frozenKept:owners.slice(0,2).every(o=>Object.isExtensible(o)===!input.frozen)}
})
process.stdout.write(JSON.stringify({revision,runtime:Bun.version,checkedPinnedBlobs,
 transpilation:{verified:false,loader:'ts',plainAssignmentInsertion:true,inputSha256:sha(wrapper+'\0'+JSON.stringify({seed:fragments.parameter,sources})),emittedSha256:sha(emitted)},results})+'\n')
