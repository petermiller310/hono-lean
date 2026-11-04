// Finite exact-source evidence; wrapper construction and TS erasure are unverified.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

const checkout = resolve(Bun.argv[2]), revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
const sha = (bytes: string | Buffer) => createHash('sha256').update(bytes).digest('hex')
assert.equal(Bun.version, '1.4.0')
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
const sourceBytes = Buffer.from(await Bun.file(resolve(checkout, 'src/router/trie-router/node.ts')).arrayBuffer())
async function fragment(folder: string, name?: string) {
  const metadata = await Bun.file(new URL(`../${folder}/source.json`, import.meta.url)).json()
  assert.equal(sha(sourceBytes), metadata.sourceSha256)
  const span = name ? metadata.fragments[name] : metadata.fragment
  const source = await Bun.file(new URL(`../${folder}/${name ?? 'source'}.ts.txt`, import.meta.url)).text()
  assert.equal(sha(source), span.sha256)
  assert.equal(sourceBytes.subarray(span.startByte, span.endByteExclusive).toString('ascii'), source)
  return source
}
const preamble = await fragment('class-installation', 'preamble')
const fields = await fragment('class-installation', 'fields')
const method = await fragment('class-installation', 'method')
const push = await fragment('methods-push')
const seed = await fragment('private-write', 'parameter')
const startup = await fragment('search-setup','startup')
const outer = await fragment('loop-entry','outer'), inner = await fragment('loop-entry','inner')
const iteration = await fragment('iteration-setup','iteration'), entry = await fragment('iteration-setup','entry')
const fullMetadata=await Bun.file(new URL('./source.json',import.meta.url)).json()
const full=await Bun.file(new URL('./full.ts.txt',import.meta.url)).text()
assert.equal(sha(full),fullMetadata.fragment.sha256)
assert.equal(sourceBytes.subarray(fullMetadata.fragment.startByte,fullMetadata.fragment.endByteExclusive).toString('ascii'),full)
assert.equal(startup+'\n'+outer+iteration+'\n'+inner+entry,full)
const packet = JSON.parse(await Bun.stdin.text())
const selectedStartup = packet.startupSource ?? startup, selectedEntry = packet.entrySource ?? entry
// The observation continuation returns after the full literal fragment. The
// omitted pattern body, updates and search completion are not substituted.
const wrapper = `function makeModule(createNullObject, METHOD_NAME_ALL, splitPath) { ${preamble}
  function define() { class Holder {
    ${fields}
    ${method}
    static params(owner) { return owner.#params }
    static method(owner) { return owner.#pushHandlerSets }
    static link(owner,key,value) { owner.#children[key] = value }
    static arrays(owner) { return [owner.#methods,owner.#patterns,...owner.#methods.flatMap(Object.values).map(r=>r.possibleKeys)] }
    seed(child,params) { __FIXED_SEED__(); }
    register(method,handler,events) { const curNode=this,possibleKeys=new Set(events); ${push} }
    first(method,path,observe) {
      ${selectedStartup}
      const finish = (step) => observe({handlerSets,curNodes,parts,curNodesQueue,len,partOffsets},step)
      ${outer}
        ${iteration}
        ${inner}
          __LITERAL_ENTRY__();
          return finish({i,j,len2,part,isLast,tempNodes,node,nextNode})
        }
      }
      return finish(null)
    }
  } return Holder }
  return {define,emptyParams,order:()=>order}
}`
let emitted = new Bun.Transpiler({loader:'ts'}).transformSync(wrapper)
assert.equal(emitted.split('__FIXED_SEED__();').length,2)
emitted = emitted.replace('__FIXED_SEED__();',seed)
assert.equal(emitted.split('__LITERAL_ENTRY__();').length,2)
emitted = emitted.replace('__LITERAL_ENTRY__();',selectedEntry)
const makeModule = new Function(emitted+'\nreturn makeModule')()
const {createNullObject} = await import(pathToFileURL(resolve(checkout,'src/router/utils.ts')).href)
const {METHOD_NAME_ALL} = await import(pathToFileURL(resolve(checkout,'src/router.ts')).href)
const {splitPath} = await import(pathToFileURL(resolve(checkout,'src/utils/url.ts')).href)
const string = (units:number[]) => units.map(u=>String.fromCharCode(u)).join('')
const units = (text:string) => Array.from({length:text.length},(_,i)=>text.charCodeAt(i))
const primitives:Record<string,any>={u:undefined,n:null,f:false,t:true,z:0,one:1,empty:'',text:'x'}
const encode=(value:any):any=>value===undefined?{kind:'undefined'}:value===null?{kind:'null'}:
  typeof value==='string'?{kind:'string',units:units(value)}:typeof value==='number'?{kind:'number',value}:{kind:'bool',value}
const fill=(entries:any[])=>{
  const object=Object.create(null)
  for(const [key,code] of entries??[]) Object.defineProperty(object,string(key),{
    value:primitives[code],writable:true,enumerable:true,configurable:true})
  return object
}
const capture=(object:any)=>Object.getOwnPropertyNames(object).sort((a,b)=>a<b?-1:a>b?1:0)
  .map(key=>({key:units(key),value:encode(object[key])}))
const results=(packet.cases??[]).map((input:any)=>{
  const module=makeModule(createNullObject,METHOD_NAME_ALL,splitPath),First=module.define(),Second=module.define()
  const root=new First(),parent=new First(),literal=new First(),wildcard=new First(),foreign=new Second()
  const owners={root,parent,literal,wildcard,foreign},branded=[root,parent,literal,wildcard]
  const paramsA=fill(input.entries),paramsB=fill(input.laterEntries)
  const values:Record<string,any>={...primitives,...owners,plain:Object.create(null)}
  const path=string(input.path??[47,108,105,116]),query=string(input.query??[71,69,84])
  const child=values[input.child??'literal'],star=values[input.wildcard??'u']
  // Ordinary fixture child maps use an independent first-field scan, never
  // the faulted startup's generated part. Node.insert remains unverified.
  if(path.length){let start=path[0]==='/'?1:0,end=start;while(end<path.length&&path[end]!=='/')end++
    First.link(root,path.slice(start,end),child)}
  if(branded.includes(child)) First.link(child,'*',star)
  const fixedSeed=First.prototype.seed
  for(const owner of branded) fixedSeed.call(root,owner,paramsA)
  for(const [target,registrations] of [[root,input.root??[]],[literal,input.literal??[]],[wildcard,input.star??[]]] as any[]){
    for(const r of registrations) First.prototype.register.call(target,string(r.method),r.handler,r.keys.map(string))
  }
  const oldArrays=[...branded.flatMap(owner=>First.arrays(owner)),...Second.arrays(foreign)],oldValues=oldArrays.map(a=>a.slice())
  const oldMethod=First.method(root),retained:any[]=[],retainedValues:any[][]=[],collectors:any[][]=[]
  let fresh=true,oldFrame=true,last:any,lastState:any
  const label=(value:any):any=>{
    for(const [name,owner] of Object.entries(owners)) if(value===owner) return {kind:name}
    return encode(value)
  }
  const observe=(state:any,step:any)=>{
    const arrays=[state.handlerSets,state.curNodes,state.parts,state.curNodesQueue,...(step?[step.tempNodes]:[])]
    fresh&&=arrays.every((array,at)=>Array.isArray(array)&&!oldArrays.includes(array)&&!retained.includes(array)&&arrays.indexOf(array)===at)
    oldFrame&&=oldArrays.every((array,at)=>array.length===oldValues[at].length&&array.every((v:any,i:number)=>v===oldValues[at][i]))
    oldFrame&&=retained.every((array,at)=>array.length===retainedValues[at].length&&array.every((v:any,i:number)=>v===retainedValues[at][i]))
    retained.push(...arrays);retainedValues.push(...arrays.map(array=>array.slice()));collectors.push(state.handlerSets)
    last=step;lastState=state
  }
  try{
    First.prototype.first.call(values[input.receiver??'root'],query,path,observe)
    if(input.repeat){fixedSeed.call(root,root,paramsB);First.prototype.first.call(values[input.receiver??'root'],query,path,observe)}
  }catch(error){if(!(error instanceof TypeError))throw error;return {ok:false}}
  const rows=collectors.flat(),paramsLabel=(v:any)=>v===module.emptyParams?'shared':v===paramsA?'A':v===paramsB?'B':'unknown'
  return {ok:true,entered:last!==null,next:label(last?.nextNode),node:label(last?.node),temp:last?last.tempNodes.map(label):[],
    setup:{parts:lastState.parts.map(units),len:lastState.len,part:encode(last?.part),isLast:last?.isLast??null,
      i:last?.i??null,j:last?.j??null,len2:last?.len2??null,offsetsNull:lastState.partOffsets===null,fresh,oldArraysKept:oldFrame},
    matches:rows.map(r=>({handler:r.handler,score:r.score,keys:r.possibleKeys.map(units),captures:capture(r.params)})),
    collectorSizes:collectors.map(c=>c.length),sameRecords:rows.map(a=>rows.map(b=>a===b)),sameParams:rows.map(a=>rows.map(b=>a.params===b.params)),
    params:Object.entries(owners).map(([name,owner])=>[name,paramsLabel((name==='foreign'?Second:First).params(owner))]),
    order:module.order(),methodKept:branded.every(owner=>First.method(owner)===oldMethod),
    nullPrototypes:rows.every(r=>Object.getPrototypeOf(r.params)===null)}
})
process.stdout.write(JSON.stringify({revision,runtime:Bun.version,checkedPinnedBlobs,
  transpilation:{verified:false,importedPinnedSplit:true,plainEntryInsertion:true,
    contiguousSourceBytes:Buffer.byteLength(full),sourceOverrides:['startupSource','entrySource'].filter(key=>packet[key]!==undefined),
    inputSha256:sha(wrapper+'\0'+JSON.stringify({seed,entry:selectedEntry})),emittedSha256:sha(emitted),
    continuation:'observation after first literal fragment; remaining source body omitted'},results})+'\n')
