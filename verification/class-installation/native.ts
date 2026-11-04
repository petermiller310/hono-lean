// Exact selected private elements, preamble, push and call entries in explicit class scaffolding.
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
const pushMeta = await Bun.file(new URL('../methods-push/source.json', import.meta.url)).json()
const pushSource = await Bun.file(new URL('../methods-push/source.ts.txt', import.meta.url)).text()
assert.equal(sha(pushSource), pushMeta.fragment.sha256)
assert.equal(bytes.subarray(pushMeta.fragment.startByte, pushMeta.fragment.endByteExclusive).toString('ascii'), pushSource)
const callMeta = await Bun.file(new URL('../private-call/source.json', import.meta.url)).json()
const calls: Record<string,string> = {}
for (const kind of ['four','five']) {
  calls[kind] = await Bun.file(new URL(`../private-call/call-${kind}.ts.txt`, import.meta.url)).text()
  assert.equal(sha(calls[kind]), callMeta.fragments[kind].sha256)
  assert.equal(bytes.subarray(callMeta.fragments[kind].startByte, callMeta.fragments[kind].endByteExclusive).toString('ascii'), calls[kind])
}
const packet = JSON.parse(await Bun.stdin.text())
const wrapper = `function makeModule(createNullObject, METHOD_NAME_ALL) { ${packet.preambleSource ?? fragments.preamble}
  function define() { class Holder<T> {
    ${packet.fieldsSource ?? fragments.fields}
    ${packet.methodSource ?? fragments.method}
    static inspect(value) { return [value.#methods, value.#children, value.#patterns, value.#pattern, value.#params, value.#pushHandlerSets] }
    stageParams(value) { this.#params = value }
    register(method, handler, events) { const curNode = this; const possibleKeys = new Set(events); ${pushSource} }
    consume(kind, target, method, params) {
      const handlerSets = [], node = this, nextNode = target, child = target;
      let returned;
      if (kind === 'four') { returned = ${calls.four.trim()} }
      else { returned = ${calls.five.trim()} }
      return { handlerSets, returned }
    }
  } return Holder }
  return { define, emptyParams, order: () => order }
}`
const emitted = new Bun.Transpiler({ loader: 'ts' }).transformSync(wrapper)
const makeModule = new Function(emitted + '\nreturn makeModule')()
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const { METHOD_NAME_ALL } = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const string = (units: number[]) => units.map(u => String.fromCharCode(u)).join('')
const units = (s: string) => Array.from({length:s.length}, (_,i) => s.charCodeAt(i))
const encode = (v: any) => v === undefined ? {kind:'undefined'} : v === null ? {kind:'null'} : typeof v === 'string' ? {kind:'string',units:units(v)} : typeof v === 'number' ? {kind:'number',value:v} : {kind:'bool',value:v}
const values: Record<string, unknown> = {u:undefined,n:null,f:false,z:0,empty:'',t:true,one:1,text:'x'}
const fill = (entries: any[]) => { const o=Object.create(null); for(const [key,code] of entries??[]) Object.defineProperty(o,string(key),{value:values[code],writable:true,enumerable:true,configurable:true}); return o }
const capture = (o: object) => Object.getOwnPropertyNames(o).sort((a,b)=>a<b?-1:a>b?1:0).map(key=>({key:units(key),value:encode((o as any)[key])}))
const encodePattern = (value: unknown, moduleEmpty: unknown) => value === undefined ? 'undefined' : value === null ? 'null' : value === moduleEmpty ? 'module' : typeof value
const results = (packet.cases ?? []).map((input: any) => {
  let helperCalls = 0
  const module = makeModule(() => { helperCalls++; return createNullObject() }, METHOD_NAME_ALL)
  const definitions: any[] = [], instances: any[] = [], snapshots: any[] = [], owners: number[] = []
  for (let i=0;i<(input.priorDefinitions??0);i++) module.define()
  for (const [classIndex, count] of input.counts.entries()) {
    const definition = module.define(); definitions.push(definition)
    for (let i = 0; i < count; i++) { const instance = new definition(); instances.push(instance); snapshots.push(definition.inspect(instance)); owners.push(classIndex) }
  }
  const methods = snapshots.map(values => values[0]), children = snapshots.map(values => values[1]), patterns = snapshots.map(values => values[2])
  const arraySet = new Set([...methods, ...patterns]), objectSet = new Set(children)
  const classBrandMatrix = definitions.map(definition => instances.map(instance => { try { definition.inspect(instance); return true } catch { return false } }))
  const unbrandedRejected = definitions.every(definition => { try { definition.inspect(Object.create(definition.prototype)); return false } catch { return true } })
  const observations = snapshots.map((values, at) => ({ methodsLength: values[0].length, patternsLength: values[2].length,
    childrenOwnCount: Reflect.ownKeys(values[1]).length, childrenNullPrototype: Object.getPrototypeOf(values[1]) === null,
    pattern: encodePattern(values[3], module.emptyParams), paramsIsModule: values[4] === module.emptyParams,
    methodsPatternsDistinct: values[0] !== values[2], publicOwnCount: Reflect.ownKeys(instances[at]).length,
    prototypeKept: Object.getPrototypeOf(instances[at]) === definitions[owners[at]].prototype, methodIsFunction: typeof values[5] === 'function' }))
  const initialHelperCalls = helperCalls, initialOrder = module.order()
  let query = null
  if (input.query) {
    const q=input.query, receiver=instances[q.receiver], target=instances[q.target]
    for(const r of q.registrations) target.register(string(r.method),r.handler,r.events.map(string))
    receiver.stageParams(fill(q.nodeEntries))
    const {handlerSets,returned} = receiver.consume(q.kind,target,string(q.method),fill(q.parameterEntries))
    query = { matches: handlerSets.map((r: any)=>({handler:r.handler,score:r.score,keys:r.possibleKeys.map(units),captures:capture(r.params)})),
      returned:encode(returned), order:module.order(), nullPrototypes:handlerSets.every((r:any)=>Object.getPrototypeOf(r.params)===null),
      methodValuesKept:snapshots.every((v,i)=>definitions[owners[i]].inspect(instances[i])[5]===v[5]) }
  }
  return { instances: observations, arraysIsolated: arraySet.size === 2 * instances.length,
    childrenIsolated: objectSet.size === instances.length && !objectSet.has(module.emptyParams),
    sharedParams: snapshots.every(values => values[4] === module.emptyParams),
    moduleNullPrototype: Object.getPrototypeOf(module.emptyParams) === null, helperCalls:initialHelperCalls, order:initialOrder,
    classBrandMatrix, methodSharedMatrix:snapshots.map(v=>snapshots.map(w=>v[5]===w[5])), unbrandedRejected, query }
})
let scope: unknown = null
if (packet.scopeProbes) {
  let fields=0
  class Returner { constructor(value:object) { return value } }
  class Stamp extends Returner {
    #field = (++fields, typeof this.#method)
    #method() { return 7 }
    static read(value:Stamp) { return [value.#field, value.#method()] }
  }
  const receiver = Object.preventExtensions({}); new Stamp(receiver)
  let duplicateThrows=false;try{new Stamp(receiver)}catch{duplicateThrows=true}
  const [methodSeenDuringField,result]=Stamp.read(receiver as Stamp)
  const readonlyRejected = new Function('class P { #m(){}; write(){ this.#m=1 } }; try {new P().write();return false}catch{return true}')()
  scope={methodSeenDuringField,result,duplicateThrows,fieldInitializers:fields,readonlyRejected}
}
process.stdout.write(JSON.stringify({ revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { verified: false, loader: 'ts', inputSha256: sha(wrapper), emittedSha256: sha(emitted) }, results, scope }) + '\n')
