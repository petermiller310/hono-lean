// Finite evidence from pinned source. Wrapper/TypeScript erasure are unverified.
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
async function fragment(folder: string, name?: string) {
  const metadata = await Bun.file(new URL(`../${folder}/source.json`, import.meta.url)).json()
  const raw = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
  assert.equal(sha(raw), metadata.sourceSha256)
  const span = name ? metadata.fragments[name] : metadata.fragment
  const text = await Bun.file(new URL(`../${folder}/${name ?? 'source'}.ts.txt`, import.meta.url)).text()
  assert.equal(sha(text), span.sha256)
  assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString('ascii'), text)
  return text
}
const preamble = await fragment('class-installation', 'preamble')
const fields = await fragment('class-installation', 'fields')
const method = await fragment('class-installation', 'method')
const push = await fragment('methods-push')
const seed = await fragment('private-write', 'parameter')
const startup = await fragment('search-setup', 'startup')
const iteration = await fragment('iteration-setup', 'iteration')
const entry = await fragment('iteration-setup', 'entry')
const firstNode = entry.slice(0, entry.indexOf('\n') + 1)
const originalOuter = await fragment('loop-entry', 'outer')
const originalInner = await fragment('loop-entry', 'inner')
const packet = JSON.parse(await Bun.stdin.text())
const outer = packet.outerSource ?? originalOuter, inner = packet.innerSource ?? originalInner
// Headers are inserted unchanged. The bodies below are observation
// continuations, not the omitted Hono suffix or a whole-search implementation.
const wrapper = `function makeModule(createNullObject, METHOD_NAME_ALL, splitPath) { ${preamble}
  function define() { class Holder {
    ${fields}
    ${method}
    static params(owner) { return owner.#params }
    static method(owner) { return owner.#pushHandlerSets }
    static arrays(owner) { return [owner.#methods, owner.#patterns, ...owner.#methods.flatMap(Object.values).map(r => r.possibleKeys)] }
    seed(child, params) { __FIXED_SEED__(); }
    register(method, handler, events) {
      const curNode = this, possibleKeys = new Set(events); ${push}
    }
    prefix(method, path, observe) {
      ${startup}
      const finish = (outer, inner) => observe({handlerSets, curNode, curNodes, parts, curNodesQueue, len, partOffsets}, outer, inner)
      ${outer}
        ${iteration}
        const observedOuter = {i, part, isLast, tempNodes}
        ${inner}
          ${firstNode}
          return finish(observedOuter, {j, len2, node})
        }
        return finish(observedOuter, null)
      }
      return finish(null, null)
    }
  } return Holder }
  return {define, emptyParams, order: () => order}
}`
let emitted = new Bun.Transpiler({loader:'ts'}).transformSync(wrapper)
assert.equal(emitted.split('__FIXED_SEED__();').length, 2)
emitted = emitted.replace('__FIXED_SEED__();', seed)
const makeModule = new Function(emitted + '\nreturn makeModule')()
const probeWrapper = `function headerProbe(curNodes, action, cap) {
  const trace = []
  ${inner}
    trace.push({index:j, bound:len2, value:curNodes[j]})
    if (action === 'grow') curNodes.push(99)
    if (action === 'shrink') curNodes.shift()
    if (trace.length >= cap) return {trace, capped:true, nodes:curNodes}
  }
  return {trace, capped:false, nodes:curNodes}
}`
const probeEmission = new Bun.Transpiler({loader:'ts'}).transformSync(probeWrapper)
const probe = new Function(probeEmission + '\nreturn headerProbe')()
const {createNullObject} = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const {METHOD_NAME_ALL} = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const {splitPath} = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
const string = (units:number[]) => units.map(unit => String.fromCharCode(unit)).join('')
const units = (text:string) => Array.from({length:text.length},(_,i) => text.charCodeAt(i))
const encode = (value:any):any => value === undefined ? {kind:'undefined'} :
  typeof value === 'string' ? {kind:'string', units:units(value)} : {kind:'number',value}
const results = (packet.cases ?? []).map((input:any) => {
  const module = makeModule(createNullObject, METHOD_NAME_ALL, splitPath), Holder = module.define()
  const root = new Holder(), other = new Holder(), stale = Object.assign(Object.create(null), {id:'stale'})
  Holder.prototype.seed.call(root, root, stale)
  Holder.prototype.seed.call(root, other, stale)
  for (let n = 0; n < (input.registrations ?? 0); n++) {
    Holder.prototype.register.call(root, n % 2 ? 'ALL' : 'GET', n, ['id','id','name'])
  }
  const oldArrays = [root,other].flatMap(owner => Holder.arrays(owner)), oldValues = oldArrays.map(array => array.slice())
  const methodValue = Holder.method(root), retained:any[] = [], snapshots:any[] = []
  let fresh = true, frame = true
  const observe = (state:any, outer:any, inner:any) => {
    const arrays = [state.handlerSets,state.curNodes,state.parts,state.curNodesQueue]
    if (outer) arrays.push(outer.tempNodes)
    fresh &&= arrays.every((array,at) => Array.isArray(array) && !oldArrays.includes(array) &&
      !retained.includes(array) && arrays.indexOf(array) === at)
    retained.push(...arrays)
    frame &&= oldArrays.every((array,at) => array.length === oldValues[at].length && array.every((v:any,i:number) => v === oldValues[at][i]))
    return {parts:state.parts.map(units),len:state.len,offsetsNull:state.partOffsets === null,
      collectorEmpty:state.handlerSets.length === 0,pendingEmpty:state.curNodesQueue.length === 0,
      singletonNodes:state.curNodes.length === 1 && state.curNodes[0] === root,
      resetShared:Holder.params(root) === module.emptyParams,otherKept:Holder.params(other) === stale,
      methodKept:[root,other].every(owner => Holder.method(owner) === methodValue),
      outer:outer === null ? null : {index:outer.i,part:encode(outer.part),isLast:outer.isLast,queueEmpty:outer.tempNodes.length === 0},
      inner:inner === null ? null : {index:inner.j,bound:inner.len2,nodeIsRoot:inner.node === root,nodeUndefined:inner.node === undefined}}
  }
  for (let n = 0; n < (input.repeat ? 2 : 1); n++) {
    if (n) Holder.prototype.seed.call(root, root, stale)
    snapshots.push(Holder.prototype.prefix.call(root,'GET',string(input.path ?? []),observe))
  }
  return {snapshots,fresh,oldArraysKept:frame,order:module.order()}
})
const probes = (packet.probes ?? []).map((input:any) => {
  const observed = probe(Array.from({length:input.length},(_,i) => i),input.action ?? 'keep',input.cap ?? 16)
  return {...observed,trace:observed.trace.map((row:any) => ({...row,value:encode(row.value)}))}
})
process.stdout.write(JSON.stringify({revision,runtime:Bun.version,checkedPinnedBlobs,
  transpilation:{verified:false,importedPinnedSplit:true,headerBodies:'explicit unverified observation continuations',
    inputSha256:sha(wrapper + '\0' + seed),emittedSha256:sha(emitted),
    probeInputSha256:sha(probeWrapper),probeEmittedSha256:sha(probeEmission)},results,probes}) + '\n')
