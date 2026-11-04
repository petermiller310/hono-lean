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
const splitMeta = await Bun.file(new URL('../splitpath/source.json', import.meta.url)).json()
const splitBytes = Buffer.from(await Bun.file(resolve(checkout, splitMeta.sourcePath)).arrayBuffer())
const splitSource = await Bun.file(new URL('../splitpath/splitPath.ts.txt', import.meta.url)).text()
assert.equal(sha(splitBytes), splitMeta.sourceSha256)
assert.equal(sha(splitSource), splitMeta.functionSha256)
assert.equal(splitBytes.subarray(splitMeta.startByte, splitMeta.endByteExclusive).toString('ascii'), splitSource)
const packet = JSON.parse(await Bun.stdin.text())
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
    startup(method, path) {
      ${packet.startupSource ?? startup}
      return {handlerSets, curNode, curNodes, parts, curNodesQueue, len, partOffsets};
    }
    iteration(parts, i, len) {
      ${iteration}
      return {part, isLast, tempNodes};
    }
  } return Holder }
  return {define, emptyParams, order: () => order}
}`
let emitted = new Bun.Transpiler({loader: 'ts'}).transformSync(wrapper)
assert.equal(emitted.split('__FIXED_SEED__();').length, 2)
emitted = emitted.replace('__FIXED_SEED__();', seed)
const makeModule = new Function(emitted + '\nreturn makeModule')()
const {createNullObject} = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const {METHOD_NAME_ALL} = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const {splitPath: importedSplitPath} = await import(pathToFileURL(resolve(checkout, 'src/utils/url.ts')).href)
let chosenSplitPath = importedSplitPath
let splitEmission: string | null = null
if (packet.splitSource !== undefined) {
  splitEmission = new Bun.Transpiler({loader: 'ts'}).transformSync(packet.splitSource.replace(/^export /, ''))
  chosenSplitPath = new Function(splitEmission + '\nreturn splitPath')()
}
const string = (units: number[]) => units.map(u => String.fromCharCode(u)).join('')
const units = (text: string) => Array.from({length: text.length}, (_,i) => text.charCodeAt(i))
const results = (packet.cases ?? []).map((input: any) => {
  const module = makeModule(createNullObject, METHOD_NAME_ALL, chosenSplitPath)
  const First = module.define(), Second = module.define()
  const root = new First(), other = new First(), foreign = new Second(), plain = Object.create(null)
  const values: Record<string, any> = {root, other, foreign, plain, u: undefined, n: null}
  const owners = [root, other], stale = Object.assign(Object.create(null), {id:'stale'})
  First.prototype.seed.call(root, root, stale)
  First.prototype.seed.call(root, other, stale)
  for (let n = 0; n < (input.registrations ?? 0); n++) {
    First.prototype.register.call(root, n % 2 ? 'ALL' : 'GET', n, ['id', 'id', 'name'])
  }
  const oldArrays = owners.flatMap(owner => First.arrays(owner))
  const oldValues = oldArrays.map(array => array.slice()), methodValue = First.method(root)
  const receiver = values[input.receiver ?? 'root'], path = string(input.path ?? [])
  const snapshots: any[] = []
  const allFresh: any[] = []
  let fresh = true, frames = true
  try {
    for (let n = 0; n < (input.repeat ? 2 : 1); n++) {
      if (n) First.prototype.seed.call(root, root, stale)
      const state = First.prototype.startup.call(receiver, 'GET', path)
      const generated = [state.handlerSets, state.curNodes, state.parts, state.curNodesQueue]
      fresh &&= generated.every((value, at) => Array.isArray(value) && !oldArrays.includes(value) &&
        !allFresh.includes(value) && generated.indexOf(value) === at)
      allFresh.push(...generated)
      frames &&= oldArrays.every((array, at) => array.length === oldValues[at].length &&
        array.every((value: any, i: number) => value === oldValues[at][i]))
      const i = input.i ?? 0
      let outer = null
      if (i < state.parts.length) {
        const output = First.prototype.iteration.call(receiver, state.parts, i, state.len)
        outer = {part: units(output.part), isLast: output.isLast,
          queueFresh: Array.isArray(output.tempNodes) && output.tempNodes.length === 0 &&
            !allFresh.includes(output.tempNodes) && !oldArrays.includes(output.tempNodes),
          nodeIsReceiver: state.curNodes[0] === receiver}
        allFresh.push(output.tempNodes)
      }
      snapshots.push({parts: state.parts.map(units), len: state.len, offsetsNull: state.partOffsets === null,
        collectorEmpty: state.handlerSets.length === 0, pendingEmpty: state.curNodesQueue.length === 0,
        rootAlias: state.curNode === receiver, singletonNodes: state.curNodes.length === 1 && state.curNodes[0] === receiver,
        resetShared: First.params(root) === module.emptyParams, otherKept: First.params(other) === stale,
        methodKept: owners.every(owner => First.method(owner) === methodValue), outer})
    }
  } catch (error) {
    if (!(error instanceof TypeError)) throw error
    return {ok: false}
  }
  return {ok: true, snapshots, fresh, oldArraysKept: frames, order: module.order()}
})
process.stdout.write(JSON.stringify({revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: {verified: false, importedPinnedSplit: packet.splitSource === undefined,
    inputSha256: sha(wrapper + '\0' + seed), emittedSha256: sha(emitted),
    splitEmittedSha256: splitEmission === null ? null : sha(splitEmission)}, results}) + '\n')
