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
const windows: Record<string,string> = {}
for (const name of ['search','iteration','entry']) windows[name] = await fragment('iteration-setup', name)
const packet = JSON.parse(await Bun.stdin.text())
const sources = Object.fromEntries(Object.entries(windows).map(([name, text]) => [name, packet[`${name}Source`] ?? text]))
const wrapper = `function makeModule(createNullObject, METHOD_NAME_ALL) { ${preamble}
  function define() { class Holder {
    ${fields}
    ${method}
    static params(owner) { return owner.#params }
    static method(owner) { return owner.#pushHandlerSets }
    static link(owner, key, value) { owner.#children[key] = value }
    static arrays(owner) { return [owner.#methods, owner.#patterns, ...owner.#methods.flatMap(Object.values).map(r => r.possibleKeys)] }
    seed(child, params) { __BRANCH_SEED__(); }
    register(method, handler, events) {
      const curNode = this, possibleKeys = new Set(events); ${push}
    }
    searchSetup(parts) {
      ${sources.search}
      return {len, partOffsets};
    }
    iterationSetup(parts, i, len, curNodes) {
      ${sources.iteration}
      return {part, isLast, tempNodes};
    }
    perform(curNodes, j, part, isLast, handlerSets, tempNodes, method) {
      __ITERATION_ENTRY__();
      return {node, nextNode};
    }
  } return Holder }
  return { define, emptyParams, order: () => order }
}`
let emitted = new Bun.Transpiler({loader: 'ts'}).transformSync(wrapper)
assert.equal(emitted.split('__BRANCH_SEED__();').length, 2)
emitted = emitted.replace('__BRANCH_SEED__();', seed)
assert.equal(emitted.split('__ITERATION_ENTRY__();').length, 2)
emitted = emitted.replace('__ITERATION_ENTRY__();', sources.entry)
const makeModule = new Function(emitted + '\nreturn makeModule')()
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const { METHOD_NAME_ALL } = await import(pathToFileURL(resolve(checkout, 'src/router.ts')).href)
const string = (units: number[]) => units.map(u => String.fromCharCode(u)).join('')
const units = (text: string) => Array.from({length: text.length}, (_,i) => text.charCodeAt(i))
const primitives: Record<string, any> = {u: undefined, n: null, f: false, t: true, z: 0, one: 1, empty: '', text: 'x'}
const encode = (v: any): any => v === undefined ? {kind: 'undefined'} : v === null ? {kind: 'null'} :
  typeof v === 'string' ? {kind: 'string', units: units(v)} : typeof v === 'number' ?
    {kind: 'number', value: v} : {kind: 'bool', value: v}
const fill = (entries: any[]) => {
  const object = Object.create(null)
  for (const [key, code] of entries ?? []) Object.defineProperty(object, string(key), {
    value: primitives[code], writable: true, enumerable: true, configurable: true
  })
  return object
}
const capture = (object: any) => Object.getOwnPropertyNames(object).sort((a,b) => a < b ? -1 : a > b ? 1 : 0)
  .map(key => ({key: units(key), value: encode(object[key])}))
const results = (packet.cases ?? []).map((input: any) => {
  const module = makeModule(createNullObject, METHOD_NAME_ALL), First = module.define(), Second = module.define()
  const root = new First(), parent = new First(), literal = new First(), wildcard = new First(), foreign = new Second()
  const owners = {root, parent, literal, wildcard, foreign}, paramsA = fill(input.entries), paramsB = fill(input.laterEntries)
  const values: Record<string, any> = {...primitives, ...owners, plain: Object.create(null)}
  const selected = values[input.child ?? 'literal'], star = values[input.wildcard ?? 'u']
  const parts = (input.parts ?? [[108,105,116]]).map(string)
  const curNodes = (input.nodes ?? ['parent']).map((name: string) => values[name])
  const i = input.i ?? 0, j = input.j ?? 0, canonicalNode = curNodes[j], canonicalPart = parts[i]
  const query = string(input.query ?? [71,69,84])
  const branded = [root, parent, literal, wildcard]
  // Fixed fixture inputs, independent of mutated setup/entry source. These
  // ordinary maps and separate source202 seeds do not prove Node.insert.
  if (branded.includes(canonicalNode)) First.link(canonicalNode, canonicalPart, selected)
  if (branded.includes(selected)) First.link(selected, '*', star)
  const fixedSeed = First.prototype.seed
  if (branded.includes(canonicalNode)) fixedSeed.call(root, canonicalNode, paramsA)
  for (const [target, registrations] of [[literal, input.literal ?? []], [wildcard, input.star ?? []]] as any[]) {
    for (const r of registrations) First.prototype.register.call(target, string(r.method), r.handler, r.keys.map(string))
  }
  const methodValue = First.method(root)
  const handlerSets: any[] = []
  const receiver = values[input.receiver ?? 'root']
  const beforeParts = parts.slice(), beforeNodes = curNodes.slice()
  let nextNode: any, node: any, setup: any, saved: any, previousQueue: any
  let queueFresh = true
  const run = () => {
    // Omitted for-headers are explicit caller activations supplying only i/j.
    const oldArrays = [parts, curNodes, handlerSets, ...branded.flatMap(o => First.arrays(o))]
    setup = First.prototype.iterationSetup.call(receiver, parts, i, saved.len, curNodes)
    queueFresh &&= !oldArrays.includes(setup.tempNodes) && setup.tempNodes !== previousQueue
    previousQueue = setup.tempNodes
    ;({node, nextNode} = First.prototype.perform.call(receiver, curNodes, j, setup.part, setup.isLast,
      handlerSets, setup.tempNodes, query))
  }
  try {
    saved = First.prototype.searchSetup.call(receiver, parts)
    run()
    if (input.repeat) {
      if (branded.includes(canonicalNode)) fixedSeed.call(root, canonicalNode, paramsB)
      run()
    }
  } catch (error) {
    if (!(error instanceof TypeError)) throw error
    return {ok: false}
  }
  const label = (value: any): any => {
    for (const [name, object] of Object.entries(owners)) if (value === object) return {kind: name}
    return encode(value)
  }
  const paramsLabel = (value: any) => value === module.emptyParams ? 'shared' : value === paramsA ? 'A' : value === paramsB ? 'B' : 'unknown'
  return {ok: true, next: label(nextNode), node: label(node), temp: setup.tempNodes.map(label),
    setup: {len: saved.len, part: encode(setup.part), isLast: setup.isLast, offsetsNull: saved.partOffsets === null,
      queueFresh, partsKept: parts.length === beforeParts.length && parts.every((v: any, at: number) => v === beforeParts[at]),
      nodesKept: curNodes.length === beforeNodes.length && curNodes.every((v: any, at: number) => v === beforeNodes[at])},
    matches: handlerSets.map(r => ({handler: r.handler, score: r.score, keys: r.possibleKeys.map(units), captures: capture(r.params)})),
    sameRecords: handlerSets.map(a => handlerSets.map(b => a === b)),
    sameParams: handlerSets.map(a => handlerSets.map(b => a.params === b.params)),
    params: Object.entries(owners).map(([name, owner]) => [name, paramsLabel((name === 'foreign' ? Second : First).params(owner))]),
    order: module.order(), methodKept: [root, parent, literal, wildcard].every(o => First.method(o) === methodValue),
    nullPrototypes: handlerSets.every(r => Object.getPrototypeOf(r.params) === null)}
})
process.stdout.write(JSON.stringify({revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: {verified: false, loader: 'ts', plainEntryInsertion: true,
    inputSha256: sha(wrapper + '\0' + JSON.stringify({seed, entry: sources.entry})), emittedSha256: sha(emitted)}, results}) + '\n')
