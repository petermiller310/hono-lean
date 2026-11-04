// Exact data-field/preamble text in explicit class/default-constructor scaffolding.
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
const helperMeta = await Bun.file(new URL('../methods-loop/source.json', import.meta.url)).json()
const helperSource = bytes.subarray(helperMeta.containingMethod.startByte, helperMeta.containingMethod.endByteExclusive).toString('ascii')
assert.equal(sha(helperSource), helperMeta.containingMethod.sha256)
const packet = JSON.parse(await Bun.stdin.text())
const wrapper = `function makeModule(createNullObject) { ${packet.preambleSource ?? fragments.preamble}
  function define() { class Holder<T> {
    ${packet.fieldsSource ?? fragments.fields}
    ${helperSource}
    static inspect(value) { return [value.#methods, value.#children, value.#patterns, value.#pattern, value.#params] }
  } return Holder }
  return { define, emptyParams, order: () => order }
}`
const emitted = new Bun.Transpiler({ loader: 'ts' }).transformSync(wrapper)
const makeModule = new Function(emitted + '\nreturn makeModule')()
const { createNullObject } = await import(pathToFileURL(resolve(checkout, 'src/router/utils.ts')).href)
const encodePattern = (value: unknown, moduleEmpty: unknown) => value === undefined ? 'undefined' : value === null ? 'null' : value === moduleEmpty ? 'module' : typeof value
const results = (packet.cases ?? []).map((input: any) => {
  let helperCalls = 0
  const module = makeModule(() => { helperCalls++; return createNullObject() })
  const definitions: any[] = [], instances: any[] = [], snapshots: any[] = [], owners: number[] = []
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
    prototypeKept: Object.getPrototypeOf(instances[at]) === definitions[owners[at]].prototype }))
  return { instances: observations, arraysIsolated: arraySet.size === 2 * instances.length,
    childrenIsolated: objectSet.size === instances.length && !objectSet.has(module.emptyParams),
    sharedParams: snapshots.every(values => values[4] === module.emptyParams),
    moduleNullPrototype: Object.getPrototypeOf(module.emptyParams) === null, helperCalls, order: module.order(),
    classBrandMatrix, unbrandedRejected }
})
let scope: unknown = null
if (packet.scopeProbes) {
  let selfThrows = false, laterThrows = false
  try { class Self { #x = this.#x }; new Self() } catch { selfThrows = true }
  try { class Later { #x = this.#y; #y = 1 }; new Later() } catch { laterThrows = true }
  class Earlier { #x = 1; #y = this.#x; read() { return this.#y } }
  class Omitted { #x; #y = this.#x; read() { return this.#y } }
  class WithMethod { #x = this.#read(); #read() { return 7 }; read() { return this.#x } }
  let calls = 0
  class Returner { constructor(value: object) { return value } }
  class Stamp extends Returner { #x = ++calls; static read(value: Stamp) { return value.#x } }
  const target = Object.preventExtensions({}); new Stamp(target)
  let duplicateThrows = false; try { new Stamp(target) } catch { duplicateThrows = true }
  const copiedPrototype = Object.create(Object.getPrototypeOf(target))
  let cloneThrows = false; try { Stamp.read(copiedPrototype) } catch { cloneThrows = true }
  scope = { selfThrows, laterThrows, earlier: new Earlier().read(), omittedUndefined: new Omitted().read() === undefined,
    privateMethodBeforeField: new WithMethod().read(), nonextensibleStamp: Stamp.read(target), duplicateThrows, initializerCalls: calls, cloneThrows }
}
process.stdout.write(JSON.stringify({ revision, runtime: Bun.version, checkedPinnedBlobs,
  transpilation: { verified: false, loader: 'ts', inputSha256: sha(wrapper), emittedSha256: sha(emitted) }, results, scope }) + '\n')
