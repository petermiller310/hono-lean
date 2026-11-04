// Three exact source operations in a supplied event context, not Node.insert.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'

const checkout = resolve(Bun.argv[2])
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => execFileSync('git', ['-C', checkout, ...args],
  { encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
assert.equal(Bun.version, '1.4.0')
assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
for (const entry of git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = Buffer.from(await Bun.file(resolve(checkout, entry.slice(tab + 1))).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
}
const metadata = await Bun.file(new URL('./source.json', import.meta.url)).json()
const file = Buffer.from(await Bun.file(resolve(checkout, metadata.sourcePath)).arrayBuffer())
assert.equal(createHash('sha256').update(file).digest('hex'), metadata.sourceSha256)
const texts: Record<string, string> = {}
for (const name of ['create', 'add', 'spread']) {
  texts[name] = await Bun.file(new URL(`./${name}.ts.txt`, import.meta.url)).text()
  const span = metadata.fragments[name]
  assert.equal(file.subarray(span.startByte, span.endByteExclusive).toString('ascii'), texts[name])
  assert.equal(createHash('sha256').update(texts[name]).digest('hex'), span.sha256)
}
const packet = JSON.parse(await Bun.stdin.text())
const transpiler = new Bun.Transpiler({ loader: 'ts' })
const compile = (source: string, name: string) => {
  const emitted = transpiler.transformSync(source)
  return { emitted, value: new Function(emitted + '\nreturn ' + name)() }
}
// The original TS constructor text remains intact. Bun performs its unchecked
// type erasure; this native evidence does not verify the transpiler.
const create = compile(`function make(Set, Factory) {
  const possibleKeys = 'outer'
  const inner = () => { ${packet.createSource ?? texts.create}
    return possibleKeys }
  return { value: inner(), outerKept: possibleKeys === 'outer' }
}`, 'make')
const add = compile(`function add(possibleKeys, pattern) {
  return ( ${packet.addSource ?? texts.add} )
}`, 'add')
const spread = compile(`function spread(possibleKeys) {
  return ( ${packet.spreadSource ?? texts.spread} )
}`, 'spread')
const fromUnits = (units: number[]) => units.map(unit => String.fromCharCode(unit)).join('')
const toUnits = (text: string) => Array.from({ length: text.length }, (_, i) => text.charCodeAt(i))
const same = (a: any[], b: any[]) => a.length === b.length && a.every((value, i) => Object.is(value, b[i]))
const results = packet.cases.map((input: any) => {
  const oldSet = new Set(['frame-set'])
  const initialPattern: any[] = [undefined, undefined]
  const oldArray = ['frame-array']
  const constructed = create.value(Set, Set)
  const possibleKeys = constructed.value
  const alias = possibleKeys
  const arrays: any[][] = [initialPattern, oldArray]
  let addReturnedAlias = true
  let inputFrameKept = true
  const feed = (names: number[][]) => {
    for (const name of names) {
      // Explicit caller context, not a claim about insertion's branch trace.
      const pattern: any[] = [undefined, fromUnits(name)]
      arrays.push(pattern)
      const before = [...pattern]
      const result = add.value(possibleKeys, pattern)
      addReturnedAlias = (result === alias) && addReturnedAlias
      inputFrameKept &&= same(pattern, before)
    }
  }
  feed(input.names)
  const first = spread.value(possibleKeys)
  assert(Array.isArray(first)); arrays.push(first)
  const copiedFirst = [...first]
  const second = spread.value(possibleKeys)
  assert(Array.isArray(second)); arrays.push(second)
  feed(input.later ?? [])
  const third = spread.value(possibleKeys)
  assert(Array.isArray(third)); arrays.push(third)
  const snapshots = [first, second, third].map(value => ({ ref: arrays.indexOf(value),
    keys: value.map(item => { assert.equal(typeof item, 'string'); return toUnits(item) }) }))
  return { setRef: 1, freshSet: possibleKeys !== oldSet, outerKept: constructed.outerKept,
    addReturnedAlias, inputFrameKept, snapshots,
    firstUnchanged: same(first, copiedFirst), distinctArrays: first !== second && second !== third && first !== third,
    setKeys: [...Set.prototype.values.call(possibleKeys)].map(toUnits),
    frameKept: same([...oldSet], ['frame-set']) && same(oldArray, ['frame-array']) }
})
let scope: any = null
if (packet.scopeProbes) {
  const standard = create.value(Set, Set).value
  add.value(standard, ['pattern', 'a', 'matcher'])
  add.value(standard, ['pattern', 'b', 'matcher'])
  const iterator = Set.prototype.values.call(standard)
  const first = iterator.next()
  add.value(standard, ['pattern', 'c', 'matcher'])
  const remaining = [iterator.next(), iterator.next(), iterator.next()]
  add.value(standard, ['pattern', 'd', 'matcher'])
  const exhausted = iterator.next()
  standard[Symbol.iterator] = function* () { yield 'a'; yield 'a'; yield 'b' }
  const overridden = spread.value(standard)
  let coercions = 0
  const boxed = create.value(Set, Set).value
  const one = new String('x'), two = new String('x')
  one.toString = two.toString = () => { coercions++; return 'x' }
  add.value(boxed, ['pattern', one, 'matcher'])
  add.value(boxed, ['pattern', two, 'matcher'])
  scope = { liveFirst: first.value, liveRemaining: remaining.map(value => value.done ? null : value.value),
    exhaustedStaysDone: exhausted.done === true, overriddenIterator: overridden.map(toUnits),
    boxedDistinct: boxed.size === 2, coercions }
}
console.log(JSON.stringify({ runtime: Bun.version, revision: pin,
  transpilation: { loader: 'ts', createInputSha256: createHash('sha256').update(packet.createSource ?? texts.create).digest('hex'),
    emittedCreateSha256: createHash('sha256').update(create.emitted).digest('hex'), verified: false }, results, scope }))
