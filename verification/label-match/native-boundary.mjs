// Bounded native-only ENGINE-FLAGS-1 reproducer, independently reviewed.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'

const checkout = resolve(process.argv[2])
const revision = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const runtime = typeof Bun === 'undefined' ? 'node' : 'bun'
const version = runtime === 'bun' ? Bun.version : process.versions.node
assert.equal(version, runtime === 'bun' ? '1.4.0' : '22.22.2')
const git = (...args) => execFileSync('git', ['-C', checkout, ...args], {
  encoding: 'utf8', env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }
})
assert.equal(git('rev-parse', 'HEAD').trim(), revision)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
let checkedPinnedBlobs = 0
for (const entry of git('ls-tree', '-rz', revision, '--', 'src', 'package.json').split('\0').filter(Boolean)) {
  const tab = entry.indexOf('\t'), blob = entry.slice(0, tab).split(' ')[2]
  const bytes = readFileSync(resolve(checkout, entry.slice(tab + 1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), blob)
  checkedPinnedBlobs++
}
assert.equal(checkedPinnedBlobs, 315)
const raw = readFileSync(resolve(checkout, 'src/utils/url.ts'))
const source = raw.subarray(1387, 1446).toString()
const sourceSha256 = createHash('sha256').update(source).digest('hex')
assert.equal(Buffer.byteLength(source), 59)
assert.equal(sourceSha256, 'e1a741ae801aec83c5926a9d2b71e0b2a6dce9ee29406ef602a8d54a862d0207')
const invoke = new Function('label', '"use strict";\n' + source + '\nreturn match')
const encode = value => value === undefined ? { kind: 'undefined' } : { kind: 'string', value }
const observe = value => ({
  values: Array.from(value, encode), own2: Object.hasOwn(value, '2'),
  ownNames: Object.getOwnPropertyNames(value), index: value.index,
  input: value.input, ownGroups: Object.hasOwn(value, 'groups'),
  groupsUndefined: value.groups === undefined
})
const control = observe(invoke(':id'))
assert.deepEqual(control.values, [{ kind: 'string', value: ':id' }, { kind: 'string', value: 'id' }, { kind: 'undefined' }])
assert.equal(control.own2, true)
const oldStringDescriptors = Object.getOwnPropertyDescriptors(String.prototype)
const oldRegExpDescriptors = Object.getOwnPropertyDescriptors(RegExp.prototype)
const oldString = Object.getOwnPropertyDescriptor(String.prototype, 'match')
const oldSymbol = Object.getOwnPropertyDescriptor(RegExp.prototype, Symbol.match)
const oldGlobal = Object.getOwnPropertyDescriptor(RegExp.prototype, 'global')
const oldExec = Object.getOwnPropertyDescriptor(RegExp.prototype, 'exec')
const events = []
let instrumented
try {
  Object.defineProperty(String.prototype, 'match', {
    configurable: true, enumerable: oldString.enumerable,
    get() {
      events.push('getStringMatch')
      return function (rx) {
        events.push('callStringMatch')
        assert.equal(this, ':id')
        assert.equal(Object.getPrototypeOf(rx), RegExp.prototype)
        assert.deepEqual(Object.getOwnPropertyDescriptor(rx, 'lastIndex'), {
          value: 0, writable: true, enumerable: false, configurable: false
        })
        assert.equal(Object.hasOwn(rx, 'flags'), false)
        Object.defineProperty(rx, 'flags', {
          configurable: true,
          get() { events.push('getOwnFlags'); throw new Error('own-flags-read') }
        })
        events.push('installOwnFlags')
        return oldString.value.call(this, rx)
      }
    }
  })
  Object.defineProperty(RegExp.prototype, Symbol.match, {
    configurable: true, enumerable: oldSymbol.enumerable,
    get() {
      events.push('getSymbolMatch')
      return function (input) { events.push('callSymbolMatch'); return oldSymbol.value.call(this, input) }
    }
  })
  Object.defineProperty(RegExp.prototype, 'global', {
    configurable: true, enumerable: oldGlobal.enumerable,
    get() { events.push('getGlobal'); return oldGlobal.get.call(this) }
  })
  Object.defineProperty(RegExp.prototype, 'exec', {
    configurable: true, enumerable: oldExec.enumerable,
    get() {
      events.push('getExec')
      return function (input) { events.push('callExec'); return oldExec.value.call(this, input) }
    }
  })
  try { instrumented = { ok: true, result: observe(invoke(':id')) } }
  catch (error) { instrumented = { ok: false, message: error.message } }
} finally {
  Object.defineProperty(String.prototype, 'match', oldString)
  Object.defineProperty(RegExp.prototype, Symbol.match, oldSymbol)
  Object.defineProperty(RegExp.prototype, 'global', oldGlobal)
  Object.defineProperty(RegExp.prototype, 'exec', oldExec)
}
assert.deepEqual(Object.getOwnPropertyDescriptors(String.prototype), oldStringDescriptors)
assert.deepEqual(Object.getOwnPropertyDescriptors(RegExp.prototype), oldRegExpDescriptors)
const common = ['getStringMatch', 'callStringMatch', 'installOwnFlags', 'getSymbolMatch', 'callSymbolMatch']
if (runtime === 'bun') {
  assert.deepEqual(events, [...common, 'getOwnFlags'])
  assert.deepEqual(instrumented, { ok: false, message: 'own-flags-read' })
} else {
  assert.deepEqual(events, [...common, 'getGlobal', 'getExec', 'callExec'])
  assert.deepEqual(instrumented, { ok: true, result: control })
}
console.log(JSON.stringify({
  id: 'ENGINE-FLAGS-1', revision, runtime, version, checkedPinnedBlobs,
  sourceBytes: 59, sourceSha256, plainJavaScript: true, typescriptErasure: false,
  verified: false, nativeOnly: true, instrumented: true, control, events,
  outcome: instrumented, prototypesRestored: true, baselineAllowlistChanged: false,
  reference: 'https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-regexp.prototype-@@match',
  scope: 'Exact source with current String.match wrapper poisoning only the fresh literal own flags. Bun reads flags per selected 2025 edition; pinned Node uses direct global. Native-only boundary outside the standard realm; no normal-output/source-model counterexample or native protocol theorem.'
}))
