import assert from 'node:assert/strict'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
// One case per process: a failed lookup can mutate a watched builtin.
// No server or network request is created, and the upstream tree is read only.
const arguments_ = Bun.argv.slice(2)
assert.equal(arguments_.length, 3, 'Usage: bun verification/routing-method-probe.ts <hono-checkout> <RouterName> <method>')
const [checkoutArgument, routerName, method] = arguments_
const checkout = resolve(checkoutArgument)
const pin = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git = (...args: string[]) => {
  const result = Bun.spawnSync(['git', '-C', checkout, ...args], { env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' } })
  assert.equal(result.exitCode, 0)
  return result.stdout.toString()
}
assert.equal(git('rev-parse', 'HEAD').trim(), pin)
assert.equal(git('status', '--porcelain', '--untracked-files=all').trim(), '')
const blobs = git('ls-tree', '-rz', pin, '--', 'src', 'package.json').split('\0').filter(Boolean)
for (const entry of blobs) {
  const tab = entry.indexOf('\t'), expected = entry.slice(0, tab).split(' ')[2]
  const path = entry.slice(tab + 1)
  const bytes = Buffer.from(await Bun.file(checkout + '/' + path).arrayBuffer())
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'), expected)
}
assert.equal(Bun.version, '1.4.0')
const sources: Record<string, [string, string]> = {
  TrieRouter: ['trie-router/router.ts', 'TrieRouter'],
  RegExpRouter: ['reg-exp-router/router.ts', 'RegExpRouter'],
  LinearRouter: ['linear-router/router.ts', 'LinearRouter'],
  PatternRouter: ['pattern-router/router.ts', 'PatternRouter'],
  SmartRouter: ['smart-router/router.ts', 'SmartRouter'],
}
assert(Object.hasOwn(sources, routerName), 'Unsupported RouterName')
const [file, symbol] = sources[routerName]
const module = await import(checkout + '/src/router/' + file)
let router
if (routerName === 'SmartRouter') {
  const { RegExpRouter } = await import(checkout + '/src/router/reg-exp-router/router.ts')
  const { TrieRouter } = await import(checkout + '/src/router/trie-router/router.ts')
  router = new module[symbol]({ routers: [new RegExpRouter(), new TrieRouter()] })
} else router = new module[symbol]()
const watch = [['Object', Object], ['Object.prototype', Object.prototype],
  ['Object.prototype.toString', Object.prototype.toString]] as const
const snapshot = () => watch.map(([name, value]) => {
  const descriptor = Object.getOwnPropertyDescriptor(value, 'params')
  return { name, hasOwnParams: descriptor !== undefined,
    paramsDescriptor: descriptor ? { valueType: typeof descriptor.value,
      valueHasNullPrototype: Object.getPrototypeOf(descriptor.value) === null,
      ownValueKeys: Object.keys(descriptor.value), writable: descriptor.writable,
      enumerable: descriptor.enumerable, configurable: descriptor.configurable } : null }
})
router.add('GET', '/a', 'a')
const before = snapshot()
let result: unknown = null, exception: unknown = null
try { result = router.match(method, '/a') } catch (error) {
  exception = error instanceof Error ? { name: error.name, message: error.message } : { thrown: String(error) }
}
const after = snapshot()
console.log(JSON.stringify({ runtime: Bun.version, revision: pin, router: routerName,
  input: { routes: [{ method: 'GET', path: '/a', handler: 'a' }], request: { method, path: '/a' } },
  result, exception, before, after }))
