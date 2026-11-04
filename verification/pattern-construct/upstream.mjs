// Actual selected terminal tuple expression on genuine RegExp constructor identity.
// Plain-JS wrappers, observer and engine interpretation remain unverified.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'

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
const sha = bytes => createHash('sha256').update(bytes).digest('hex')
const metadata = JSON.parse(readFileSync(new URL('./source.json', import.meta.url)))
const raw = readFileSync(resolve(checkout, metadata.sourcePath)), span = metadata.fragments.full
const original = readFileSync(new URL('./full.ts.txt', import.meta.url), 'utf8')
assert.equal(metadata.revision, revision)
assert.equal(sha(raw), metadata.sourceSha256)
assert.equal(sha(original), span.sha256)
assert.equal(span.sha256, 'b70aef226ab3fc4a7ec886b9d64dbace87107beb4989920d05b48f6bd6b86560')
assert.equal(raw.subarray(span.startByte, span.endByteExclusive).toString(), original)
assert.equal(Buffer.byteLength(original), 46)
assert.equal(runtime,'bun')
const {getPattern}=await import(pathToFileURL(resolve(checkout,'src/utils/url.ts')).href)
const sourceGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'source').get
const flagsGetter=Object.getOwnPropertyDescriptor(RegExp.prototype,'flags').get
const unitString=values=>values.map(x=>String.fromCharCode(x)).join('')
const profiles=[['Digits','[0-9]+','12'],['Letters','[A-z]+','[\\]^_`'],['Punctuation','[9-A]+','9:@A'],['Singleton','[z-z]+','zz']]
const constructions=[]
for(const [profile,body,hit]of profiles)for(const [index,next]of [undefined,':later','*',''].entries()){
  const name=`actualConstruct${profile}${index}`,label=`:${name}{${body}}`
  const first=getPattern(label,next),again=getPattern(label,next)
  assert.equal(first,again);assert.equal(first[2],again[2]);assert.equal(first[0],label);assert.equal(first[1],name)
  const regex=first[2]
  assert.equal(sourceGetter.call(regex),'^'+body+'$');assert.equal(flagsGetter.call(regex),'')
  assert.equal(Object.getPrototypeOf(regex),RegExp.prototype)
  assert.deepEqual(Object.getOwnPropertyDescriptor(regex,'lastIndex'),{value:0,writable:true,enumerable:false,configurable:false})
  assert.equal(regex.exec(hit)[0],hit);assert.equal(regex.exec(hit+'\n'),null);assert.equal(regex.lastIndex,0)
  regex.lastIndex=17;assert.equal(getPattern(label,next)[2].lastIndex,17)
  constructions.push({profile,label,body,next:next===undefined?{kind:'undefined'}:{kind:'string',value:next},source:sourceGetter.call(regex),freshLastIndexZero:true,
    sameCachedTuple:first===again,cachedMatcherRetainsMutation:true,hit:unitString(Array.from(hit,x=>x.charCodeAt(0)))})
}
const orders=[]
for(const terminalFirst of [false,true]){
  const name='actualConstructorOrder'+(terminalFirst?'B':'A'),label=`:${name}{[0-9]+}`
  const first=getPattern(label,terminalFirst?undefined:'undefined'),second=getPattern(label,terminalFirst?'undefined':undefined)
  assert.equal(first,second);assert.equal(first[2],second[2])
  const expected=terminalFirst?'^[0-9]+$':String.raw`^[0-9]+(?=\/undefined)`
  assert.equal(sourceGetter.call(second[2]),expected)
  assert.equal(second[0],terminalFirst?label:label+'#undefined')
  orders.push({terminalFirst,sameTuple:true,sameMatcher:true,retainedSource:sourceGetter.call(second[2]),retainedTupleKey:second[0]})
}
console.log(JSON.stringify({revision,runtime,version,checkedPinnedBlobs,verified:false,nativeTypeScriptLoadingVerified:false,
  sourceSha256:sha(original),constructionCount:constructions.length,queryCount:constructions.length*2,constructions,orders,
  scope:'Finite actualgetPattern cold terminal constructions, cachehit identity/mutation and both undefined/stringundefined first-wins orders. Not a label-regex/cache/branchselection/insertion/destructuring/native proof; no D1 baseline change.'}))
