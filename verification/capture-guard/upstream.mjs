// Finite whole-router controls. Bun's TypeScript loader and the engine remain
// unverified. These observations do not close matcher.exec or full search proofs.
import assert from 'node:assert/strict'
import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
assert.equal(Bun.version,'1.4.0')
const checkout=resolve(Bun.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision)
assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)) {
  const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
const {TrieRouter}=await import(pathToFileURL(resolve(checkout,'src/router/trie-router/router.ts')).href)
const records=[]
for(const name of ['id','constructor','__proto__'])for(const path of ['/alpha','/123']) {
  const router=new TrieRouter(),pattern=`/:${name}{[a-z]+}`
  router.add('GET',pattern,'capture')
  const hits=router.match('GET',path)[0]
  const record={name,pattern,path,handlers:hits.map(hit=>hit[0])}
  if(hits.length) {
    const params=hits[0][1],value=params[name]
    record.own=Object.hasOwn(params,name);record.nullPrototype=Object.getPrototypeOf(params)===null
    record.value=value===Object.prototype?{objectPrototype:true}:value
  }
  records.push(record)
}
console.log(JSON.stringify({revision,checkedPinnedBlobs,verified:false,nativeTypeScriptLoadingVerified:false,records}))
