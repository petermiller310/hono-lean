// Finite whole pinned TrieRouter context. This does not close full search,
// matcher.exec, TypeScript frontend or native adequacy obligations.
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
assert.equal(Bun.version,'1.4.0')
const checkout=resolve(Bun.argv[2]),revision='5ca49b0720755c585c9a9835f0a479ceea36fb52'
const git=(...args)=>execFileSync('git',['-C',checkout,...args],{encoding:'utf8',env:{...process.env,GIT_OPTIONAL_LOCKS:'0'}})
assert.equal(git('rev-parse','HEAD').trim(),revision);assert.equal(git('status','--porcelain','--untracked-files=all').trim(),'')
let checkedPinnedBlobs=0
for(const entry of git('ls-tree','-rz',revision,'--','src','package.json').split('\0').filter(Boolean)) {
  const tab=entry.indexOf('\t'),blob=entry.slice(0,tab).split(' ')[2],bytes=readFileSync(resolve(checkout,entry.slice(tab+1)))
  assert.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),blob);checkedPinnedBlobs++
}
const {TrieRouter}=await import(pathToFileURL(resolve(checkout,'src/router/trie-router/router.ts')).href)
const records=[]
for(const [first,second] of [['id','id'],['constructor','id'],['__proto__','id'],['id','__proto__']])for(const path of ['/alpha/12','/alpha/no']) {
  const pattern=`/:${first}/:${second}{[0-9]+}`,router=new TrieRouter()
  router.add('GET',pattern,'capture');const hits=router.match('GET',path)[0]
  const record={first,second,path,pattern,handlers:hits.map(hit=>hit[0])}
  if(hits.length) {
    const params=hits[0][1]
    record.nullPrototype=Object.getPrototypeOf(params)===null
    record.entries=Object.keys(params).sort().map(key=>[key,params[key]===Object.prototype?{objectPrototype:true}:params[key]])
  }
  records.push(record)
}
console.log(JSON.stringify({revision,checkedPinnedBlobs,verified:false,nativeTypeScriptLoadingVerified:false,records}))
