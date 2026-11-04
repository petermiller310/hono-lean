import assert from 'node:assert/strict';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import test from 'node:test';
import { expandExports, loadTypeScript, scanProject, generate, verifyCheckout, writeOrCheck } from '../inventory.mjs';

const parser=loadTypeScript();
const entry=source=>[{entryPoint:'.',exportPattern:'.',source,targets:{import:'./dist/index.js'}}];
function fixture(files){
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'hono-inventory-test-'));
  for(const [p,s]of Object.entries(files)){const name=path.join(root,p);fs.mkdirSync(path.dirname(name),{recursive:true});fs.writeFileSync(name,s);}
  const list=Object.keys(files);
  return {root,list,cleanup:()=>fs.rmSync(root,{recursive:true,force:true}),scan:(source='src/index.ts')=>scanProject(root,list,parser.ts,entry(source))};
}
const using=(files,fn)=>{const f=fixture(files);try{return fn(f);}finally{f.cleanup();}};

test('wildcards expand nested subpaths and explicit keys take precedence',()=>{
  const exports={'./utils/*':{import:'./dist/utils/*.js',types:'./dist/types/utils/*.d.ts'},'./utils/a':{import:'./dist/other.ts.js'}};
  const result=expandExports(exports,['src/utils/a.ts','src/utils/deep/b.ts','src/other.ts.ts']);
  assert.deepEqual(result.map(e=>[e.entryPoint,e.source]),[['./utils/a','src/other.ts.ts'],['./utils/deep/b','src/utils/deep/b.ts']]);
  assert.throws(()=>expandExports({'.':{import:'./dist/missing.js'}},[]),/Expected one source/);
});

test('type-only class aliases and star chains stay erased; explicit runtime wins',()=>using({
  'src/a.ts':'export class C {}\nexport interface T {}\nexport abstract class RuntimeAbstract {}',
  'src/b.ts':'export type * from "./a"',
  'src/index.ts':'export * from "./b"; export {C as ValueC} from "./a"; export type {C as TypeC} from "./a"; export {RuntimeAbstract} from "./a";import type {C as Imported} from "./a";export {Imported};export * as Namespace from "./b";'
},f=>{
  const result=f.scan();const m=new Map(result.exports[0].symbols.map(s=>[s.name,s.classification]));
  assert.equal(m.get('C'),'type_only');assert.equal(m.get('T'),'type_only');
  assert.equal(m.get('ValueC'),'runtime');assert.equal(m.get('TypeC'),'type_only');assert.equal(m.get('RuntimeAbstract'),'runtime');
  assert.equal(m.get('Imported'),'type_only');assert.equal(m.get('Namespace'),'runtime');
}));

test('inherited accessors, static methods, arrow fields, options and private source remain indexed',()=>using({
  'src/base.ts':'export class Base { private secret=1; #realSecret=2; get value(){return this.secret}; set value(v:number){this.secret=v}; static make(){}; public arrow=(x:string)=>x }',
  'src/index.ts':'import {Base} from "./base"; type Options={router?:unknown}&({strict?:true;getPath?:()=>string}|{strict:false;getPath?:never}); export class Child extends Base {constructor(options:Options={}){super()} }'
},f=>{
  const result=f.scan();const c=result.exports[0].symbols.find(s=>s.name==='Child').class;
  assert(c.instance.some(m=>m.name==='value'&&m.inherited));assert(c.static.some(m=>m.name==='make'));
  assert(c.instance.some(m=>m.name==='arrow'&&m.parameters[0].name==='x'));
  assert(!c.instance.some(m=>m.name==='secret'||m.name==='#realSecret'));
  assert.deepEqual(c.constructors[0].parameters[0].declaredObjectProperties.map(p=>p.name),['getPath','router','strict']);
  assert(result.modules.find(m=>m.source==='src/base.ts').declarations.some(d=>d.name==='secret'&&d.visibility==='typescript_private_runtime_present'));
}));

test('generated methods and direct constructor assignments have actual origins',()=>using({
  'src/methods.ts':'export const METHODS=["get","post"] as const; export const ALL="all";',
  'src/index.ts':'import {METHODS,ALL} from "./methods"; export class App {get!:()=>void;post!:()=>void;all!:()=>void;on!:(name:string)=>void; constructor(){const names=[...METHODS,ALL];names.forEach(method=>{this[method]=()=>{}});this.on=(name:string)=>{};Object.assign(this,{})}} class Other {get!:()=>void;constructor(){this.get=()=>{}}}'
},f=>{
  const result=f.scan();const dynamic=result.dynamicSites.find(s=>s.kind==='computed_property_assignment');
  assert.deepEqual(dynamic.resolvedNames,['all','get','post']);
  assert.equal(dynamic.nameResolutionExhaustive,false);
  const c=result.exports[0].symbols.find(s=>s.name==='App').class;
  assert.equal(c.instance.find(m=>m.name==='get').runtimeAssignmentOrigins.length,1);
  assert.equal(c.instance.find(m=>m.name==='on').runtimeAssignmentOrigins[0].parameters[0].name,'name');
  assert(result.gaps.some(g=>g.kind==='reflective_property_update'));
}));

test('factory returned methods are visible and host array methods do not become options',()=>using({
  'src/index.ts':'class Factory {createApp(){return 1}; private hidden(){};createMiddleware(){return 2}}; export const createFactory=()=>new Factory(); export const input=(options:string[])=>options;'
},f=>{
  const result=f.scan();const sym=result.exports[0].symbols;
  assert.deepEqual(sym.find(s=>s.name==='createFactory').returnedShapes[0].members.map(m=>m.name),['createApp','createMiddleware']);
  const p=sym.find(s=>s.name==='input').signatures[0][0];
  assert.equal(p.declaredObjectProperties.length,0);assert(p.hostOrIntrinsicMembersPresent);
}));

test('object exports, default objects and aliases expose one-level public member candidates',()=>using({
  'src/values.ts':'const use=(input:string)=>input;export const api={map:(value:number)=>value,use,nested:{hidden:1}};export default {run:use};export const array:string[]=[];export class C {method(){}}',
  'src/index.ts':'export {api,default as DefaultApi,array,C} from "./values";'
},f=>{
  const byName=new Map(f.scan().exports[0].symbols.map(s=>[s.name,s]));
  const api=byName.get('api').valueShape;
  assert.deepEqual(api.members.map(m=>m.name),['map','nested','use']);
  assert.equal(api.members.find(m=>m.name==='map').signatures[0].parameters[0].name,'value');
  assert.equal(api.members.find(m=>m.name==='use').signatures[0].parameters[0].name,'input');
  assert.equal(api.members.find(m=>m.name==='map').evidence.sourceConnection,'absent');
  assert.equal(api.members.find(m=>m.name==='nested').valueShape,undefined);
  assert.deepEqual(byName.get('DefaultApi').valueShape.members.map(m=>m.name),['run']);
  assert.equal(byName.get('array').valueShape.members.length,0);
  assert(byName.get('array').valueShape.excludedHostOrIntrinsicMemberCount>0);
  assert.equal(byName.get('C').valueShape,null);assert(byName.get('C').class);
}));

test('pinned ledger includes the actual Children and default JSX object APIs',()=>{
  const ledger=JSON.parse(fs.readFileSync(new URL('../coverage.json',import.meta.url),'utf8'));
  const symbol=(entry,name)=>ledger.exports.find(e=>e.entryPoint===entry).symbols.find(s=>s.name===name);
  assert.deepEqual(symbol('./jsx','Children').valueShape.members.map(m=>m.name),['count','forEach','map','only','toArray']);
  const registry=new Map(ledger.declarations.map(d=>[d.id,d]));
  for(const member of symbol('./jsx','Children').valueShape.members){
    assert(member.declarations.some(id=>registry.get(id).source==='src/jsx/children.ts'));
    assert.equal(member.evidence.sourceConnection,'absent');
  }
  for(const entry of ['./jsx','./jsx/dom'])assert(symbol(entry,'default').valueShape.members.some(m=>m.name==='Children'));
  assert.deepEqual(symbol('./jsx/dom/client','default').valueShape.members.map(m=>m.name),['createRoot','hydrateRoot']);
  assert.deepEqual(symbol('./jsx/dom/server','default').valueShape.members.map(m=>m.name),['renderToReadableStream','renderToString','version']);
});

test('dependency closure includes private/type dependencies and imported tests, not filename guesses',()=>using({
  'src/index.ts':'export {run} from "./middle";',
  'src/middle.ts':'import {leaf} from "./leaf";import type {T} from "./types"; export const run=(x:T)=>leaf(x);',
  'src/leaf.ts':'export const leaf=(x:unknown)=>x;',
  'src/types.ts':'export interface T {}',
  'src/unrelated.test.ts':'import {run} from "./index";run({});'
},f=>{
  const result=f.scan();assert.deepEqual(result.exports[0].conservativeSourceDependencies,['src/index.ts','src/leaf.ts','src/middle.ts','src/types.ts']);
  assert(result.modules.every(m=>m.upstreamTests.includes('src/unrelated.test.ts')));
  assert.equal(result.modules.find(m=>m.source==='src/types.ts').classification,'erased_type_only');
}));

test('ambient declarations are classified without attempting JS emission',()=>using({
  'src/index.ts':'export type {External} from "./ambient";',
  'src/ambient.d.ts':'export declare class External {method():void}'
},f=>{const r=f.scan();assert.equal(r.exports[0].symbols[0].classification,'type_only');assert.equal(r.modules.find(m=>m.source.endsWith('.d.ts')).classification,'erased_type_only');}));

test('self-package subpaths resolve through exports rather than guessed source layout',()=>using({
  'src/index.ts':'export {special} from "hono/special";',
  'src/preset/nested.ts':'export const special=1;',
  'src/preset.test.ts':'import {special} from "hono/special";'
},f=>{
  const entries=[...entry('src/index.ts'),{entryPoint:'./special',exportPattern:'./special',source:'src/preset/nested.ts',targets:{import:'./dist/preset/nested.js'}}];
  const r=scanProject(f.root,f.list,parser.ts,entries);
  assert.equal(r.exports[0].symbols[0].classification,'runtime');
  assert(r.upstreamTests[0].conservativeSourceDependencies.includes('src/preset/nested.ts'));
}));

test('missing relative imports and syntax errors fail closed',()=>{
  using({'src/index.ts':'export {nope} from "./absent"'},f=>assert.throws(()=>f.scan(),/Unresolved\/out-of-scope internal/));
  using({'src/index.ts':'export const x = ;'},f=>assert.throws(()=>f.scan(),/syntax errors/));
});

test('nonliteral imports, proxies and absent external types stay explicit gaps',()=>using({
  'src/index.ts':'import type {Unknown} from "missing-package";export const open=(name:string)=>import(name);export const proxy=new Proxy({},{});export const x:Unknown={};'
},f=>{const r=f.scan();assert(r.gaps.some(g=>g.kind==='unresolved_dynamic_import'));assert(r.gaps.some(g=>g.kind==='proxy_generated_api'));assert(r.gaps.some(g=>g.kind==='external_import_contract'));assert(r.diagnostics.length);}));

test('pin, tracked bytes and untracked files are guarded; generation is deterministic',()=>using({
  'package.json':JSON.stringify({name:'fixture',version:'0.0.0',exports:{'.':{import:'./dist/index.js'}}}),
  'src/index.ts':'export const sample=(x:string)=>x;\n'
},f=>{
  const git=(...args)=>execFileSync('git',['-C',f.root,...args],{encoding:'utf8'}).trim();
  git('init','-q');git('config','user.name','Inventory fixture');git('config','user.email','fixture@example.invalid');git('add','.');git('-c','commit.gpgsign=false','commit','-qm','fixture');
  const target={repository:'fixture',revision:git('rev-parse','HEAD')};
  verifyCheckout(f.root,target);assert.throws(()=>verifyCheckout(f.root,{...target,revision:'0'.repeat(40)}),/not pinned/);
  const a=generate(f.root,target,parser),b=generate(f.root,target,parser);assert.deepEqual(a,b);
  assert.equal(a.summary.sourceConnectedTheorems,0);assert(a.declarations.every(d=>d.id&&d.sha256));
  const output=path.join(os.tmpdir(),'hono-coverage-fixture-'+path.basename(f.root)+'.json');
  try{assert.throws(()=>writeOrCheck(output,a,true),/stale/);writeOrCheck(output,a,false);writeOrCheck(output,a,true);fs.appendFileSync(output,' ');assert.throws(()=>writeOrCheck(output,a,true),/stale/);}finally{fs.rmSync(output,{force:true});}
  fs.writeFileSync(path.join(f.root,'stray.txt'),'unexpected');assert.throws(()=>verifyCheckout(f.root,target),/untracked/);fs.unlinkSync(path.join(f.root,'stray.txt'));
  fs.appendFileSync(path.join(f.root,'src/index.ts'),'\nexport const changed=1;');assert.throws(()=>verifyCheckout(f.root,target),/clean/);
  git('checkout','--','src/index.ts');fs.writeFileSync(path.join(f.root,'.gitattributes'),'*.ts text eol=crlf\n');git('add','.gitattributes');git('-c','commit.gpgsign=false','commit','-qm','line endings');
  fs.writeFileSync(path.join(f.root,'src/index.ts'),fs.readFileSync(path.join(f.root,'src/index.ts'),'utf8').replace(/\n/g,'\r\n'));
  git('add','src/index.ts'); // Refresh the index's conversion/stat metadata; normalized Git bytes stay LF.
  assert(fs.readFileSync(path.join(f.root,'src/index.ts'),'utf8').includes('\r\n'));
  assert.equal(git('status','--porcelain'),'');assert.throws(()=>verifyCheckout(f.root,{...target,revision:git('rev-parse','HEAD')}),/Working bytes differ/);
}));
