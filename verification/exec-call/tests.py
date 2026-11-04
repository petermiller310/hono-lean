#!/usr/bin/env python3
"""Finite exact156 ordinary-current-callee evidence; builtin regex stays open."""
import argparse
import copy
import itertools
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--hono',type=Path,required=True);HONO=p.parse_args().hono.resolve()
NODE=os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE=(ROOT/'verification/exec-call/full.ts.txt').read_text()
def units(s):
 raw=s.encode('utf-16-le',errors='surrogatepass');return [int.from_bytes(raw[i:i+2],'little') for i in range(0,len(raw),2)]
def tag(kind,**fields):return dict(kind=kind,**fields)
U,N=tag('undefined'),tag('null')
S=lambda x:tag('string',units=x)
O=lambda x:tag('object',ref=x)
A=lambda x:tag('array',ref=x)
F=lambda x:tag('function',ref=x)
NUM=lambda x:tag('number',value=x)
def truthy(v):return v['kind'] not in ['null','undefined'] and not(v['kind'] in ['bool','number'] and not v['value']) and not(v['kind']=='string' and not v['units'])
def data(k,v):return dict(key=units(k),kind='data',value=copy.deepcopy(v),writable=True,enumerable=True,configurable=True)
def obj(own=(),prototype=None):return dict(own=list(own),prototype=prototype,extensible=True)
def normalize(r):
 r=copy.deepcopy(r)
 for o in r.get('objects',[]):
  if 'own'in o:o['own'].sort(key=lambda f:f['key'])
 return r
def invoke(command,packet=None):
 r=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=ROOT,env=ENV,text=True,capture_output=True,timeout=120)
 if r.returncode:raise AssertionError(r.stdout+r.stderr)
 return json.loads(r.stdout)
def model(packet):return invoke(['lake','env','lean','--run','verification/exec-call/Driver.lean'],packet)
def native(packet,engine='bun'):
 r=invoke([engine,'verification/exec-call/native.mjs',str(HONO)],packet)
 assert r['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52' and r['checkedPinnedBlobs']==315
 assert r['verified'] is False
 return r
METHODS={
 'singleton':'exec(input) { return [input] }',
 'argument':'exec(input) { return input }',
 'null':'exec(input) { return null }',
 'receiver':'exec(input) { return this }',
 'empty':'exec(input) { return [] }',
 'fallthrough':'exec(input) {}',
 'zero':'exec(input) { return 0 }',
 'false':'exec(input) { return false }',
 'true':'exec(input) { return true }',
 'capture':'exec(input) { return box.value }',
 'effects':'exec(input) { box.value = input; this.seen = input; return [box.value] }',
 'push':'exec(input) { box.calls.push(input); return box.calls }',
 'normal-effects':'exec(input) { this.seen = input }',
 'private-read':'exec(input) { return this.#secret }',
 'private-write':'exec(input) { this.#secret = input; return this.#secret }',
 'local':'exec(input) { const local = [input]; return local }',
 'has-own':'exec(input) { return Object.hasOwn(this, \'seen\') }',
 'callee':'exec(input) { return this.exec }',
 'error':'exec(input) { return this.missing.value }',
 'error-after-write':'exec(input) { box.value = input; return this.missing.value }',
}
def oracle(case,mode,source=SOURCE):
 """Independent selected program contracts; never runs parser/evaluator/engine."""
 inherited=case.get('inherited',False);kind=case.get('calleeKind','method');handle=case.get('methodHandle',3)
 exec_desc=data('exec',F(handle))
 if kind in ['undefined','number','null']:
  exec_desc=data('exec',{'undefined':U,'number':NUM(7),'null':N}[kind])
 elif kind in ['missingGetter','prototypeGetter']:
  exec_desc=dict(key=units('exec'),kind='accessor',getter='missing' if kind=='missingGetter' else 'prototype',setter='missing',enumerable=True,configurable=True)
 objects=[dict(intrinsic='Object.prototype'),obj([data('other',F(4))]+([] if inherited else [exec_desc]),2),
  obj([data('exec',F(3))] if inherited else []),obj([data('value',case.get('boxValue',S(units('captured')))),data('calls',A(0))]),obj()]
 if 'box.exec'in source:return dict(ok=False)
 other='.other('in source
 if not other and not inherited and kind!='method':return dict(ok=False)
 selected=4 if other else 3 if inherited else handle
 if selected not in [3,4]:return dict(ok=False)  # unknown modeled table handle; native fixtures do not use this branch
 if selected==4:mode='null'
 if mode in ['error','error-after-write']:return dict(ok=False) # rejection projection only; no rollback observation
 value=S(case['input']) if '(restPathString)'in source else O(1)
 heap=[[]];secret=NUM(7)
 def set_field(index,name,v):
  key=units(name);objects[index]['own']=[f for f in objects[index]['own'] if f['key']!=key]+[data(name,v)]
 if mode in ['singleton','effects','local']:
  if mode=='effects':set_field(3,'value',value);set_field(1,'seen',value)
  result=A(1);heap.append([value])
 elif mode=='argument':result=value
 elif mode=='null':result=N
 elif mode=='receiver':result=O(1)
 elif mode=='empty':result=A(1);heap.append([])
 elif mode in ['fallthrough','normal-effects']:
  result=U
  if mode=='normal-effects':set_field(1,'seen',value)
 elif mode=='zero':result=NUM(0)
 elif mode in ['false','has-own']:result=tag('bool',value=False)
 elif mode=='true':result=tag('bool',value=True)
 elif mode=='capture':result=copy.deepcopy(case.get('boxValue',S(units('captured'))))
 elif mode=='push':heap[0].append(value);result=A(0)
 elif mode=='private-read':result=secret
 elif mode=='private-write':secret=value;result=secret
 elif mode=='callee':result=F(3 if inherited else handle)
 else:raise ValueError(mode)
 name='result' if 'const result ='in source else 'm'
 m=result if name=='m' else O(4)
 return normalize(dict(ok=True,declaredName=name,declaredValue=result,m=m,guard=truthy(m),heap=heap,objects=objects,secret=secret,scope=True))
def contexts():
 inputs=[units(s) for s in ['', '/', '12','not-digits','/a/b','constructor','__proto__','a\n','\r\n','00']]+[[0],[55296],[56320],[55357,56832],[55296,47,56320],list(range(128))]
 cases=[dict(input=value,inherited=inherit,methodHandle=handle) for value,inherit,handle in itertools.product(inputs,[False,True],[3,4])]
 for kind in ['undefined','number','null','missingGetter','prototypeGetter']:
  cases.extend(dict(input=value,calleeKind=kind) for value in inputs[:5])
 vals=[U,N,tag('bool',value=False),tag('bool',value=True),NUM(0),NUM(-17),S([]),S([55296,0,56320]),A(0),O(0),O(1),O(3),O(4),F(3),F(4),tag('constructor')]
 cases += [dict(input=[49,50],boxValue=v) for v in vals]
 rng=random.Random(1562025)
 for i in range(16):cases.append(dict(input=[rng.randrange(65536) for _ in range(i*3)],inherited=bool(i%2)))
 return cases
class Checks(unittest.TestCase):
 def assert_results(self,actual,expected):
  self.assertEqual(len(actual),len(expected))
  for i,(a,b)in enumerate(zip(actual,expected)):
   with self.subTest(context=i):self.assertEqual(normalize(a),b)
 def test_01_identity_and_tampering(self):
  r=subprocess.run(['python3','verification/exec-call/source.py','--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True);self.assertEqual(r.returncode,0,r.stdout+r.stderr)
  with tempfile.TemporaryDirectory()as tmp:
   root=Path(tmp);(root/'verification').mkdir();(root/'HonoLean/Upstream').mkdir(parents=True)
   shutil.copytree(ROOT/'verification/exec-call',root/'verification/exec-call');shutil.copytree(ROOT/'HonoLean/Upstream/NodeExecCall',root/'HonoLean/Upstream/NodeExecCall')
   f=root/'verification/exec-call/full.ts.txt';f.write_text(f.read_text().replace('.exec(','.other('))
   r=subprocess.run(['python3',str(root/'verification/exec-call/source.py'),'--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True);self.assertNotEqual(r.returncode,0)
 def test_02_body_computations_and_effects(self):
  cases=contexts()
  for mode,method in METHODS.items():
   with self.subTest(method=mode):
    packet=dict(methodSource=method,cases=cases);expected=[oracle(c,mode)for c in cases]
    m=model(packet);self.assertTrue(m['parsed']);self.assert_results(m['results'],expected)
    for engine in ['bun',NODE]:self.assert_results(native(packet,engine)['results'],expected)
  print(f'{len(cases)}contexts x{len(METHODS)}genuine method bodies: model/oracle/Bun/Node')
 def test_03_admitted_source_faults(self):
  cases=[dict(input=[49,50]),dict(input=[],inherited=True)]
  faults=[SOURCE.replace('.exec(','.other('),SOURCE.replace('(restPathString)','(matcher)'),SOURCE.replace('const m =','const result ='),SOURCE.replace('matcher.exec','box.exec')]
  base=[oracle(c,'singleton')for c in cases]
  for source in faults:
   packet=dict(source=source,cases=cases);expected=[oracle(c,'singleton',source)for c in cases];self.assertNotEqual(expected,base)
   m=model(packet);self.assertTrue(m['parsed']);self.assert_results(m['results'],expected)
   for engine in ['bun',NODE]:self.assert_results(native(packet,engine)['results'],expected)
 def test_04_parser_boundaries(self):
  for source in ['const m = matcher.exec()','const m = matcher.exec(restPathString, restPathString)',
   'const m = matcher.exec(++restPathString)','const m = matcher.exec(m)','const m = matcher.exec(restPathString); const x = m']:
   self.assertEqual(model(dict(source=source,cases=[])),dict(parsed=False))
  for method in ['#exec(input) { return input }','exec = (input) => { return input }','exec(input: string) { return input }',
   'exec(input,other) { return input }','exec(input) { return arguments }','exec(input) { return super.exec(input) }','exec(input) { box = input }']:
   self.assertEqual(model(dict(methodSource=method,cases=[])),dict(parsed=False))
 def test_05_native_boundaries(self):
  for engine in ['bun',NODE]:
   r=invoke([engine,'verification/exec-call/boundary.mjs',str(HONO)]);self.assertFalse(r['verified'])
   self.assertEqual(r['checkedPinnedBlobs'],315);self.assertEqual(r['sourceBytes'],51)
   self.assertTrue(r['plainJavaScript']);self.assertFalse(r['typescriptErasure'])
   b=r['outsideDomain'];self.assertEqual(b['duringArgumentExecWrite'],['argument-write','old','new'])
   self.assertEqual(b['noncallableArgumentEvents'],['argument']);self.assertEqual(b['nullBaseArgumentEvents'],[])
   self.assertEqual(b['throwingGetterEvents'],['get']);self.assertEqual(b['partialFailure'],dict(effects=['effect'],boxValue='changed'))
   self.assertTrue(b['builtinRegex']['noncallableHasNoFallback']);self.assertEqual(b['builtinRegex']['lastIndex'],17)
 def test_06_unsupported_nested_member_is_frontend_refusal(self):
  # Nested block-member dispatch is outside this projected method grammar.
  # Native success is retained separately; parser refusal is NOT a TypeError.
  packet=dict(methodSource='exec(input) { return this.other() }',cases=[dict(input=[49,50])])
  self.assertEqual(model(packet),dict(parsed=False))
  for engine in ['bun',NODE]:
   r=native(packet,engine)['results'][0];self.assertTrue(r['ok'])
   self.assertEqual(r['declaredValue'],N);self.assertEqual(r['m'],N);self.assertFalse(r['guard'])
if __name__=='__main__':unittest.main(argv=['exec-call'],verbosity=2)
