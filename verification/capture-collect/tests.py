#!/usr/bin/env python3
"""Finite source123→guard158–160→actual161/helper integration evidence."""
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
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--hono',type=Path,required=True)
HONO=p.parse_args().hono.resolve()
NODE=os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE=(ROOT/'verification/capture-collect/full.ts.txt').read_text()
def units(s):
 raw=s.encode('utf-16-le',errors='surrogatepass');return [int.from_bytes(raw[i:i+2],'little') for i in range(0,len(raw),2)]
def run(command,packet=None):
 r=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=ROOT,env=ENV,text=True,capture_output=True,timeout=120)
 if r.returncode:raise AssertionError(r.stdout+r.stderr)
 return json.loads(r.stdout)
def native(packet,engine='bun'):
 r=run([engine,'verification/capture-collect/native.mjs',str(HONO)],packet)
 assert r['revision']=='5ca49b0720755c585c9a9835f0a479ceea36fb52' and r['checkedPinnedBlobs']==315
 assert r['transpilation']['verified'] is False and r['transpilation']['compiler']=='6.0.3'
 assert all(len(w['inputSha256'])==len(w['emittedSha256'])==64 for w in r['transpilation']['wrappers'])
 return r['results']
def model(packet):return run(['lake','env','lean','--run','verification/capture-collect/Driver.lean'],packet)
def tag(kind,**fields):return dict(kind=kind,**fields)
U=tag('undefined');CTOR=tag('constructor')
def encode(code):
 if isinstance(code,dict):return code
 if code.startswith('r'):return tag('object',ref=4+int(code[1:]))
 return {'u':U,'n':tag('null'),'f':tag('bool',value=False),'z':tag('number',value=0),'empty':tag('string',units=[]),
 't':tag('bool',value=True),'one':tag('number',value=1),'text':tag('string',units=[120]),'ctor':CTOR}[code]
def truthy(value):return value['kind'] not in ['undefined','null'] and not(value['kind'] in ['number','bool'] and not value['value']) and not(value['kind']=='string' and not value['units'])
def descriptor(key,value):return dict(key=list(key),value=copy.deepcopy(value),writable=True,enumerable=True,configurable=True)
def normalized(result):
 result=copy.deepcopy(result)
 for fields in result['allocations']:fields.sort(key=lambda item:item['key'])
 return result
PROTO=tuple(units('__proto__'));CONSTRUCTOR=tuple(units('constructor'))
def oracle(case):
 """Independent map/selection arithmetic; no interpreter/native/parser invocation."""
 parent={tuple(k):encode(v) for k,v in case.get('nodeEntries',[])}
 inherited={tuple(k):encode(v) for k,v in case.get('inheritedNode',[])}
 fresh={} if case.get('shared') else copy.deepcopy(parent)
 name=tuple(case['name'])
 if name not in fresh:
  assert not case.get('missingMatch'),'A skipped own capture is needed for missing m'
  capture=encode(case.get('capture','text'))
  if name!=PROTO:fresh[name]=capture
  else:assert capture['kind']=='string','Only primitive string legacy-ignore in this contract fixture'
 def read_parent(key):
  if key in parent:return parent[key]
  if case.get('ordinaryParent'):
   if key==CONSTRUCTOR:return CTOR
   if key==PROTO:return tag('object',ref=0)
   # Other native Object.prototype names are expressly excluded unless own-shadowed.
  elif inherited:
   if key in inherited:return inherited[key]
   if key==tuple(units('marker')):return tag('string',units=units('prior'))
  return U
 def read_fresh(key):
  if key in fresh:return fresh[key]
  if key==CONSTRUCTOR:return CTOR
  if key==PROTO:return tag('object',ref=0)
  return U
 count=len(case['records']);prior=case.get('priorCount',0)
 collector=[-1]*prior+case.get('priorRecords',[]);record_params=[-1]*count
 allocations=[[descriptor(k,v) for k,v in fresh.items()]]
 for row in case['rows']:
  own={tuple(k):v for k,v in row.get('own',[])};inherited_row={} if row.get('nullPrototype') else dict((tuple(k),v) for k,v in row.get('inherited',[]))
  def selected_read(key):return own.get(key,inherited_row.get(key,'u'))
  selected=selected_read(tuple(case['method']))
  if not truthy(encode(selected)):selected=selected_read(tuple(units('ALL')))
  if not truthy(encode(selected)):continue
  index=int(selected[1:]);collector.append(index);record_params[index]=len(allocations)
  captures={}
  for at,key in enumerate(case['records'][index]):
   key=tuple(key);parameter,node=read_fresh(key),read_parent(key)
   value=parameter if at==0 and truthy(parameter) else parameter if node['kind'] in ['undefined','null'] else node
   captures[key]=value
  allocations.append([descriptor(key,value) for key,value in captures.items()])
 old_length=4+len(case['records'])+2*len(case['rows'])+3
 return normalized(dict(freshParams=tag('object',ref=old_length),collector=collector,recordParams=record_params,
  collectorParams=[record_params[i] if i>=0 else -1 for i in collector],allocations=allocations,nullPrototypes=True,freshOrdinary=True,
  methodsKept=True,keysKept=True,handlerFieldsKept=True,scope=['outer-i','outer-len','outer-handler','outer-key']))
def row(*fields,inherited=(),null=False):return dict(own=[[units(k),v] for k,v in fields],inherited=[[units(k),v] for k,v in inherited],nullPrototype=null)
def fixture(keys=('id','name'),**kwargs):
 result=dict(method=units('GET'),records=[[units(k) if isinstance(k,str) else k for k in keys]],rows=[row(('GET','r0'))],
 nodeEntries=[[units('id'),'text']],name=units('name'),capture='text',ordinaryParent=True)
 result.update(kwargs);return result
def contexts():
 cases=[];keys=['id','name','__proto__','constructor','',[55296,0,56320],[55357,56832]]
 for pair,shared,ordinary in itertools.product(itertools.permutations(keys,2),[False,True],[False,True]):
  c=fixture(pair,shared=shared,ordinaryParent=ordinary)
  for capture in ['text','empty']:
   d=copy.deepcopy(c);d['capture']=capture;cases.append(d)
 for key,value,ordinary in itertools.product(keys,['u','n','f','z','empty','t','one','text','ctor','r0'],[False,True]):
  k=units(key) if isinstance(key,str) else key
  cases.append(fixture([k,units('name')],nodeEntries=[[k,value]],ordinaryParent=ordinary,name=k,missingMatch=True))
 for prior,rows,method in itertools.product([0,1,3],[[],[row(('GET','r0')),row(('ALL','r0'))],
  [row(('GET','z'),('ALL','r0')),row(('GET','r0')),row(('GET','f'))],
  [row(inherited=[('GET','r0')]),row(('GET','r0')),row(('GET','n'),inherited=[('ALL','r0')])]],['GET','POST','ALL']):
  cases.append(fixture(priorCount=prior,rows=rows,method=units(method)))
 # Unequal and equal branch identities, inherited parent data, missing/skipped m,
 # separate records, long snapshots, repeated same-record rows and UTF16 names.
 cases += [fixture(shared=True,nodeEntries=[[units('id'),'text']]),
  fixture(inheritedNode=[[units('id'),'f']],ordinaryParent=False,nodeEntries=[]),
  fixture(inheritedNode=[[units('name'),'empty']],ordinaryParent=False,nodeEntries=[]),
  fixture(['constructor','name'],nodeEntries=[],name=units('constructor')),
  fixture(['id','constructor'],nodeEntries=[[units('id'),'text']],name=units('constructor')),
  fixture(priorCount=2,priorRecords=[0,0],rows=[row(('GET','r0')),row(('ALL','r0')),row(('GET','r0'))])]
 rng=random.Random(161123)
 for index in range(210):
  chosen=rng.sample(keys,rng.randint(0,5));count=rng.randint(1,3)
  records=[[units(k) if isinstance(k,str) else k for k in chosen] for _ in range(count)]
  rows=[row((rng.choice(['GET','POST','ALL']),f'r{rng.randrange(count)}')) for _ in range(rng.randint(0,8))]
  cases.append(fixture(chosen,records=records,rows=rows,method=units(rng.choice(['GET','POST','ALL'])),shared=bool(index%2),priorCount=index%4))
 return cases
class Checks(unittest.TestCase):
 def assert_results(self,actual,expected):
  self.assertEqual(len(actual),len(expected))
  for index,(observed,wanted) in enumerate(zip(actual,expected)):
   with self.subTest(context=index):self.assertEqual(normalized(observed),wanted)
 def test_01_source_identity_and_tampering(self):
  result=subprocess.run(['python3','verification/capture-collect/source.py','--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True)
  self.assertEqual(result.returncode,0,result.stdout+result.stderr)
  with tempfile.TemporaryDirectory() as folder:
   path=Path(folder);(path/'verification').mkdir();shutil.copytree(ROOT/'verification/capture-collect',path/'verification/capture-collect')
   (path/'HonoLean/Upstream').mkdir(parents=True);shutil.copytree(ROOT/'HonoLean/Upstream/NodeCaptureCollect',path/'HonoLean/Upstream/NodeCaptureCollect')
   target=path/'verification/capture-collect/call.ts.txt';target.write_text(target.read_text().replace('node.#params, params','params, node.#params'))
   bad=subprocess.run(['python3',str(path/'verification/capture-collect/source.py'),'--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True)
   self.assertNotEqual(bad.returncode,0)
 def test_02_source_maps_and_live_aliases(self):
  cases=contexts();packet=dict(cases=cases);expected=[oracle(c) for c in cases]
  self.assert_results(model(packet),expected)
  for engine in ['bun',NODE]:self.assert_results(native(packet,engine),expected)
  print(f'{len(cases)} source123+guard+161 contexts; Bun/Node/model/oracle agree')
 def test_03_admitted_source_faults(self):
  cases=[fixture(['id','constructor'],name=units('constructor')),fixture(['id','name'],nodeEntries=[[units('name'),'one']]),
   fixture(['id','name'],nodeEntries=[],shared=True)]
  faults=[SOURCE.replace('node.#params, params','params, node.#params'),SOURCE.replace('!Object.hasOwn','Object.hasOwn'),
   SOURCE.replace('m[0]','m[1]'),SOURCE.replace('node.#params, params','node.#params, null')]
  base=[oracle(c) for c in cases];self.assertEqual(len(faults),4)
  for fault in faults:
   self.assertNotEqual(fault,SOURCE);packet=dict(cases=cases,source=fault)
   actual=[normalized(r) for r in model(packet)];self.assertNotEqual(actual,base)
   for engine in ['bun',NODE]:self.assertEqual([normalized(r) for r in native(packet,engine)],actual)
 def test_04_intrinsic_function_is_visible(self):
  c=fixture(['id','constructor'],name=units('constructor'));expected=oracle(c)
  for engine in ['bun',NODE]:
   result=normalized(native(dict(cases=[c]),engine)[0]);self.assertEqual(result,expected)
   self.assertIn(dict(key=units('constructor'),value=CTOR,writable=True,enumerable=True,configurable=True),result['allocations'][1])
 def test_05_boundaries(self):
  for engine in ['bun',NODE]:
   result=run([engine,'verification/capture-collect/boundary.mjs',str(HONO)])
   self.assertFalse(result['verified']);self.assertTrue(result['source161KeepsParentFourthAndLocalFifth'])
   self.assertTrue(result['rootDescriptorsUnchanged']);self.assertEqual(len(result['outsideDomain']['inheritedMethods']),6)
 def test_06_pinned_router(self):
  result=run(['bun','verification/capture-collect/upstream.mjs',str(HONO)])
  self.assertFalse(result['verified']);self.assertEqual(result['queryCount'],19)
  self.assertTrue(result['constructorSecondIsObjectFunction']);self.assertTrue(result['constructorJsonOmitted'])
  self.assertTrue(result['reverseOrderPositive']);self.assertTrue(result['repeatedQueriesKeepEarlierReturnedMap'])
if __name__=='__main__':unittest.main(argv=['capture-collect'],verbosity=2)
