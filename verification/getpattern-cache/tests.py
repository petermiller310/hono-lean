#!/usr/bin/env python3
"""Actual cache control vs independent visible identity/descriptor history contract."""
import argparse
import copy
import itertools
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from oracle import U,string,units,key,history
ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--hono',type=Path,required=True);args=p.parse_args();HONO=args.hono.resolve()
ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0');NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/getpattern-cache/full.ts.txt').read_text();BLOCK=(ROOT/'verification/getpattern-cache/block.ts.txt').read_text()
def invoke(command,packet=None,root=ROOT,check=True):
 r=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=root,env=ENV,text=True,capture_output=True,timeout=180)
 if check and r.returncode:raise AssertionError(r.stdout+r.stderr)
 return r

def model(packet):return json.loads(invoke(['lake','env','lean','--run','verification/getpattern-cache/Driver.lean'],packet).stdout)
def native(packet,engine):
 data=json.loads(invoke([engine,'verification/getpattern-cache/native-main.mjs',str(HONO)],packet).stdout)
 assert data['checkedPinnedBlobs']==315 and data['verified']is False and data['observerVerified']is False
 assert data['hiddenAllocationsObserved']is False and data['typescriptInitializationObserved']is False and data['closureBootstrapVerified']is False
 return data['results']
def project_errors(observations):
 # Keep exception class separately checked; this is a normal/failure projection,
 # not a model/native exception-name or partial-state theorem.
 return [[{'ok':False}if not step['ok']else step for step in case]for case in observations]
def step(label,next_value=U):return dict(label=units(label),next=next_value)
def seeded(label,next_value,value,**flags):return dict(key=key(units(label),next_value),value=value,**flags)

def warm_cases():
 values=[{'kind':'bool','value':True},{'kind':'number','value':1},{'kind':'number','value':-7},string(units('cached')),string([55296,0]),
  {'kind':'array','ref':0},{'kind':'array','ref':1}]+[{'kind':'object','ref':i}for i in range(4)]+[{'kind':'function','ref':6}]
 cases=[]
 for label,next_value,value,owner in itertools.product([':id',':id{(}',':i\nd',':名'],[U,string([]),string(units('undefined')),string(units('next'))],values,['seed','inherited']):
  cases.append({owner:[seeded(label,next_value,value,writable=False,enumerable=False,configurable=False)],'extensible':False,'constructorKind':'number','steps':[step(label,next_value)]})
 return cases

def cold_cases():
 cases=[];falsy=[U,{'kind':'null'},{'kind':'bool','value':False},{'kind':'number','value':0},string([])]
 for name,next_value,value,owner,writable,extensible in itertools.product(['id','constructor','__proto__','名','\ud800\x00\udc00'],
      [U,string([]),string(units('next')),string(units('undefined'))],falsy,['seed','inherited'],[False,True],[False,True]):
  label=':'+name
  cases.append({owner:[seeded(label,next_value,value,writable=writable,enumerable=False,configurable=False)],'extensible':extensible,
                'constructorKind':'number','steps':[step(label,next_value)]})
 for name,next_value,extensible in itertools.product(['id','a#b','i\nj'],[U,string(units('x'))],[False,True]):
  cases.append(dict(extensible=extensible,constructorKind='number',steps=[step(':'+name,next_value)]))
 return cases

def history_cases():
 events=[step(':id'),step(':id',string(units('undefined'))),step(':a#b',string(units('c'))),step(':a',string(units('b#c'))),step(':z',string([])),step('bad')]
 cases=[dict(constructorKind='number',steps=list(steps))for length in range(4)for steps in itertools.product(events,repeat=length)]
 cases.append(dict(constructorKind='number',steps=[step(':id',string(units('{(}#undefined'))),step(':id#{(}'),step(':id#{(}')]))
 return cases

def terminal_cases():
 safe=list(range(48,58))+list(range(65,91))+list(range(97,123));cases=[]
 for lo,hi in itertools.product(safe,safe):
  if lo<=hi:cases.append(dict(steps=[dict(label=[58,105,100,123,91,lo,45,hi,93,43,125],next=U)]))
 for next_value in [U,string([]),string(units(':next')),string(units('*tail'))]:
  cases.append(dict(steps=[step(':id{[0-9]+}',next_value),step(':id{[0-9]+}',next_value)]))
 cases.append(dict(steps=[step(':id{[0-9]+}'),step(':id{[0-9]+}',string(units('undefined')))]))
 return cases

class Checks(unittest.TestCase):
 def check_cases(self,cases,block=False,source=None,expected=None):
  packet=dict(mode='block'if block else'full',cases=cases,source=source or(BLOCK if block else SOURCE))
  expected=expected if expected is not None else[history(c,block)for c in cases]
  result=model(packet);self.assertTrue(result['parsed']);self.assertEqual(result['results'],expected)
  for engine in ['bun',NODE]:
   actual=native(packet,engine)
   for row in actual:
    for event in row:
     if not event['ok']:self.assertEqual(event['errorName'],'TypeError')
   self.assertEqual(project_errors(actual),expected)
 def test01_warm_any_truthy(self):
  cases=warm_cases();self.assertEqual(len(cases),384);self.check_cases(cases)
  # The exact440B warm block need not read any supplied match at all.
  self.check_cases(cases[:48],block=True)
 def test02_falsy_and_strict_descriptors(self):
  cases=cold_cases();self.assertEqual(len(cases),812);self.check_cases(cases)
 def test03_persistent_histories_and_collisions(self):
  cases=history_cases();self.assertEqual(len(cases),260);self.check_cases(cases)
 def test04_terminal_constructor_and_miss(self):
  cases=terminal_cases();self.assertEqual(len(cases),1958);self.check_cases(cases)
  cases=[dict(cacheKind='undefined',constructorKind='number',steps=[step(label,{'kind':'object','ref':0})])for label in ['','id',':',':{}',':id{}',':id{a\nb}',':id{a}\n']]
  self.check_cases(cases)
 def test05_primitive_key_conversions(self):
  next_values=[U,{'kind':'null'},{'kind':'bool','value':False},{'kind':'bool','value':True}]+[{'kind':'number','value':n}for n in [-9007199254740991,-7,0,17,9007199254740991]]
  cases=[dict(constructorKind='number',steps=[step(':id',n),step(':id',n)])for n in next_values]
  self.check_cases(cases)
 def test06_supported_source_faults(self):
  fixture=dict(constructorKind='number',steps=[step(':id')]);original=history(fixture);faults=[]
  expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][2]={'kind':'bool','value':False}
  faults.append((SOURCE.replace('[label, match[1], true]','[label, match[1], false]'),expected))
  expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][1]=string(units(':id'))
  faults.append((SOURCE.replace('[label, match[1], true]','[label, match[0], true]'),expected))
  expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][0]=string(key(units(':id'),U))
  faults.append((SOURCE.replace('[label, match[1], true]','[cacheKey, match[1], true]'),expected))
  expected=[dict(ok=True,value=U,cache=dict(own=[],prototype='Object.prototype',extensible=True),visibleGraph=[],oldFrames=True)]
  faults.append((SOURCE.replace('if (!patternCache[cacheKey])','if (patternCache[cacheKey])'),expected))
  expected=copy.deepcopy(original);expected[0]['value']=U;expected[0]['cache']['own'][0]['key']=units(':id')
  faults.append((SOURCE.replace('patternCache[cacheKey] = [label, match[1], true]','patternCache[label] = [label, match[1], true]'),expected))
  expected=copy.deepcopy(original);expected[0]['cache']['own'][0]['value']={'kind':'reference','id':'r1'}
  expected[0]['visibleGraph']=[dict(id='r0',kind='array',values=[string(units(':id')),string(units('id')),U]),
                             dict(id='r1',kind='array',values=[string(units(':id')),string(units('id')),{'kind':'bool','value':True}])]
  faults.append((SOURCE.replace('return patternCache[cacheKey]','return match'),expected))
  self.assertEqual(len(faults),6)
  for source,expected in faults:
   self.assertNotEqual(source,SOURCE);self.assertNotEqual(expected,original)
   self.check_cases([fixture],source=source,expected=[expected])

 def test07_source_and_artifact_identity(self):
  invoke(['python3','verification/getpattern-cache/source.py','--hono',str(HONO)])
  with tempfile.TemporaryDirectory(prefix='cache-identity-')as directory:
   root=Path(directory);target=root/'verification/getpattern-cache';target.mkdir(parents=True)
   for file in ['source.py','source.json','full.ts.txt','block.ts.txt','init.ts.txt','key.ts.txt','guard.ts.txt','plain.ts.txt','return.ts.txt']:shutil.copyfile(ROOT/'verification/getpattern-cache'/file,target/file)
   dependency=root/'verification/label-match';dependency.mkdir();shutil.copyfile(ROOT/'verification/label-match/full.ts.txt',dependency/'full.ts.txt')
   generated=root/'HonoLean/Upstream/PatternCache';generated.mkdir(parents=True);shutil.copyfile(ROOT/'HonoLean/Upstream/PatternCache/Generated.lean',generated/'Generated.lean')
   command=['python3',str(target/'source.py'),'--hono',str(HONO)];invoke(command,root=root)
   for file in [target/'full.ts.txt',target/'init.ts.txt',target/'block.ts.txt',target/'source.json',generated/'Generated.lean']:
    old=file.read_bytes();file.write_bytes(old+b' ');self.assertNotEqual(invoke(command,root=root,check=False).returncode,0);file.write_bytes(old)
   invoke(command,root=root)
 def test08_native_effect_and_domain_controls(self):
  evidence=json.loads((ROOT/'verification/getpattern-cache/control-evidence.json').read_text())
  self.assertFalse(evidence['verified']);self.assertTrue(evidence['nativeOnly']);self.assertEqual(len(evidence['records']),2)
  for engine,record in zip(['bun',NODE],evidence['records']):
   actual=json.loads(invoke([engine,'verification/getpattern-cache/native-controls.mjs',str(HONO)]).stdout)
   self.assertEqual(actual,record);self.assertEqual(len(actual['results']),6)
  # The retained cold lookahead AST reaches a grammar-domain refusal here;
  # the same native source is valid and succeeds. Never classify this as a
  # native SyntaxError or allowlist it as an ordinary conformance agreement.
  packet=dict(cases=[dict(steps=[step(':id{[0-9]+}',string(units('next')))])])
  result=model(packet);self.assertTrue(result['parsed']);self.assertEqual(result['results'],[[{'ok':False}]])
  for engine in ['bun',NODE]:
   result=native(packet,engine)[0][0];self.assertTrue(result['ok'])
   self.assertEqual(result['visibleGraph'][0]['values'][0],string(key(units(':id{[0-9]+}'),string(units('next')))))
   # Public .source displays an escaped slash; the constructor input and
   # retained source template still contain the original raw slash.
   self.assertEqual(result['visibleGraph'][1]['source'],units(r'^[0-9]+(?=\/next)'))

 def test09_retain_native_preflight(self):invoke(['python3','verification/getpattern-cache/check-native.py','--hono',str(HONO)])
if __name__=='__main__':unittest.main(argv=['getpattern-cache-tests'])
