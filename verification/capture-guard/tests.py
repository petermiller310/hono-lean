#!/usr/bin/env python3
"""Exact-source guarded captures: descriptor/prototype cases and faults."""
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
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve()
NODE=os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE=(ROOT/'verification/capture-guard/full.ts.txt').read_text()

def units(text): return [int.from_bytes(text.encode('utf-16-le',errors='surrogatepass')[i:i+2],'little') for i in range(0,len(text.encode('utf-16-le',errors='surrogatepass')),2)]
def tag(kind,**fields): return dict(kind=kind,**fields)
U,N=tag('undefined'),tag('null')
S=lambda value:tag('string',units=value)
A=lambda ref:tag('array',ref=ref)
O=lambda ref:tag('object',ref=ref)
NUM=lambda value:tag('number',value=value)

def data(key,value=NUM(7),writable=True,enumerable=True,configurable=True):
    return dict(key=key,kind='data',value=value,writable=writable,enumerable=enumerable,configurable=configurable)

def accessor(key,getter='unsupported',setter='missing',enumerable=False,configurable=False):
    return dict(key=key,kind='accessor',getter=getter,setter=setter,enumerable=enumerable,configurable=configurable)

def obj(own=None,prototype=None,extensible=True):
    return dict(own=own or [],prototype=prototype,extensible=extensible)

def fixture(key,own=None,inherited=None,depth=0,extensible=True,capture=None,m=True):
    capture=[97,108,112,104,97] if capture is None else capture
    other=[120] if key!=[120] else [121]
    objects=[obj([data([102],S([102,114,97,109,101]))]),
             obj([data(other,O(0),False,False,False)]+([own] if own else []),2 if depth else None,extensible)]
    for at in range(depth):
        objects.append(obj(([inherited] if inherited and at==depth-1 else []),at+3 if at+1<depth else None))
    result=dict(objects=objects,params=1,name=key,heap=[[S(capture),S([122])],[O(0),A(0)]])
    if m: result['m']=A(0)
    return result

def normalize(result):
    result=copy.deepcopy(result)
    for object in result.get('objects',[]): object['own'].sort(key=lambda field:tuple(field['key']))
    for field in ['getterCalls','setterCalls','wrapperSha256']: result.pop(field,None)
    return result

def oracle(case):
    """Initial descriptor search and independent outcome table, no source eval."""
    objects=copy.deepcopy(case['objects']); key=case['name']; target=objects[case['params']]
    own=lambda object:next((field for field in object['own'] if field['key']==key),None)
    if own(target) is not None:
        return normalize(dict(ok=True,objects=objects,heap=case['heap'],scope=True))
    m=case.get('m',U)
    if m['kind']!='array': return dict(ok=False)
    row=case['heap'][m['ref']]; value=row[0] if row else U
    # Main admitted absent-domain contexts supply a primitive string capture.
    assert value['kind']=='string'
    descriptor=None; current=case['params']; visited=set()
    while current is not None:
        assert current not in visited; visited.add(current)
        descriptor=own(objects[current])
        if descriptor is not None: break
        current=objects[current]['prototype']
    if descriptor and descriptor['kind']=='accessor':
        if descriptor['setter']!='prototype': return dict(ok=False)
    else:
        if descriptor and not descriptor['writable']: return dict(ok=False)
        if not target['extensible']: return dict(ok=False)
        target['own'].append(data(key,value))
    return normalize(dict(ok=True,objects=objects,heap=case['heap'],scope=True))

def own_cases():
    result=[]
    keys=[units(key) for key in ['id','__proto__','constructor','','0','01','hasOwn','toString']]
    values=[U,N,tag('bool',value=False),NUM(0),S([]),S([55296,0,56320]),O(0),A(1)]
    for key in keys:
        descriptors=[data(key,value,*flags) for value,flags in zip(values,[(False,False,False),(True,False,True),(False,True,False),(True,True,True)]*2)]
        descriptors += [accessor(key,getter,setter) for getter,setter in itertools.product(['missing','prototype','unsupported'],['missing','prototype'])]
        for descriptor,extensible,mode in itertools.product(descriptors,[False,True],['absent','null','array']):
            case=fixture(key,descriptor,depth=2,extensible=extensible,m=mode!='absent')
            if mode=='null': case['m']=N
            result.append(case)
    return result

def absent_cases():
    result=[]
    keys=[units(key) for key in ['id','__proto__','constructor','','0','01']]+[[55296,0,56320],[55357,56832]]
    for key in keys:
        descriptors=[None,data(key,U),data(key,NUM(0),False),data(key,O(0),True,False,False),
                     accessor(key,'unsupported','prototype'),accessor(key,'prototype','missing'),accessor(key,'missing','unsupported')]
        for descriptor,extensible,depth,capture in itertools.product(descriptors,[False,True],[1,3,8,31],[[],[55296,47,56320,0]]):
            result.append(fixture(key,inherited=descriptor,depth=depth,extensible=extensible,capture=capture))
        for extensible in [False,True]: result.append(fixture(key,extensible=extensible))
    rng=random.Random(7219)
    for _ in range(100):
        key=[rng.choice([0,47,97,55296,56320]) for _ in range(rng.randrange(7))]
        result.append(fixture(key,inherited=data(key,NUM(0),bool(rng.randrange(2))),depth=rng.randrange(1,9),
                              extensible=bool(rng.randrange(2)),capture=[rng.randrange(65536) for _ in range(rng.randrange(9))]))
    return result

def invoke(args,packet=None):
    return subprocess.run(args,cwd=ROOT,env=ENV,text=True,input=None if packet is None else json.dumps(packet),capture_output=True,timeout=300)

def model(packet):
    result=invoke(['lake','env','lean','--run','verification/capture-guard/Driver.lean'],packet)
    if result.returncode: raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)

def native(packet,runtime='bun'):
    result=invoke([runtime,'verification/capture-guard/native.mjs',str(HONO)],packet)
    if result.returncode: raise AssertionError(result.stdout+result.stderr)
    output=json.loads(result.stdout)
    assert output['checkedPinnedBlobs']==315 and output['verified'] is False and output['fragmentTypeErasure'] is False
    return output['results']

class CaptureGuardTests(unittest.TestCase):
    def compare(self,cases,source=SOURCE,runtime='bun'):
        packet=dict(cases=cases,source=source)
        modeled=model(packet);self.assertTrue(modeled['parsed'])
        observed=native(packet,runtime)
        modeled_results=[normalize(result) for result in modeled['results']]
        self.assertEqual([normalize(result) for result in observed],modeled_results)
        if source==SOURCE:
            for result in observed:
                if result['ok']: self.assertEqual((result['getterCalls'],result['setterCalls']),(0,0))
        return modeled_results

    def test_own_descriptor_skips_without_capture_readiness(self):
        cases=own_cases();self.assertEqual(self.compare(cases),[oracle(case) for case in cases])
        print(f'Own-descriptor skip: {len(cases)} contexts, including absent/null m',flush=True)

    def test_absent_descriptor_path_dispatch(self):
        cases=absent_cases();self.assertEqual(self.compare(cases),[oracle(case) for case in cases])
        print(f'Absent/prototype dispatch: {len(cases)} contexts through32 objects',flush=True)

    def test_admitted_source_faults_and_syntax(self):
        key=units('id')
        cases=[fixture(key,own=data(key,S([]))),fixture(key),fixture(units('__proto__'),inherited=accessor(units('__proto__'),'prototype','prototype'),depth=1)]
        expected=[oracle(case) for case in cases]
        faults=[SOURCE.replace('!Object.hasOwn','Object.hasOwn'),SOURCE.replace('Object.hasOwn(params, name)',"Object.hasOwn(params, 'wrong')"),
                SOURCE.replace('params[name] =',"params['wrong'] ="),SOURCE.replace('m[0]','m[1]'),
                SOURCE.replace('m[0]','name'), 'params[name] = m[0]\n']
        for source in faults:
            self.assertTrue(model(dict(cases=[],source=source))['parsed'],source)
            self.assertNotEqual(self.compare(cases,source),expected,source)
        rejected=[SOURCE.replace('params, name','params'),SOURCE.replace('params, name','params, name, m'),
                  SOURCE.replace('hasOwn','unknownMethod'),SOURCE.replace('params, name','params, unknown'),
                  'const Object = params\n'+SOURCE,SOURCE+'callback()\n',SOURCE+'/* trailing */\n']
        for source in rejected: self.assertFalse(model(dict(cases=[],source=source))['parsed'],source)
        for source in [SOURCE.replace('\n','\r\n'),SOURCE.rstrip()]: self.assertEqual(self.compare(cases,source),expected)

    def test_node_and_native_boundaries(self):
        self.assertIsNotNone(NODE,'Use HONO_NODE or put Node22.22.2 on PATH')
        cases=own_cases()[::41]+absent_cases()[::53]
        self.assertEqual(self.compare(cases,runtime=NODE),[oracle(case) for case in cases])
        shadow=[]
        for binding in [tag('constructor'),N,O(0)]:
            for own in [None,data(units('id'),U)]:
                case=fixture(units('id'),own=own);case['objectBinding']=binding;shadow.append(case)
        outcomes=self.compare(shadow)
        self.assertEqual(outcomes,[oracle(case) if case['objectBinding']['kind']=='constructor' else dict(ok=False) for case in shadow])
        for runtime in ['bun',NODE]:
            result=invoke([runtime,'verification/capture-guard/boundary.mjs',str(HONO)])
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertFalse(json.loads(result.stdout)['verified'])

    def test_source_identity(self):
        checked=invoke(['python3','verification/capture-guard/source.py','--hono',str(HONO)])
        self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            files=['verification/capture-guard/source.py','verification/capture-guard/source.json',
                   *['verification/capture-guard/'+name+'.ts.txt' for name in ['full','guard','assignment','close']],
                   'HonoLean/Upstream/NodeCaptureGuard/Generated.lean']
            for file in files:
                path=root/file;path.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/file,path)
            for file in files[1:]:
                path=root/file;before=path.read_bytes();path.write_bytes(before+b'\n')
                result=invoke(['python3',str(root/files[0]),'--hono',str(HONO)]);self.assertNotEqual(result.returncode,0,file);path.write_bytes(before)
            clone=root/'hono'
            subprocess.run(['git','clone','--quiet','--shared','--no-checkout',str(HONO),str(clone)],check=True,env=ENV)
            subprocess.run(['git','-C',str(clone),'checkout','--quiet','--detach','5ca49b0720755c585c9a9835f0a479ceea36fb52'],check=True,env=ENV)
            path=clone/'src/router/trie-router/node.ts';path.write_bytes(path.read_bytes()+b'\n')
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged','src/router/trie-router/node.ts'],check=True,env=ENV)
            result=invoke(['python3',str(root/files[0]),'--hono',str(clone)]);self.assertNotEqual(result.returncode,0)

    def test_actual_pinned_regexp_routes(self):
        result=invoke(['bun','verification/capture-guard/upstream.mjs',str(HONO)])
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        observed=json.loads(result.stdout)
        self.assertFalse(observed['verified']);self.assertFalse(observed['nativeTypeScriptLoadingVerified'])
        self.assertEqual(observed['checkedPinnedBlobs'],315)
        expected=[]
        for name in ['id','constructor','__proto__']:
            for path in ['/alpha','/123']:
                record=dict(name=name,pattern=f'/:{name}{{[a-z]+}}',path=path,handlers=['capture'] if path=='/alpha' else [])
                if path=='/alpha': record.update(own=True,nullPrototype=True,value=dict(objectPrototype=True) if name=='__proto__' else 'alpha')
                expected.append(record)
        self.assertEqual(observed['records'],expected)

if __name__=='__main__': unittest.main(argv=['capture-guard'])
