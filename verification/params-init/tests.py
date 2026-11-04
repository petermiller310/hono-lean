#!/usr/bin/env python3
"""Pinned params initializer: identity branches, shallow copy and source faults."""
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
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve();NODE=os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE=(ROOT/'verification/params-init/full.ts.txt').read_text()

def units(text):
    raw=text.encode('utf-16-le',errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2],'little') for i in range(0,len(raw),2)]
def tag(kind,**fields):return dict(kind=kind,**fields)
U,N=tag('undefined'),tag('null')
S=lambda value:tag('string',units=value)
O=lambda ref:tag('object',ref=ref)
A=lambda ref:tag('array',ref=ref)
NUM=lambda value:tag('number',value=value)
def data(key,value=NUM(7),writable=True,enumerable=True,configurable=True):
    return dict(key=key,kind='data',value=value,writable=writable,enumerable=enumerable,configurable=configurable)
def accessor(key,enumerable=False,getter='unsupported',setter='unsupported'):
    return dict(key=key,kind='accessor',getter=getter,setter=setter,enumerable=enumerable,configurable=False)
def obj(own=None,prototype=None,extensible=True):return dict(own=own or [],prototype=prototype,extensible=extensible)

def fixture(fields=None,shared=False,prototype=4,extensible=True):
    objects=[dict(intrinsicPrototype=True),obj([data(units('node'),NUM(9),False,False,False)],0),obj(),
             obj(copy.deepcopy(fields),prototype,extensible),
             obj([data(units('inherited'),S(units('omit'))),accessor(units('inheritedGetter'),True)],0),
             obj([data(units('frame'),A(0),False,False,False)])]
    if shared:objects[2]=copy.deepcopy(objects[3])
    return dict(objects=objects,heap=[[O(3),O(5)],[A(0),O(0)]],node=1,source=2 if shared else 3,emptyParams=2)

def normalized(result):
    result=copy.deepcopy(result)
    for object in result.get('objects',[]):
        if 'own' in object:object['own'].sort(key=lambda field:tuple(field['key']))
    for field in ['getterCalls','setterCalls']:result.pop(field,None)
    return result

def oracle(case):
    """Independent before-field selection; no parser/interpreter/native call."""
    fields=[]
    if case['source']!=case['emptyParams']:
        source=case['objects'][case['source']]
        for field in source.get('own',[]):
            if field['enumerable']:
                assert field['kind']=='data','Enumerable getter is a separate model-refusal fixture'
                fields.append(data(field['key'],copy.deepcopy(field['value'])))
    result=copy.deepcopy(case['objects'])+[obj(fields,0)]
    return normalized(dict(ok=True,result=O(len(case['objects'])),slot=O(case['source']),scope=True,
                           objects=result,heap=case['heap'],fresh=True))

def shared_cases():
    cases=[]
    for key in [units(value) for value in ['id','__proto__','constructor','','0','01']]+[[55296,0,56320],[55357,56832]]:
        descriptors=[data(key,U,False,True,False),data(key,O(5),True,False,False),
                     accessor(key,True),accessor(key,False)]
        descriptors += [accessor(key,enumerable,getter) for enumerable,getter in
                        itertools.product([False,True],['missing','prototype'])]
        for descriptor,extensible,prototype in itertools.product(descriptors,[False,True],[None,0,4]):
            cases.append(fixture([descriptor],True,prototype,extensible))
    for reference in [0,1]:
        case=fixture(shared=True);case['source']=reference;case['emptyParams']=reference;cases.append(case)
    return cases

def copy_cases():
    cases=[]
    keys=[units(key) for key in ['id','__proto__','constructor','','0','10','01','toString']]+[[55296,0,56320],[55357,56832]]
    values=[U,N,tag('bool',value=False),NUM(0),NUM(-17),NUM(9007199254740991),S([]),S([55296,47,56320]),
            O(0),O(1),O(2),O(3),O(5),A(0),A(1),tag('constructor')]
    for index,(key,value,flags) in enumerate(itertools.product(keys,values,itertools.product([False,True],repeat=3))):
        cases.append(fixture([data(key,value,*flags),accessor(units('hidden_accessor'))],False,
                             prototype=[None,0,4][index%3],extensible=bool((index//3)%2)))
    for reference in [0,1]:
        case=fixture();case['source']=reference;cases.append(case)
    for count in [0,1,64,129,257]:
        fields=[data([60000,index],values[index%len(values)],False,index%3!=0,False) for index in range(count)]
        cases.append(fixture(fields,False,extensible=False))
    equal=fixture([data(units('id'),S(units('same shape')),False,True,False)])
    equal['objects'][2]=copy.deepcopy(equal['objects'][3]);cases.append(equal)
    for getter in ['missing','prototype']:
        cases.append(fixture([data(units('id'),A(0)),accessor(units('hidden'),False,getter,'prototype')]))
    nodeAlias=fixture();nodeAlias['source']=1;nodeAlias['objects'][1]['own']=[data(units('self'),O(1))];cases.append(nodeAlias)
    rng=random.Random(123202)
    for _ in range(120):
        fields=[];seen=set()
        for _ in range(rng.randrange(9)):
            key=tuple(rng.choice([0,47,97,55296,56320]) for _ in range(rng.randrange(6)))
            if key in seen:continue
            seen.add(key)
            if rng.randrange(5)==0:fields.append(accessor(list(key),False))
            else:fields.append(data(list(key),copy.deepcopy(rng.choice(values)),bool(rng.randrange(2)),bool(rng.randrange(2)),bool(rng.randrange(2))))
        cases.append(fixture(fields,False,prototype=[None,0,4][rng.randrange(3)],extensible=bool(rng.randrange(2))))
    return cases

def invoke(args,packet=None):
    return subprocess.run(args,cwd=ROOT,env=ENV,text=True,input=None if packet is None else json.dumps(packet),capture_output=True,timeout=300)
def model(packet):
    result=invoke(['lake','env','lean','--run','verification/params-init/Driver.lean'],packet)
    if result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)
def native(packet,runtime='bun'):
    result=invoke([runtime,'verification/params-init/native.mjs',str(HONO)],packet)
    if result.returncode:raise AssertionError(result.stdout+result.stderr)
    output=json.loads(result.stdout)
    assert output['checkedPinnedBlobs']==315 and output['verified'] is False and output['fragmentTypeErasure'] is False
    assert output['intrinsicPrototypeProjection'] is True
    return output['results']

class ParamsInitTests(unittest.TestCase):
    def compare(self,cases,source=SOURCE,runtime='bun'):
        packet=dict(cases=cases,source=source)
        modeled=model(packet);self.assertTrue(modeled['parsed'])
        observed=native(packet,runtime)
        values=[normalized(value) for value in modeled['results']]
        self.assertEqual([normalized(value) for value in observed],values)
        if source==SOURCE:
            for value in observed:
                if value['ok']:self.assertEqual((value['getterCalls'],value['setterCalls']),(0,0))
        return values

    def test_shared_identity_skips_all_copy_readiness(self):
        cases=shared_cases();self.assertEqual(self.compare(cases),[oracle(case) for case in cases])
        print(f'Shared identity: {len(cases)} contexts, including enumerable throwing accessors',flush=True)

    def test_copy_descriptors_aliases_and_frames(self):
        cases=copy_cases();self.assertEqual(self.compare(cases),[oracle(case) for case in cases])
        print(f'Own DATA copy: {len(cases)} contexts, including long/alias/O0 cases',flush=True)

    def test_admitted_source_faults_and_parser_controls(self):
        cases=[fixture([data(units('id'),S(units('copy')))]),fixture([data(units('id'),NUM(0))],True),
               fixture([data(units('__proto__'),O(5),False,True,False)])]
        expected=[oracle(case) for case in cases]
        faults=[SOURCE.replace('node.#params === emptyParams','node.#params === node.#params'),
                SOURCE.replace('node.#params === emptyParams','node.#params === node'),
                SOURCE.replace('? {} : { ...node.#params }','? { ...node.#params } : {}'),
                SOURCE.replace('{ ...node.#params }','{ ...emptyParams }'),
                SOURCE.replace('node.#params === emptyParams ? {} : { ...node.#params }','node.#params'),
                SOURCE.replace('{ ...node.#params }','{}')]
        self.assertEqual(len(faults),6)
        for source in faults:
            self.assertNotEqual(source,SOURCE)
            self.assertTrue(model(dict(cases=[],source=source))['parsed'],source)
            self.assertNotEqual(self.compare(cases,source),expected,source)
        rejected=[SOURCE.replace('const params','let params'),SOURCE.replace('node.#params','node.#notDeclared'),
                  SOURCE.replace('...node.#params','...unknown'),SOURCE.replace('...node.#params','...callback()'),
                  SOURCE.replace('...node.#params',"__proto__: node"),SOURCE+'unknown\n',SOURCE+'/* trailing */\n']
        for source in rejected:self.assertFalse(model(dict(cases=[],source=source))['parsed'],source)
        for source in [SOURCE.rstrip(),SOURCE.replace('\n','\r\n')]:self.assertEqual(self.compare(cases,source),expected)

    def test_model_refusal_and_node_boundary(self):
        # A particular throwing getter agrees with model refusal; this is not a
        # claim that arbitrary enumerable getters throw. Native successes are
        # demonstrated separately by boundary.mjs.
        cases=[fixture([accessor([97,index],True)]) for index in range(16)]
        self.assertEqual(self.compare(cases),[dict(ok=False)]*16)
        self.assertIsNotNone(NODE,'Use HONO_NODE or Node22.22.2 on PATH')
        portable=shared_cases()[::17]+copy_cases()[::47]
        self.assertEqual(self.compare(portable,runtime=NODE),[oracle(case) for case in portable])
        for runtime in ['bun',NODE]:
            result=invoke([runtime,'verification/params-init/boundary.mjs',str(HONO)])
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertFalse(json.loads(result.stdout)['verified'])

    def test_source_identity(self):
        result=invoke(['python3','verification/params-init/source.py','--hono',str(HONO)])
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);files=['verification/params-init/source.py','verification/params-init/source.json',
                'verification/params-init/full.ts.txt','HonoLean/Upstream/NodeParamsInit/Generated.lean']
            for file in files:
                target=root/file;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/file,target)
            for file in files[1:]:
                path=root/file;before=path.read_bytes();path.write_bytes(before+b'\n')
                result=invoke(['python3',str(root/files[0]),'--hono',str(HONO)]);self.assertNotEqual(result.returncode,0,file);path.write_bytes(before)
            clone=root/'hono'
            subprocess.run(['git','clone','--quiet','--shared','--no-checkout',str(HONO),str(clone)],check=True,env=ENV)
            subprocess.run(['git','-C',str(clone),'checkout','--quiet','--detach','5ca49b0720755c585c9a9835f0a479ceea36fb52'],check=True,env=ENV)
            path=clone/'src/router/trie-router/node.ts';path.write_bytes(path.read_bytes()+b'\n')
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged','src/router/trie-router/node.ts'],check=True,env=ENV)
            result=invoke(['python3',str(root/files[0]),'--hono',str(clone)]);self.assertNotEqual(result.returncode,0)

    def test_actual_pinned_multisegment_routes(self):
        result=invoke(['bun','verification/params-init/upstream.mjs',str(HONO)])
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        observed=json.loads(result.stdout);self.assertFalse(observed['verified'])
        self.assertFalse(observed['nativeTypeScriptLoadingVerified']);self.assertEqual(observed['checkedPinnedBlobs'],315)
        expected=[]
        for first,second in [('id','id'),('constructor','id'),('__proto__','id'),('id','__proto__')]:
            for path in ['/alpha/12','/alpha/no']:
                record=dict(first=first,second=second,path=path,pattern=f'/:{first}/:{second}{{[0-9]+}}',handlers=['capture'] if path=='/alpha/12' else [])
                if path=='/alpha/12':
                    fields={first:dict(objectPrototype=True) if first=='__proto__' else 'alpha'}
                    if second not in fields:fields[second]=dict(objectPrototype=True) if second=='__proto__' else '12'
                    record.update(nullPrototype=True,entries=sorted(fields.items()))
                expected.append(record)
        # JSON arrays represent the parallel key/value entries.
        self.assertEqual(observed['records'],json.loads(json.dumps(expected)))

if __name__=='__main__':unittest.main(argv=['params-init'])
