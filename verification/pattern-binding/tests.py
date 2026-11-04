#!/usr/bin/env python3
"""Default-array binding and selected constructor/binding/exec evidence; protocol cells are model-only."""
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

ROOT = Path(__file__).resolve().parents[2]
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0', GIT_OPTIONAL_LOCKS='0')
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--hono', type=Path, required=True)
HONO = p.parse_args().hono.resolve()
NODE = os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE = (ROOT/'verification/pattern-binding/full.ts.txt').read_text()
REVISION = '5ca49b0720755c585c9a9835f0a479ceea36fb52'


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def tag(kind, **fields): return dict(kind=kind, **fields)
def string(value): return tag('string', units=value)
def array(ref): return tag('array', ref=ref)
def obj(ref): return tag('object', ref=ref)
def number(value): return tag('number', value=value)


def descriptor(value, writable=True, enumerable=True, configurable=True):
    return dict(kind='data', value=value, writable=writable, enumerable=enumerable, configurable=configurable)


def own(name, value, **flags): return dict(key=units(name), **descriptor(value, **flags))


def match_view(value):
    return dict(zero=descriptor(string(value)), length=descriptor(number(1), enumerable=False, configurable=False),
                index=descriptor(number(0)), input=descriptor(string(value)), groups=descriptor(tag('undefined')))


def normalize(result):
    result = copy.deepcopy(result)
    for cell in result.get('objects', []):
        if 'own' in cell: cell['own'].sort(key=lambda item: item['key'])
    return result


def invoke(command, packet=None):
    result = subprocess.run(command, input=None if packet is None else json.dumps(packet), cwd=ROOT,
                            env=ENV, text=True, capture_output=True, timeout=180)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def model(packet): return invoke(['lake','env','lean','--run','verification/pattern-binding/Driver.lean'], packet)


def native(packet, engine):
    result = invoke([engine,'verification/pattern-binding/native.mjs',str(HONO)],packet)
    assert result['revision']==REVISION and result['checkedPinnedBlobs']==315
    assert result['verified'] is False and result['observerVerified'] is False
    assert result['plainJavaScript'] is True and result['typescriptErasure'] is False
    assert result['protocolTraceNativeObserved'] is False
    return result['results']


def body_endpoints(body):
    safe = lambda x: 48<=x<=57 or 65<=x<=90 or 97<=x<=122
    if len(body)!=6 or body[0]!=91 or body[2]!=45 or body[4:]!=[93,43]: return None
    lo,hi=body[1],body[3]
    return (lo,hi) if safe(lo) and safe(hi) and lo<=hi else None


ELEMENTS={'original':[None,'name','matcher'],'swap':[None,'matcher','name'],'alternate':[None,'name','matcher'],
          'remove':['name','matcher'],'extra':[None,None,'name','matcher'],'fewer':[None,'name'],'rename':[None,'captured','matcher'],'empty':[]}
U=tag('undefined')
def protocol(values,elements,arrayref,iteratorref):
    """Independent selected-edition iterator/binding observation contract."""
    state=dict(name=string(units('outer-name')),matcher=obj(6),m=obj(5))
    trace=[dict(event='symbolGet',array=arrayref,value=tag('function',ref=7)),
           dict(event='iteratorAllocated',ref=iteratorref,array=arrayref),
           dict(event='nextGet',ref=iteratorref,value=tag('function',ref=8))]
    allocated=[dict(own=[],prototype=4,extensible=True)];cursor=0;done=False
    for binding in elements:
        value=U
        if not done:
            trace.append(dict(event='lengthGet',array=arrayref,length=len(values)))
            if cursor<len(values):
                value=values[cursor];trace.append(dict(event='elementGet',array=arrayref,index=cursor,value=value));cursor+=1
            else:done=True
            reference=iteratorref+len(allocated)
            allocated.append(dict(own=[own('value',value),own('done',tag('bool',value=done))],prototype=0,extensible=True))
            trace.extend([dict(event='resultAllocated',ref=reference,value=value,done=done),dict(event='doneGet',ref=reference,value=tag('bool',value=done))])
            if binding is not None and not done:trace.append(dict(event='valueGet',ref=reference,value=value))
        if binding is not None:
            state[binding]=value;trace.append(dict(event='initialized',name=binding,value=value))
    if not done:trace.append(dict(event='returnGet',ref=iteratorref,value=U))
    internal=dict(record=dict(iterator=iteratorref,nextMethod=tag('function',ref=8),done=done),
                  cursor=dict(array=None if done else arrayref,nextIndex=cursor),allocated=allocated,trace=trace)
    return state,internal

def oracle(case,pipeline=False,mode='original'):
    if not pipeline and (case.get('iteratorKind','inherited') not in ['inherited','alias'] or case.get('patternKind','array')!='array'):
        return dict(ok=False),None
    values=[string(case['label']),string(case['name']),string(case['body'])]if pipeline else case['values']
    alternate=case.get('alternateValues',[string(units('alternate-label')),string(units('alternate-name')),obj(6)])
    heap=[[string(units('prior'))],copy.deepcopy(values),copy.deepcopy(alternate)]
    visible=[dict(intrinsic=x)for x in ['Object.prototype','RegExp.prototype','Array.prototype','Iterator.prototype','ArrayIterator.prototype']]
    visible += [dict(own=[own('kept',string(units('canary')))],prototype=None,extensible=True),
                dict(own=[own('lastIndex',number(17),writable=False,enumerable=False,configurable=False)],prototype=1,extensible=True)]
    produced=None
    if pipeline:
        bounds=body_endpoints(case['body'])
        if bounds is None:return dict(ok=False),None
        heap.append([string(case['label']),string(case['name']),obj(7)])
        visible.append(dict(own=[own('lastIndex',number(0),enumerable=False,configurable=False)],prototype=1,extensible=True))
        produced=dict(tuple=array(3),regex=obj(7),source=[94]+case['body']+[36],flags=[])
    ref=2 if mode=='alternate' else 3 if pipeline else 1
    bound,internal=protocol(heap[ref],ELEMENTS[mode],ref,8 if pipeline else 7)
    current_view=None
    if pipeline:
        matcher=bound['matcher']
        if matcher not in [obj(6),obj(7)]:return dict(ok=False),None
        lo,hi=(112,114)if matcher==obj(6)else bounds
        value=case.get('input',[49,50]);hit=bool(value)and all(lo<=unit<=hi for unit in value)
        bound['m']=array(4)if hit else tag('null')
        if hit:heap.append([string(value)]);current_view=match_view(value)
    kind=case.get('iteratorKind','inherited')
    iterator_desc=None if pipeline or kind=='inherited' else descriptor(tag('function',ref=7)if kind=='alias'else number(0)if kind=='number'else U)
    symbols=[dict(kind='array',ref=1,descriptor=iterator_desc),dict(kind='array',ref=2,descriptor=None),
             dict(kind='object',ref=2,descriptor=descriptor(tag('function',ref=7),enumerable=False))]
    if pipeline:symbols.append(dict(kind='array',ref=3,descriptor=None))
    observed=dict(ok=True,name=bound['name'],matcher=bound['matcher'],m=bound['m'],heap=heap,visibleObjects=visible,symbols=symbols,
                  view=current_view,priorView=match_view(units('prior')),produced=produced,scope=True,oldFrames=True,brandsKept=True)
    return observed,internal

def normalise(observed):
    observed=copy.deepcopy(observed)
    for cell in observed.get('visibleObjects',[]):
        if'own'in cell:cell['own'].sort(key=lambda x:x['key'])
    return observed

def binding_contexts():
    values=[U,tag('null'),tag('bool',value=False),tag('bool',value=True),number(0),number(-7),number(9007199254740991),
            string([]),string(units('id')),string([55296,0,56320]),obj(0),obj(1),obj(5),obj(6),array(0),array(1),array(2),
            tag('function',ref=0),tag('function',ref=3),tag('function',ref=4),tag('function',ref=5),tag('function',ref=6),tag('function',ref=7),tag('function',ref=8),tag('constructor')]
    cases=[dict(values=[values[(i+j)%len(values)],a,b])for(i,a),(j,b)in itertools.product(enumerate(values),repeat=2)]
    for length,offset in itertools.product(range(12),range(len(values))):cases.append(dict(values=[values[(i+offset)%len(values)]for i in range(length)]))
    for kind in ['alias','number','undefined']:
        cases += [dict(values=[string(units('label')),string(units('id')),obj(6)][:length],iteratorKind=kind)for length in range(4)]
    cases += [dict(values=[],patternKind=kind)for kind in ['number','undefined']]
    return cases

def pipeline_contexts():
    safe=list(range(48,58))+list(range(65,91))+list(range(97,123));cases=[]
    for lo,hi in itertools.product(safe,safe):
        if lo<=hi:
            for value in [[lo,hi],[]]:cases.append(dict(label=units(':id{range}'),name=units('id'),body=[91,lo,45,hi,93,43],input=value))
    for name,value in itertools.product(['','constructor','__proto__','名','\ud800\x00\udc00'],
           ['', '12','12\n','12\r\n','12\u2028','x','１２','\ud800']):
        cases.append(dict(label=units(':x/'+name),name=units(name),body=units('[0-9]+'),input=units(value)))
    return cases

class Checks(unittest.TestCase):
    def check_packet(self,cases,pipeline=False,mode='original',source=SOURCE):
        packet=dict(mode='pipeline'if pipeline else'binding',source=source,cases=cases);expected=[oracle(c,pipeline,mode)for c in cases]
        actual=model(packet);self.assertTrue(actual['parsed']);self.assertEqual(len(actual['results']),len(expected))
        self.assertEqual([normalise(x)for x in actual['results']],[normalise(pair[0])for pair in expected])
        for a,(_,b)in zip(actual['modelOnlyProtocol'],expected):
            if a is not None:
                for cell in a['allocated']:cell['own'].sort(key=lambda x:x['key'])
            if b is not None:
                b=copy.deepcopy(b)
                for cell in b['allocated']:cell['own'].sort(key=lambda x:x['key'])
            self.assertEqual(a,b)
        for engine in ['bun',NODE]:self.assertEqual([normalise(x)for x in native(packet,engine)],[normalise(pair[0])for pair in expected])

    def test_01_identity_and_tampering(self):
        result=subprocess.run(['python3','verification/pattern-binding/source.py','--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        with tempfile.TemporaryDirectory()as tmp:
            root=Path(tmp);(root/'verification').mkdir();(root/'HonoLean/Upstream').mkdir(parents=True)
            shutil.copytree(ROOT/'verification/pattern-binding',root/'verification/pattern-binding')
            shutil.copytree(ROOT/'HonoLean/Upstream/NodePatternBinding',root/'HonoLean/Upstream/NodePatternBinding')
            for relative in ['verification/pattern-binding/full.ts.txt','HonoLean/Upstream/NodePatternBinding/Generated.lean']:
                path=root/relative;before=path.read_text();path.write_text(before.replace('name, matcher','matcher, name'))
                changed=subprocess.run(['python3',str(root/'verification/pattern-binding/source.py'),'--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True)
                self.assertNotEqual(changed.returncode,0);path.write_text(before)

    def test_02_default_binding_and_model_only_protocol(self):
        cases=binding_contexts()
        for i in range(0,len(cases),300):self.check_packet(cases[i:i+300])
        print(f'{len(cases)} binding contexts; nativeVISIBLE vsMODELONLY protocol/cursor/cells')

    def test_03_actual_constructor_binding_exec_pipeline(self):
        cases=pipeline_contexts()
        for i in range(0,len(cases),400):self.check_packet(cases[i:i+400],pipeline=True)
        print(f'{len(cases)} selected ctor→138→156 contexts; all1953range pairs finite, universal156join digits only')

    def test_04_supported_source_faults(self):
        cases=[dict(values=[string(units('label')),string(units('name')),obj(6),string(units('fourth'))]),dict(values=[])]
        faults=[('swap',SOURCE.replace('name, matcher','matcher, name')),
                ('alternate',SOURCE.replace('= pattern','= alternatePattern')),
                ('remove',SOURCE.replace('[, name, matcher]','[name, matcher]')),
                ('extra',SOURCE.replace('[, name, matcher]','[,, name, matcher]')),
                ('fewer',SOURCE.replace('[, name, matcher]','[, name]')),
                ('rename',SOURCE.replace('name, matcher','captured, matcher')),
                ('empty',SOURCE.replace('[, name, matcher]','[]'))]
        self.assertEqual(len(faults),7)
        baseline=[oracle(c)[0]for c in cases]
        for mode,source in faults:
            self.assertNotEqual([oracle(c,mode=mode)[0]for c in cases],baseline)
            self.check_packet(cases,mode=mode,source=source)
        good=[dict(label=units(':id{[0-9]+}'),name=units('id'),body=units('[0-9]+'),input=units('12'))]
        for mode,source in faults[:2]+faults[4:6]:self.check_packet(good,pipeline=True,mode=mode,source=source)

    def test_05_frontend_and_runtime_domain_boundaries(self):
        for source in ['const [name,name] = pattern','const [Object] = pattern','const [name] = name',
                       'const [,name,matcher=0] = pattern','let [,name,matcher] = pattern','const [...matcher] = pattern',
                       'const [,name,matcher] = pattern; const x = 0','const [,name,matcher] = pattern.shift()']:
            self.assertEqual(model(dict(source=source,cases=[])),dict(parsed=False))
        case=dict(values=[],patternKind='string')
        self.assertEqual(model(dict(cases=[case]))['results'],[dict(ok=False)])
        for engine in ['bun',NODE]:
            actual=native(dict(cases=[case]),engine)[0];self.assertTrue(actual['ok'])
            self.assertEqual(actual['name'],string(units('b')));self.assertEqual(actual['matcher'],string(units('c')))

    def test_06_preserve_engine_boundary(self):
        result=subprocess.run(['python3','verification/pattern-binding/check-native.py','--hono',str(HONO)],cwd=ROOT,env=ENV,text=True,capture_output=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        recorded=json.loads((ROOT/'verification/pattern-binding/native-evidence.json').read_text())
        self.assertIsNone(recorded['formalBindingTheorem']);self.assertFalse(recorded['records'][2]['throwing']['ok'])
        self.assertTrue(recorded['records'][3]['throwing']['ok'])

if __name__=='__main__':unittest.main(argv=['pattern-binding'],verbosity=2)
