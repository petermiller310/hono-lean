#!/usr/bin/env python3
"""Finite selected tuple/constructor evidence; hidden compiled records are model-only."""
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
SOURCE = (ROOT/'verification/pattern-construct/full.ts.txt').read_text()
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


def model(packet): return invoke(['lake','env','lean','--run','verification/pattern-construct/Driver.lean'], packet)


def native(packet, engine):
    result = invoke([engine,'verification/pattern-construct/native.mjs',str(HONO)],packet)
    assert result['revision']==REVISION and result['checkedPinnedBlobs']==315
    assert result['verified'] is False and result['observerVerified'] is False
    assert result['plainJavaScript'] is True and result['typescriptErasure'] is False
    return result['results']


def body_endpoints(body):
    safe = lambda x: 48<=x<=57 or 65<=x<=90 or 97<=x<=122
    if len(body)!=6 or body[0]!=91 or body[2]!=45 or body[4:]!=[93,43]: return None
    lo,hi=body[1],body[3]
    return (lo,hi) if safe(lo) and safe(hi) and lo<=hi else None


def oracle(case, mode='original'):
    """Independent initial-to-tuple and interval contract; no engine/parser/VM."""
    if case.get('calleeKind','constructor')!='constructor' and mode!='alias': return dict(ok=False),None
    label,name,body=case['label'],case['name'],case['body']
    output_label=units('alternate-label') if mode=='label' else name if mode=='swap' else label
    output_name=units('alternate-name') if mode=='name' else label if mode=='swap' else body if mode=='swap-indices' else name
    actual_body=units('[A-Z]+') if mode=='body' else name if mode in ['body-name','swap-indices'] else body
    bounds=body_endpoints(actual_body)
    if bounds is None: return dict(ok=False),None  # model grammar boundary, not a native SyntaxError claim
    lo,hi=bounds;value=case.get('input',[49,50]);hit=bool(value) and all(lo<=unit<=hi for unit in value)
    heap=[[string(units('prior'))],[string(label),string(name),string(body)],
          [string(output_label),string(output_name),obj(4)]]
    if hit: heap.append([string(value)])
    objects=[dict(intrinsic='Object.prototype'),dict(intrinsic='RegExp.prototype'),
             dict(own=[own('kept',string(units('canary')))],prototype=None,extensible=True),
             dict(own=[own('lastIndex',number(17),writable=False,enumerable=False,configurable=False)],prototype=1,extensible=True),
             dict(own=[own('lastIndex',number(0),enumerable=False,configurable=False)],prototype=1,extensible=True)]
    source=[94]+actual_body+[36]
    observed=normalize(dict(ok=True,returnedValue=array(2),heap=heap,objects=objects,
        regexp=dict(ref=4,source=source,flags=[],execIsBuiltin=True),lookup=array(3) if hit else tag('null'),
        view=match_view(value) if hit else None,priorView=match_view(units('prior')),scope=True,brandsKept=True,oldFrames=True))
    internal=dict(source=source,flags=[],compiled=[dict(op='assertStart'),dict(op='consumeRange',lower=lo,upper=hi),
                  dict(op='repeatRange',lower=lo,upper=hi),dict(op='assertEnd'),dict(op='accept')])
    return observed,internal


def contexts():
    safe=list(range(48,58))+list(range(65,91))+list(range(97,123))
    result=[]
    for lo,hi in itertools.product(safe,safe):
        if lo<=hi:
            for value in [[lo,hi],[]]:
                result.append(dict(label=units(':id{range}'),name=units('id'),body=[91,lo,45,hi,93,43],input=value))
    names=['','id','constructor','__proto__','prototype','[A-Z]+','a/b','\ud800\x00\udc00','名']
    inputs=[units(x)for x in ['12','0','x','12\n','12\r','12\r\n','12\u2028','12\u2029','１２']]+[[0],[55296],[56320],[49]*256]
    for name,value in itertools.product(names,inputs):
        result.append(dict(label=units(':label/'+name),name=units(name),body=units('[0-9]+'),input=value))
    for kind in ['number','undefined']:
        result += [dict(label=units('label'),name=units('id'),body=units('[0-9]+'),input=value,calleeKind=kind)for value in inputs[:3]]
    rng=random.Random(68138)
    for i in range(32):result.append(dict(label=[rng.randrange(65536)for _ in range(i)],name=[55296,i,56320],body=units('[A-z]+'),input=[rng.randrange(65536)for _ in range(i)]))
    return result


class Checks(unittest.TestCase):
    def assert_results(self, actual, expected):
        self.assertEqual(len(actual),len(expected))
        for index,(a,b)in enumerate(zip(actual,expected)):
            with self.subTest(context=index): self.assertEqual(normalize(a),b)

    def check_packet(self, cases, source=SOURCE, mode='original'):
        packet=dict(source=source,cases=cases);expected=[oracle(case,mode)for case in cases]
        actual=model(packet);self.assertTrue(actual['parsed'])
        self.assert_results(actual['results'],[pair[0]for pair in expected])
        self.assertEqual(actual['modelOnlyRecords'],[pair[1]for pair in expected])
        for engine in ['bun',NODE]:self.assert_results(native(packet,engine),[pair[0]for pair in expected])

    def test_01_identity_and_tampering(self):
        result=subprocess.run(['python3','verification/pattern-construct/source.py','--hono',str(HONO)],cwd=ROOT,env=ENV,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        with tempfile.TemporaryDirectory()as tmp:
            root=Path(tmp);(root/'verification').mkdir();(root/'HonoLean/Upstream').mkdir(parents=True)
            shutil.copytree(ROOT/'verification/pattern-construct',root/'verification/pattern-construct')
            shutil.copytree(ROOT/'HonoLean/Upstream/PatternConstruct',root/'HonoLean/Upstream/PatternConstruct')
            for relative in ['verification/pattern-construct/full.ts.txt','verification/pattern-construct/constructor.ts.txt','HonoLean/Upstream/PatternConstruct/Generated.lean']:
                path=root/relative;original=path.read_text();path.write_text(original.replace('match[2]','match[1]'))
                result=subprocess.run(['python3',str(root/'verification/pattern-construct/source.py'),'--hono',str(HONO)],cwd=ROOT,env=ENV,capture_output=True,text=True)
                self.assertNotEqual(result.returncode,0);path.write_text(original)

    def test_02_initial_to_constructed_query(self):
        cases=contexts()
        for start in range(0,len(cases),651):self.check_packet(cases[start:start+651])
        print(f'{len(cases)} full-world constructor+query contexts, including all1953range pairs; internalrecords checkedMODELONLY')

    def test_03_supported_source_faults_and_alias_identity(self):
        cases=[dict(label=units(':id{[0-9]+}'),name=units('[A-Z]+'),body=units('[0-9]+'),input=units(value))for value in ['12','AZ','']]
        faults=[('label',SOURCE.replace('[label,','[alternateLabel,')),('name',SOURCE.replace('match[1]','alternateName')),
                ('body',SOURCE.replace('match[2]','alternateBody')),('swap',SOURCE.replace('[label, match[1],','[match[1], label,')),
                ('body-name',SOURCE.replace('match[2]','match[1]')),
                ('swap-indices',SOURCE.replace('match[1]','MATCH_ONE').replace('match[2]','match[1]').replace('MATCH_ONE','match[2]'))]
        base=[oracle(case)[0]for case in cases]
        for mode,source in faults:
            self.assertNotEqual([oracle(case,mode)[0]for case in cases],base)
            self.check_packet(cases,source,mode)
        self.check_packet(cases,SOURCE.replace('new RegExp','new Alias'),'alias')
        self.check_packet([dict(cases[0],calleeKind='number')],SOURCE.replace('new RegExp','new Alias'),'alias')

    def test_04_frontend_and_grammar_refusals(self):
        for source in [SOURCE.replace('new RegExp','RegExp'),SOURCE.replace('`^${match[2]}$`','`^${match[2]}${match[1]}$`'),
                       SOURCE.replace('match[2]','unknown'),SOURCE+'; label',SOURCE.replace('`^','`\\^')]:
            self.assertEqual(model(dict(source=source,cases=[])),dict(parsed=False))
        case=dict(label=units('label'),name=units('id'),body=units('[0-9]+'),input=units('12'))
        for source in [SOURCE.replace('`^','`'),SOURCE.replace('}$`','}`')]:
            observed=model(dict(source=source,cases=[case]));self.assertTrue(observed['parsed'])
            self.assertEqual(observed['results'],[dict(ok=False)])
            for engine in ['bun',NODE]:self.assertTrue(native(dict(source=source,cases=[case]),engine)[0]['ok'])
        broader=dict(case,body=units('[0-9]*'),input=[])
        self.assertEqual(model(dict(cases=[broader]))['results'],[dict(ok=False)])
        for engine in ['bun',NODE]:
            self.assertTrue(native(dict(cases=[broader]),engine)[0]['ok'])
            self.assertTrue(native(dict(source=SOURCE.replace('new RegExp','RegExp'),cases=[case]),engine)[0]['ok'])

    def test_05_native_boundaries(self):
        for engine in ['bun',NODE]:
            result=invoke([engine,'verification/pattern-construct/boundary.mjs',str(HONO)])
            self.assertEqual(result['checkedPinnedBlobs'],315);self.assertEqual(result['revision'],REVISION)
            self.assertFalse(result['verified']);self.assertTrue(result['nativeOnly']);self.assertEqual(result['sourceBytes'],46)
            b=result['boundaries'];self.assertEqual(b['savedConstructorOrder'],['name','body','string','First'])
            self.assertEqual(b['argumentBeforeNonconstructor']['events'],['name','body'])
            self.assertEqual(b['tdzBeforeBody'],dict(events=['name'],referenceError=True))
            self.assertTrue(b['customConstructorSucceedsWithoutRegExpBrand']);self.assertTrue(b['boundBuiltinConstructorSucceeds'])
            self.assertTrue(b['validWiderGrammarSucceeds']);self.assertTrue(b['reversedRangeSyntaxError'])
            self.assertEqual(b['arrayBindingHooks'],[])

    def test_06_actual_constructor_cache_boundary(self):
        result=invoke(['bun','verification/pattern-construct/upstream.mjs',str(HONO)])
        self.assertFalse(result['verified']);self.assertFalse(result['nativeTypeScriptLoadingVerified'])
        self.assertEqual(result['checkedPinnedBlobs'],315);self.assertEqual(result['revision'],REVISION)
        self.assertEqual((result['constructionCount'],result['queryCount']),(16,32))
        self.assertTrue(all(row['freshLastIndexZero'] and row['sameCachedTuple'] and row['cachedMatcherRetainsMutation']for row in result['constructions']))
        self.assertEqual([row['terminalFirst']for row in result['orders']],[False,True])
        self.assertTrue(all(row['sameTuple'] and row['sameMatcher']for row in result['orders']))
        self.assertEqual(result['orders'][0]['retainedSource'],r'^[0-9]+(?=\/undefined)')
        self.assertEqual(result['orders'][1]['retainedSource'],'^[0-9]+$')


if __name__=='__main__':unittest.main(argv=['pattern-construct'],verbosity=2)
