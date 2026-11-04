#!/usr/bin/env python3
"""Exact wildcard/body source vs independent no-effect/cache history contract."""
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
from oracle import cache,U,string,units,key,history

ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve();ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/getpattern-body/body.ts.txt').read_text()
GUARD=(ROOT/'verification/getpattern-body/guard.ts.txt').read_text()
def invoke(command,packet=None,root=ROOT,check=True):
    result=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=root,env=ENV,text=True,capture_output=True,timeout=240)
    if check and result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)if packet is not None and check else result
def model(packet):return invoke(['lake','env','lean','--run','verification/getpattern-cache/Driver.lean'],packet)
def native(packet,engine):
    result=invoke([engine,'verification/getpattern-body/native.mjs',str(HONO)],packet)
    assert result['sourceBytes']==576 and result['checkedPinnedBlobs']==315 and result['verified']is False and result['observerVerified']is False
    return result['results']
def step(label,next_value=U):return dict(label=units(label),next=next_value)
def wild_cases():
    next_values=[U,dict(kind='null'),dict(kind='bool',value=False),dict(kind='number',value=17),string([]),string(units('next')),
                 dict(kind='array',ref=0),dict(kind='object',ref=0),dict(kind='object',ref=2),dict(kind='function',ref=6)]
    cases=[]
    for next_value,ctor,cache_kind,extensible in itertools.product(next_values,['builtin','number'],['object','undefined'],[False,True]):
        cases.append(dict(constructorKind=ctor,cacheKind=cache_kind,extensible=extensible,steps=[step('*',next_value)]*3))
    return cases
def mixed_histories():
    events=[step(':id'),step('bad'),step(':id{[0-9]+}'),step(':id{[0-9]+}',string(units(':rest'))),step('*'),step('*',dict(kind='object',ref=0))]
    result=[dict(steps=list(sequence))for length in range(4)for sequence in itertools.product(events,repeat=length)]
    result += [dict(steps=[step(':id{[0-9]+}'),step('*',dict(kind='object',ref=0)),step(':id{[0-9]+}',string(units('undefined')))]),
               dict(steps=[step(':a#b',string(units('c'))),step('*'),step(':a',string(units('b#c')))])]
    return result

class Checks(unittest.TestCase):
    def compare(self,cases,source=SOURCE,expected=None):
        packet=dict(cases=cases,source=source)
        expected=expected if expected is not None else[history(case)for case in cases]
        result=model(packet);self.assertTrue(result['parsed']);self.assertEqual(result['results'],expected)
        for engine in ['bun',NODE]:
            actual=native(packet,engine)
            for row in actual:
                for event in row:
                    if not event['ok']:self.assertEqual(event['errorName'],'TypeError')
            actual=[[dict(ok=False)if not event['ok']else event for event in row]for row in actual]
            self.assertEqual(actual,expected)
    def test01_wildcard_skips_unready_bindings(self):
        cases=wild_cases();self.assertEqual(len(cases),80);self.compare(cases)
    def test02_persistent_interleavings(self):
        cases=mixed_histories();self.assertEqual(len(cases),261);self.compare(cases)
    def test03_exact_star_not_prefix_or_other_string(self):
        labels=['','id','**','/*','*/','*tail','*\n','\ud800*',':id',':id{}',':id{[0-9]+}']
        cases=[dict(steps=[step(label)])for label in labels]
        self.compare(cases)
    def test04_normal_profiles_through_actual_guard(self):
        cases=[]
        for name,next_value in itertools.product(['id','i\nj','名','\ud800\x00\udc00'],[U,string([]),string(units(':next')),string(units('*tail'))]):
            for regex in [False,True]:
                label=':'+name+('{[A-z]+}'if regex else'')
                cases.append(dict(steps=[step(label,next_value),step('*'),step(label,next_value)]))
        self.assertEqual(len(cases),32);self.compare(cases)
    def test05_supported_guard_faults(self):
        star=dict(steps=[step('*')]);ordinary=dict(steps=[step('bad')])
        no_guard=SOURCE[len(GUARD)+1:]
        false_star=[cache.history(star)]
        expected=history(star);changed=copy.deepcopy(expected);changed[0]['value']=string([33])
        faults=[(SOURCE.replace("label === '*'","label === '@'"),[star],false_star),
                (SOURCE.replace("label === '*'","label !== '*'"),[ordinary],[history(star)]),
                (SOURCE.replace("return '*'","return '!'"),[star],[changed]),
                (no_guard,[star],false_star)]
        self.assertEqual(len(faults),4)
        for source,cases,expected in faults:
            self.assertNotEqual(source,SOURCE);self.assertNotEqual(expected,[history(case)for case in cases])
            self.compare(cases,source=source,expected=expected)
    def test06_source_and_generated_identity(self):
        invoke(['python3','verification/getpattern-body/source.py','--hono',str(HONO)])
        with tempfile.TemporaryDirectory(prefix='getpattern-body-identity-')as directory:
            root=Path(directory);target=root/'verification/getpattern-body';target.mkdir(parents=True)
            for name in ['source.py','source.json','guard.ts.txt','body.ts.txt','declaration.ts.txt','header.ts.txt','leading-comments.ts.txt']:
                shutil.copyfile(ROOT/'verification/getpattern-body'/name,target/name)
            dependency=root/'verification/getpattern-cache';dependency.mkdir();shutil.copyfile(ROOT/'verification/getpattern-cache/full.ts.txt',dependency/'full.ts.txt')
            generated=root/'HonoLean/Upstream/GetPatternBody';generated.mkdir(parents=True);shutil.copyfile(ROOT/'HonoLean/Upstream/GetPatternBody/Generated.lean',generated/'Generated.lean')
            command=['python3',str(target/'source.py'),'--hono',str(HONO)];invoke(command,root=root)
            for file in [target/'body.ts.txt',target/'guard.ts.txt',target/'declaration.ts.txt',target/'source.json',generated/'Generated.lean']:
                before=file.read_bytes();file.write_bytes(before+b' ');self.assertNotEqual(invoke(command,root=root,check=False).returncode,0);file.write_bytes(before)
            invoke(command,root=root)
    def test07_native_effect_and_actual_module_controls(self):
        evidence=json.loads((ROOT/'verification/getpattern-body/control-evidence.json').read_text())
        self.assertFalse(evidence['verified']);self.assertTrue(evidence['nativeOnly'])
        self.assertEqual([len(record['results'])for record in evidence['records']],[3,2])
        for engine,expected in zip(['bun',NODE],evidence['records']):
            actual=invoke([engine,'verification/getpattern-body/controls.mjs',str(HONO)],{})
            self.assertEqual(actual,expected)
    def test08_structural_arrow_parser_and_frontiers(self):
        declaration=(ROOT/'verification/getpattern-body/declaration.ts.txt').read_text()
        comments=(ROOT/'verification/getpattern-body/leading-comments.ts.txt').read_text()
        alternate=declaration.replace('getPattern =','otherPattern =').replace('Pattern | null','null | Pattern')
        refusal=[declaration.replace('next?: string','label?: string'),
                 declaration.replace('next?: string','next: string = "default"'),
                 declaration.replace('label: string, next?: string','label?: string, next: string'),
                 declaration.replace('export const','const'),
                 declaration.replace('return null','return missing'),
                 'export const f = (): Pattern | null => { // }',
                 'export const f = (): Pattern | null => { // prefix\u2028return null\n}',
                 'export const f = (): Pattern | null => { // prefix\u2029return null\n}',
                 declaration.replace(comments,'/* prefix */\n'),
                 declaration.replace('return null','return null // trailing')]
        result=invoke(['lake','env','lean','--run','verification/getpattern-body/Parser.lean'],dict(body=SOURCE,sources=[declaration,alternate]+refusal))
        self.assertEqual(len(result),12)
        expected=dict(parsed=True,name='getPattern',parameters=[dict(name='label',optional=False,type=dict(kind='named',name='string')),
                       dict(name='next',optional=True,type=dict(kind='named',name='string'))],
                      resultType=dict(kind='union',left=dict(kind='named',name='Pattern'),right=dict(kind='named',name='null')),
                      innerSource='\n'+comments+SOURCE,bodyLength=4,bodyMatches=True)
        self.assertEqual(result[0],expected)
        other=copy.deepcopy(expected);other['name']='otherPattern';other['resultType']=dict(kind='union',left=dict(kind='named',name='null'),right=dict(kind='named',name='Pattern'))
        self.assertEqual(result[1],other)
        self.assertEqual(result[2:],[dict(parsed=False)]*len(refusal))
    def test09_wildcard_without_any_allocated_realm(self):
        result=invoke(['lake','env','lean','--run','verification/getpattern-body/Unready.lean'],dict(source=SOURCE))
        expected=dict(value='HonoLean.Upstream.SourceSubset.Value.string [42]',sameEntireState=True,arrays=0,objects=0)
        self.assertEqual(result,[expected,expected])
    def test10_complete_body_keeps_reached_lookahead_frontier(self):
        fixture=dict(steps=[step(':id{[0-9]+}',string(units('tail')))])
        packet=dict(source=SOURCE,cases=[fixture])
        actual=model(packet);self.assertTrue(actual['parsed']);self.assertEqual(actual['results'],[[dict(ok=False)]])
        for engine in ['bun',NODE]:
            event=native(packet,engine)[0][0];self.assertTrue(event['ok'])
            self.assertEqual(event['visibleGraph'][0]['values'][0],string(key(units(':id{[0-9]+}'),string(units('tail')))))
            self.assertEqual(event['visibleGraph'][1]['source'],units(r'^[0-9]+(?=\/tail)'))

if __name__=='__main__':unittest.main(argv=['getpattern-body-tests'])
