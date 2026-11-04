#!/usr/bin/env python3
"""Actual arrow setup/calls vs independent argument/live-binding/cache contract."""
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
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve();ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/getpattern-invocation/setup.ts.txt').read_text()
def invoke(command,packet=None,root=ROOT,check=True):
    result=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=root,env=ENV,text=True,capture_output=True,timeout=240)
    if check and result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)if packet is not None and check else result
def model(packet):return invoke(['lake','env','lean','--run','verification/getpattern-invocation/Driver.lean'],packet)
def native(packet,engine):
    result=invoke([engine,'verification/getpattern-invocation/native.mjs',str(HONO)],packet)
    assert result['sourceBytes']==796 and result['checkedPinnedBlobs']==315
    for flag in ['verified','observerVerified','typescriptLoaderVerified','moduleInstantiationVerified','nativeLanguageAdequacyVerified','hiddenAllocationsObserved']:
        assert result[flag]is False,flag
    return result['results']
def step(label,next_value=U,**extra):return dict(label=units(label),next=next_value,**extra)
def args(*values,**extra):return dict(arguments=list(values),**extra)
def mixed_histories():
    events=[step(':id'),step('bad'),step(':id{[0-9]+}'),step(':id{[0-9]+}',string(units(':rest'))),
            args(string([42]),dict(kind='object',ref=0)),args(string(units(':id')))]
    return [dict(steps=list(sequence))for length in range(4)for sequence in itertools.product(events,repeat=length)]

class Checks(unittest.TestCase):
    def compare(self,cases,source=SOURCE,expected=None):
        packet=dict(cases=cases,source=source)
        expected=expected if expected is not None else[history(case)for case in cases]
        result=model(packet);self.assertTrue(result['parsed']);self.assertEqual(result['results'],expected)
        for engine in ['bun',NODE]:
            actual=native(packet,engine)
            for row in actual:
                for event in row['observations']:
                    if not event['ok']:self.assertEqual(event['errorName'],'TypeError')
                row['observations']=[dict(ok=False)if not event['ok']else event for event in row['observations']]
            self.assertEqual(actual,expected)
    def test01_argument_binding_and_creation_metadata(self):
        cases=[]
        for label in ['*','bad',':id',':id{[0-9]+}']:
            value=string(units(label))
            cases.append(dict(steps=[args(value),args(value,U),args(value,U,dict(kind='object',ref=0)),args(value,U,string([120]),dict(kind='number',value=99))]))
        cases.append(dict(steps=[args()]))
        self.assertEqual(len(cases),5);self.compare(cases)
    def test02_shared_closure_cache_histories(self):
        cases=mixed_histories();self.assertEqual(len(cases),259);self.compare(cases)
    def test03_current_constructor_changes_after_creation_and_calls(self):
        cases=[]
        for next_value in [U,string([]),string(units(':next')),string(units('*tail'))]:
            cases.extend([
                dict(steps=[step(':id{[0-9]+}',next_value),step(':id{[0-9]+}',next_value,constructorKind='number')]),
                dict(steps=[step('*',dict(kind='object',ref=0),constructorKind='number'),step('bad'),step(':plain'),
                            step(':new{[A-z]+}',next_value,constructorKind='builtin')]),
                dict(steps=[step(':plain',constructorKind='number'),step(':cold{[0-9]+}',next_value)]),
                dict(steps=[step(':first{[0-9]+}',next_value),step(':second{[0-9]+}',next_value,constructorKind='number')])])
        self.assertEqual(len(cases),16);self.compare(cases)
    def test04_normal_utf16_and_terminal_next_profiles(self):
        cases=[]
        for name,next_value,body in itertools.product(['id','i\nj','名','\ud800\x00\udc00'],[U,string([]),string(units(':next')),string(units('*tail'))],['','{[A-z]+}']):
            label=':'+name+body
            cases.append(dict(steps=[step(label,next_value),args(string([42])),step(label,next_value)]))
        self.assertEqual(len(cases),32);self.compare(cases)
    def test05_raw_key_collisions_keep_first_tuple(self):
        events=[step(':a#b',string(units('c'))),step(':a',string(units('b#c')))]
        string_undefined=[args(string(units(':undefined'))),step(':undefined',string(units('undefined')))]
        cases=[dict(steps=sequence+[args(string([42]))]+sequence[::-1])for pair in [events,string_undefined]for sequence in [pair,pair[::-1]]]
        self.assertEqual(len(cases),4);self.compare(cases)
    def test06_initial_descriptor_profiles(self):
        cases=[];target=key(units(':id'),U)
        values=[dict(kind='number',value=0),dict(kind='number',value=17),dict(kind='array',ref=0),U,
                string([]),string([120]),dict(kind='bool',value=False),dict(kind='object',ref=2)]
        for value,inherited,writable in itertools.product(values,[False,True],[False,True]):
            field=dict(key=target,value=value,writable=writable,enumerable=False,configurable=False)
            cases.append(dict(**{'inherited'if inherited else'seed':[field]},steps=[args(string(units(':id')))]))
        self.assertEqual(len(cases),32);self.compare(cases)
    def test07_supported_source_faults_change_behavior(self):
        star=dict(steps=[step('*')]);ordinary=dict(steps=[step('bad')]);star_expected=history(star)
        null_expected=copy.deepcopy(star_expected);null_expected['observations'][0]['value']=dict(kind='null')
        changed=copy.deepcopy(star_expected);changed['observations'][0]['value']=string([33])
        cases=[(SOURCE.replace("label === '*'","label === '@'"),[star],[null_expected]),
               (SOURCE.replace("label === '*'","label !== '*'"),[ordinary],[star_expected]),
               (SOURCE.replace("return '*'","return '!'"),[star],[changed]),
               (SOURCE.replace('return null',"return '*'"),[ordinary],[star_expected]),
               (SOURCE.replace('(label: string, next?: string)','(next: string, label?: string)'),
                [dict(steps=[args(string([42]),string(units('bad')))])],
                [history(dict(steps=[args(string(units('bad')),string([42]))]))])]
        self.assertEqual(len(cases),5)
        for source,fixtures,expected in cases:
            self.assertNotEqual(source,SOURCE);self.assertNotEqual(expected,[history(case)for case in fixtures])
            self.compare(fixtures,source=source,expected=expected)
    def test08_source_and_generated_artifact_freshness(self):
        invoke(['python3','verification/getpattern-invocation/source.py','--hono',str(HONO)])
        with tempfile.TemporaryDirectory(prefix='hono-arrow-identity-')as directory:
            root=Path(directory)
            copies=['verification/getpattern-invocation/source.py','verification/getpattern-invocation/source.json',
                    'verification/getpattern-invocation/setup.ts.txt','HonoLean/Upstream/GetPatternInvocation/Generated.lean',
                    'verification/getpattern-cache/init.ts.txt','verification/getpattern-body/declaration.ts.txt']
            for name in copies:
                target=root/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,target)
            command=['python3',str(root/copies[0]),'--hono',str(HONO)];invoke(command,root=root)
            for name in copies[1:]:
                file=root/name;before=file.read_bytes();file.write_bytes(before+b' ')
                self.assertNotEqual(invoke(command,root=root,check=False).returncode,0);file.write_bytes(before)
            invoke(command,root=root)
    def test09_actual_full_module_and_callback_frontier_controls(self):
        evidence=json.loads((ROOT/'verification/getpattern-invocation/control-evidence.json').read_text())
        self.assertFalse(evidence['verified']);self.assertTrue(evidence['nativeOnly'])
        self.assertEqual([len(record['results'])for record in evidence['records']],[4,4])
        for engine,expected in zip(['bun',NODE],evidence['records']):
            actual=invoke([engine,'verification/getpattern-invocation/controls.mjs',str(HONO)],{})
            self.assertEqual(actual,expected)
    def test10_reached_lookahead_stays_explicitly_open(self):
        fixture=dict(steps=[step(':id{[0-9]+}',string(units('tail')))])
        packet=dict(source=SOURCE,cases=[fixture]);actual=model(packet);self.assertTrue(actual['parsed'])
        self.assertEqual(actual['results'][0]['observations'],[dict(ok=False)])
        for engine in ['bun',NODE]:
            event=native(packet,engine)[0]['observations'][0];self.assertTrue(event['ok'])
            self.assertEqual(event['visibleGraph'][0]['values'][0],string(key(units(':id{[0-9]+}'),string(units('tail')))))
            self.assertEqual(event['visibleGraph'][1]['source'],units(r'^[0-9]+(?=\/tail)'))
    def test11_actual_setup_wildcard_without_normal_realm_or_globals(self):
        actual=invoke(['lake','env','lean','--run','verification/getpattern-invocation/Unready.lean'],{})
        expected=dict(value='HonoLean.Upstream.SourceSubset.Value.string [42]',sameEntireData=True,callerRestored=True,
                      oldCellsPreserved=True,cellsAdded=2,environmentsAdded=1,objects=4,arrays=0)
        self.assertEqual(actual,[expected,expected])

if __name__=='__main__':unittest.main(argv=['getpattern-invocation-tests'])
