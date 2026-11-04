#!/usr/bin/env python3
"""Pinned cold-terminal cache histories and stored-regex language comparisons."""
import argparse
import copy
import importlib.util
import itertools
import json
import os
from pathlib import Path
import shutil
import subprocess
import unittest

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('cache_oracle',ROOT/'verification/getpattern-cache/oracle.py')
oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
U,string,units,key,history=oracle.U,oracle.string,oracle.units,oracle.key,oracle.history
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve()
ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/getpattern-cache/full.ts.txt').read_text()
SAFE=list(range(48,58))+list(range(65,91))+list(range(97,123))
PAIRS=[(lo,hi)for lo in SAFE for hi in SAFE if lo<=hi]
NEXT=[U,string([]),string([58,0,55296,35,123]),string([42,47,65535,125])]
NAMES=['id','a#b','i\nj','名','\ud800\x00\udc00']

def invoke(command,packet=None):
    result=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=ROOT,env=ENV,text=True,capture_output=True,timeout=240)
    if result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)if packet is not None else result.stdout
def model(packet,probe=False):
    driver='verification/getpattern-terminal-cache/Probe.lean'if probe else'verification/getpattern-cache/Driver.lean'
    return invoke(['lake','env','lean','--run',driver],packet)
def native(packet,engine,probe=False):
    driver='verification/getpattern-terminal-cache/native.mjs'if probe else'verification/getpattern-cache/native-main.mjs'
    result=invoke([engine,driver,str(HONO)],packet)
    assert result['checkedPinnedBlobs']==315 and result['verified']is False and result['observerVerified']is False
    return result['results']
def label(name,lo,hi):return units(':'+name+'{[')+[lo,45,hi]+units(']+}')
def step(input,next_value):return dict(label=input,next=next_value)
def query_inputs(lo,hi):
    # Include empty, lower/upper boundaries, mixed accepted strings, just-outside
    # endpoints, line terminators, NUL and lone surrogate units.
    middle=(lo+hi)//2
    return [[],[lo],[hi],[lo,hi,lo],[lo-1],[hi+1],[lo,10],[lo,13],[lo,8232],[lo,8233],[0],[55296],[56320],[65535],
            [middle],[middle,lo,hi],list(range(lo,hi+1)),[lo,hi+1],[lo-1,lo]]
def probe_expected(case):
    name,body=oracle.decompose(case['label']);lo,hi=body[1],body[3]
    queries=[dict(index=0,value=q,captures=[])if q and all(lo<=unit<=hi for unit in q)else None for q in case['queries']]
    return dict(ok=True,label=case['label'],name=name,source=[94]+body+[36],flags=[],lastIndex=dict(value=0,writable=True,enumerable=False,configurable=False),
                sameTuple=True,sameRegex=True,cacheReturnsSameTuple=True,oldFrames=True,queries=queries)

class Checks(unittest.TestCase):
    def compare(self,cases,source=SOURCE,expected=None,probe=False):
        packet=dict(cases=cases,source=source)
        expected=expected if expected is not None else[probe_expected(case)if probe else history(case)for case in cases]
        result=model(packet,probe);self.assertTrue(result['parsed']);self.assertEqual(result['results'],expected)
        for engine in ['bun',NODE]:self.assertEqual(native(packet,engine,probe),expected)
    def test01_all_pairs_all_terminal_next_and_reuse(self):
        self.assertEqual(len(PAIRS),1953)
        cases=[]
        for (lo,hi),next_value in itertools.product(PAIRS,NEXT):
            event=step(label('id',lo,hi),next_value)
            cases.append(dict(steps=[event,event]))
        self.assertEqual(len(cases),7812);self.compare(cases)
    def test02_descriptor_flags_and_raw_names(self):
        cases=[]
        for name,next_value,owner,falsy,writable,extensible,enumerable,configurable in itertools.product(
            NAMES,NEXT,['seed','inherited'],[U,dict(kind='number',value=0)],[False,True],[False,True],[False,True],[False,True]):
            input=label(name,48,57)
            field=dict(key=key(input,next_value),value=falsy,writable=writable,enumerable=enumerable,configurable=configurable)
            cases.append({owner:[field],'extensible':extensible,'steps':[step(input,next_value),step(input,next_value)]})
        self.assertEqual(len(cases),1280)
        expected=[history(case)for case in cases]
        packet=dict(cases=cases,source=SOURCE);result=model(packet)
        self.assertTrue(result['parsed']);self.assertEqual(result['results'],expected)
        for engine in ['bun',NODE]:
            actual=native(packet,engine)
            for row in actual:
                for event in row:
                    if not event['ok']:self.assertEqual(event['errorName'],'TypeError')
            projected=[[dict(ok=False)if not event['ok']else event for event in row]for row in actual]
            self.assertEqual(projected,expected)
    def test03_actual_cached_records_drive_query_language(self):
        cases=[dict(label=label('id',lo,hi),next=next_value,queries=query_inputs(lo,hi))
               for (lo,hi),next_value in itertools.product(PAIRS,NEXT)]
        self.assertEqual(len(cases),7812);self.assertEqual(sum(len(case['queries'])for case in cases),148428)
        self.compare(cases,probe=True)
    def test04_supported_terminal_tuple_faults(self):
        input=label('id',48,57);fixture=dict(steps=[step(input,U)])
        original=history(fixture);faults=[]
        expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][0]=string(key(input,U))
        faults.append((SOURCE.replace(': [label, match[1], new RegExp',': [cacheKey, match[1], new RegExp'),expected))
        expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][1]=string(input)
        faults.append((SOURCE.replace(': [label, match[1], new RegExp',': [label, match[0], new RegExp'),expected))
        expected=copy.deepcopy(original);expected[0]['visibleGraph'][0]['values'][2]=dict(kind='bool',value=True)
        expected[0]['visibleGraph']=expected[0]['visibleGraph'][:1]
        faults.append((SOURCE.replace(': [label, match[1], new RegExp(`^${match[2]}$`)]',': [label, match[1], true]'),expected))
        self.assertEqual(len(faults),3)
        for source,expected in faults:
            self.assertNotEqual(source,SOURCE);self.assertNotEqual(expected,original)
            self.compare([fixture],source=source,expected=[expected])
    def test05_source_pin_and_preserved_baseline(self):
        invoke(['python3','verification/getpattern-cache/source.py','--hono',str(HONO)])
        invoke(['python3','verification/getpattern-cache/check-native.py','--hono',str(HONO)])
    def test06_warm_collision_skips_cold_lookahead_and_cold_refusal(self):
        cases=[]
        for name,(lo,hi) in itertools.product(NAMES,[(48,57),(65,90),(97,122)]):
            input=label(name,lo,hi)
            cases.append(dict(steps=[step(input,U),step(input,string(units('undefined'))),step(input,U)]))
        self.assertEqual(len(cases),15);self.compare(cases)
        # Reversing this history actually reaches67. Native succeeds; the model
        # refuses its unsupported grammar. This is NOT a conformance agreement.
        input=label('id',48,57)
        packet=dict(cases=[dict(steps=[step(input,string(units('undefined')))])])
        result=model(packet);self.assertTrue(result['parsed']);self.assertEqual(result['results'],[[dict(ok=False)]])
        for engine in ['bun',NODE]:
            result=native(packet,engine)[0][0];self.assertTrue(result['ok'])
            self.assertEqual(result['visibleGraph'][0]['values'][0],string(key(input,string(units('undefined')))))
            self.assertEqual(result['visibleGraph'][1]['source'],units(r'^[0-9]+(?=\/undefined)'))

if __name__=='__main__':unittest.main(argv=['getpattern-terminal-cache-tests'])
