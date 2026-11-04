#!/usr/bin/env python3
"""Selected actual60/62/67 + direct closed exec versus independent language."""
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
from oracle import units,label,expected

ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--hono',type=Path,required=True)
HONO=parser.parse_args().hono.resolve();ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/getpattern-body/body.ts.txt').read_text()
def invoke(command,packet=None,root=ROOT,check=True):
    result=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=root,env=ENV,text=True,capture_output=True,timeout=240)
    if check and result.returncode:raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)if packet is not None and check else result
def model(cases,source=SOURCE):
    result=invoke(['lake','env','lean','--run','verification/getpattern-lookahead/Driver.lean'],dict(cases=cases,source=source))
    assert result['parsed']is True
    return result['results']
def native(cases,engine,source=SOURCE,actual_module=False):
    result=invoke([engine,'verification/getpattern-lookahead/native.mjs',str(HONO)],dict(cases=cases,source=source,actualModule=actual_module))
    for key in ['verified','observerVerified','typescriptLoaderVerified','nativeLanguageAdequacyVerified','selectedSourceExtractionVerified','hiddenAllocationsObserved']:
        assert result[key]is False,key
    assert result['checkedPinnedBlobs']==315 and result['sourceBytes']==38 and result['tupleBytes']==60
    assert result['ancestorGuardsExecuted']==actual_module and result['actualModule']==actual_module
    return result['results']
def fixture(name,lower=97,upper=122,next_value='tail',queries=None,**extra):
    name=units(name)if isinstance(name,str)else name
    next_value=units(next_value)if isinstance(next_value,str)else next_value
    if queries is None:
        queries=[[],[lower],[lower,47]+next_value,[upper,upper,47]+next_value+[47,0,0xD800],
                 [lower,47]+next_value+[115],[47]+next_value,[lower,47]+next_value[:-1],
                 [lower,47,95]+next_value,[lower,0,47]+next_value,[lower,47]+next_value+[13,10,0x2028,0x2029]]
    return dict(name=name,lower=lower,upper=upper,label=label(name,lower,upper),next=next_value,queries=queries,**extra)
def full_module_cases():
    return [fixture('full'+str(i),lo,hi,next_value,lastIndex=index,writable=writable)
            for i,(lo,hi,next_value,index,writable)in enumerate([
                (97,122,'tail',0,True),(48,57,'A9',7,False),(65,122,'Z',-3,True),
                (48,122,'tail2',9007199254740991,False),(65,90,'next',0,False),(48,48,'X',17,True)])]

class Checks(unittest.TestCase):
    def compare(self,cases,source=SOURCE,answers=None):
        answers=answers if answers is not None else[expected(case)for case in cases]
        self.assertEqual(model(cases,source),answers)
        for engine in ['bun',NODE]:self.assertEqual(native(cases,engine,source),answers)
    def test01_endpoints_names_and_literal_next(self):
        ends=[48,57,65,90,97,122]
        ranges=[(lo,hi)for lo in ends for hi in ends if lo<=hi]
        cases=[fixture(name,lo,hi,next_value)for name,(lo,hi),next_value in itertools.product(
            ['id','i\nj','名','\ud800\x00\udc00'],ranges,['A','tail','X9'])]
        self.assertEqual(len(cases),252);self.assertEqual(sum(len(c['queries'])for c in cases),2520)
        self.compare(cases)
    def test02_assertion_is_not_consumed_or_a_segment_boundary(self):
        queries=[units(x)for x in ['abc/tail','abc/tail/rest','abc/tails','abc/tailXYZ','abc/ta','abc/Tail','abc/xtail','/tail','abc/tail\n','abc/tail\ud800']]
        case=fixture('span',queries=queries);self.compare([case])
        observations=expected(case)['queries']
        for index in [0,1,2,3,8,9]:self.assertEqual(observations[index]['value']['values'],[units('abc')])
        for index in [4,5,6,7]:self.assertIsNone(observations[index]['value'])
    def test03_cross_gap_ranges_contain_punctuation_but_not_slash(self):
        queries=[units(x)for x in [':/tail','@/tail','[/tail','\\/tail','_/tail','`/tail','A/tail','z/tails','/tail','A//tail']]
        cases=[fixture('gap'+str(i),lo,hi,queries=queries)for i,(lo,hi)in enumerate([(48,122),(65,122),(48,65)])]
        self.compare(cases)
    def test04_current_lastindex_get_does_not_move_nonglobal_start(self):
        cases=[fixture('index'+str(i),lastIndex=value,writable=writable)for i,(value,writable)in enumerate(itertools.product([-3,0,7,9007199254740991],[False,True]))]
        self.assertEqual(len(cases),8);self.compare(cases)
    def test05_supported_source_faults(self):
        cases=[fixture('fault',queries=[units('abc/tail'),units('abc/Ztail'),units('abc/Ztails')])]
        faults=[(SOURCE.replace('[cacheKey, match[1], new RegExp','[label, match[1], new RegExp'),dict(tuple_label=True)),
                (SOURCE.replace('[cacheKey, match[1], new RegExp','[cacheKey, match[0], new RegExp'),dict(tuple_whole_match=True)),
                (SOURCE.replace('`${label}#${next}`','`${label}@${next}`'),dict(key_separator=64)),
                (SOURCE.replace('(?=/${next})','(?=/Z${next})'),dict(assertion_prefix=[90]))]
        self.assertEqual(len(faults),4)
        for source,changes in faults:
            answers=[expected(case,**changes)for case in cases]
            self.assertNotEqual(source,SOURCE);self.assertNotEqual(answers,[expected(case)for case in cases])
            self.compare(cases,source,answers)
    def test06_unsupported_grammar_is_not_normalized_to_agreement(self):
        cases=[fixture('frontier'+str(i),next_value=value)for i,value in enumerate(['','tail_name','ta.il','名','ta\nil'])]
        self.assertEqual(model(cases),[dict(ok=False)]*5)
        for engine in ['bun',NODE]:
            actual=native(cases,engine)
            self.assertTrue(all(row['ok']for row in actual))
        source=SOURCE.replace('new RegExp(`^','new RegExp(`')
        case=fixture('unanchored',queries=[units('#abc/tail')])
        self.assertEqual(model([case],source),[dict(ok=False)])
        for engine in ['bun',NODE]:
            result=native([case],engine,source)[0]
            self.assertTrue(result['ok']);self.assertEqual(result['queries'][0]['value']['index'],1)
    def test07_source_and_generated_identity(self):
        invoke(['python3','verification/getpattern-lookahead/source.py','--hono',str(HONO)])
        with tempfile.TemporaryDirectory(prefix='hono-lookahead-identity-')as directory:
            root=Path(directory)
            copies=['verification/getpattern-lookahead/'+name for name in ['source.py','source.json','constructor.ts.txt','tuple.ts.txt','line.ts.txt','label-declaration.ts.txt','key-declaration.ts.txt']]
            copies+=['HonoLean/Upstream/GetPatternLookahead/Generated.lean','verification/getpattern-body/body.ts.txt','HonoLean/Upstream/GetPatternBody/Generated.lean']
            for name in copies:
                target=root/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,target)
            command=['python3',str(root/copies[0]),'--hono',str(HONO)];invoke(command,root=root)
            for name in copies[1:-1]:
                file=root/name;before=file.read_bytes();file.write_bytes(before+b' ')
                self.assertNotEqual(invoke(command,root=root,check=False).returncode,0);file.write_bytes(before)
            file=root/copies[-1];before=file.read_bytes()
            file.write_bytes(before.replace(b'def pinnedBody : String := "',b'def pinnedBody : String := "x',1))
            self.assertNotEqual(invoke(command,root=root,check=False).returncode,0);file.write_bytes(before)
            invoke(command,root=root)
    def test08_actual_full_module_finite_controls(self):
        cases=full_module_cases();answers=[expected(case)for case in cases]
        evidence=json.loads((ROOT/'verification/getpattern-lookahead/module-control-evidence.json').read_text())
        self.assertFalse(evidence['verified']);self.assertTrue(evidence['nativeOnly'])
        self.assertEqual(model(cases),answers)
        for engine,record in zip(['bun',NODE],evidence['records']):
            actual=invoke([engine,'verification/getpattern-lookahead/native.mjs',str(HONO)],dict(cases=cases,actualModule=True))
            self.assertEqual(actual,record);self.assertEqual(actual['results'],answers)
    def test09_current_constructor_rejection_remains_model_boundary(self):
        cases=[fixture('badConstructor',constructorKind='number')]
        self.assertEqual(model(cases),[dict(ok=False)])
        for engine in ['bun',NODE]:
            result=native(cases,engine)[0]
            self.assertFalse(result['ok']);self.assertEqual(result['errorName'],'TypeError')

if __name__=='__main__':unittest.main(argv=['getpattern-lookahead-tests'])
