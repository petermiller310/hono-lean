#!/usr/bin/env python3
"""Independent label/capture oracle, actual-source comparisons, faults and identity controls."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from oracle import contexts,observation,descriptor,string,UNDEFINED,pipeline_contexts,pipeline_observation
ROOT=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono',type=Path,required=True)
args=parser.parse_args();HONO=args.hono.resolve()
ENV=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
NODE=os.environ.get('HONO_NODE')or shutil.which('node')
SOURCE=(ROOT/'verification/label-match/full.ts.txt').read_text()
REVISION='5ca49b0720755c585c9a9835f0a479ceea36fb52'

def invoke(command,packet=None,root=ROOT,check=True):
    result=subprocess.run(command,input=None if packet is None else json.dumps(packet),cwd=root,env=ENV,text=True,
                          capture_output=True,timeout=180)
    if check and result.returncode:raise AssertionError(result.stdout+result.stderr)
    return result

def model(packet):return json.loads(invoke(['lake','env','lean','--run','verification/label-match/Driver.lean'],packet).stdout)
def native(packet,engine):
    value=json.loads(invoke([engine,'verification/label-match/native.mjs',str(HONO)],packet).stdout)
    assert value['revision']==REVISION and value['checkedPinnedBlobs']==315
    assert value['verified']is False and value['observerVerified']is False
    assert value['hiddenLiteralObserved']is False and value['protocolTraceNativeObserved']is False
    assert value['plainJavaScript']is True and value['typescriptErasure']is False
    assert value['sourceSha256']==hashlib.sha256(SOURCE.encode()).hexdigest()
    assert value['executedSourceSha256']==hashlib.sha256(packet.get('source',SOURCE).encode()).hexdigest()
    return value['results']

def captures_observation(label,captures):
    base=dict(outerPreserved=True,thisPreserved=True,oldFrames=True)
    if captures is None:return dict(base,result={'kind':'null'},captures=None,view=None,ownNames=None)
    fields={name:descriptor(captures[i])if i<len(captures)else None for i,name in enumerate(['zero','one','two'])}
    fields.update(length=descriptor({'kind':'number','value':len(captures)},False,False),index=descriptor({'kind':'number','value':0}),
                  input=descriptor(string(label)),groups=descriptor(UNDEFINED))
    return dict(base,result={'kind':'array','ref':1},captures=captures,view=fields,
                ownNames=sorted([str(i)for i in range(len(captures))]+['length','index','input','groups']))

class Checks(unittest.TestCase):
    def check_packet(self,cases,source=SOURCE,expected=None,pipeline=False):
        packet=dict(cases=cases,source=source,mode="pipeline"if pipeline else"label")
        expected=expected if expected is not None else[observation(c['label'])for c in cases]
        actual=model(packet);self.assertTrue(actual['parsed']);self.assertEqual(actual['results'],expected)
        for engine in ['bun',NODE]:self.assertEqual(native(packet,engine),expected)
        for case,observed,internal in zip(cases,expected,actual['modelOnly']):
            self.assertEqual(internal['literalCount'],1)
            self.assertEqual(internal['captureArrayCount'],int(observed['result']['kind']=='array'))
            self.assertEqual(internal['literalLastIndex'],descriptor({'kind':'number','value':0},False,False))
            self.assertEqual(internal['literalFlags'],[])
            self.assertTrue(internal['compiledFromStoredSource'])
            self.assertEqual(internal['literalPrototype'],2)
            self.assertTrue(internal['literalExtensible'])
            trace=internal['trace']
            self.assertEqual(trace[0],{'event':'receiver','value':string(case['label'])})
            self.assertEqual(trace[1]['event'],'get');self.assertEqual(trace[1]['key']['units'],[109,97,116,99,104])
            self.assertEqual(trace[2]['event'],'literalAllocated');self.assertEqual(trace[3]['event'],'initialized')
            self.assertEqual(trace[4]['event'],'call')
            # Current eight reads, not a supplied flags result; MODEL ONLY, no native trace equality.
            keys=[e['key']['units']for e in trace if e['event']=='get'and e['key']['kind']=='string']
            names=['match','hasIndices','global','ignoreCase','multiline','dotAll','unicode','unicodeSets','sticky','flags','exec','lastIndex']
            self.assertEqual(keys,[[ord(c)for c in name]for name in names])
            self.assertEqual(trace[-2]['event'],'lastIndex');self.assertEqual(trace[-1]['event'],'executed')
        return actual

    def test01_actual_source_contract(self):
        groups=contexts();cases=sum(groups.values(),[])
        self.assertEqual(len(cases),5193)
        self.check_packet(cases)

    def test02_supported_source_faults(self):
        # Each is executed as source; expected consequences are independently stated.
        variants=[
          (SOURCE.replace(r'\:',r'\@'),[64,105,100],[string([64,105,100]),string([105,100]),UNDEFINED]),
          (SOURCE.replace(r'\})?$',r'\})$'),[58,105,100],None),
          (SOURCE.replace(r'([^\{\}]+)',r'(?:[^\{\}]+)'),[58,105,100,123,120,125],
             [string([58,105,100,123,120,125]),string([120])]),
          (SOURCE.replace('(.+)',r'([^\{\}]+)'),[58,105,100,123,97,125,123,98,125],None),
          (SOURCE.replace(r'[^\{\}]',r'[^\{\}X]'),[58,105,88,100],None)
        ]
        self.assertEqual(len(variants),5)
        for source,label,captures in variants:
            self.assertNotEqual(source,SOURCE)
            changed=captures_observation(label,captures)
            self.assertNotEqual(changed,observation(label))
            self.check_packet([dict(label=label)],source,[changed])

    def test03_selected_full_producer_pipeline(self):
        cases=pipeline_contexts();self.assertEqual(len(cases),3970)
        self.check_packet(cases,expected=[pipeline_observation(c)for c in cases],pipeline=True)

    def test03b_optional_zero_progress_regression(self):
        source='const match = label.match(/^()?$/)'
        self.check_packet([dict(label=[])],source,[captures_observation([],[string([]),UNDEFINED])])
        source='const match = label.match(/^((a?)?)?$/)'
        self.check_packet([dict(label=[]),dict(label=[97])],source,[
            captures_observation([],[string([]),UNDEFINED,UNDEFINED]),
            captures_observation([97],[string([97]),string([97]),string([97])])])
        # Empty captures are valid inside an outer optional that DOES consume.
        source='const match = label.match(/^(()a)?$/)'
        self.check_packet([dict(label=[97])],source,[captures_observation([97],[string([97]),string([97]),string([])])])

    def test04_frontend_and_domain_refusals(self):
        for source in [SOURCE.replace('const','let',1),SOURCE.replace('const match','constmatch'),SOURCE.replace('const match','const$match'),SOURCE.replace('label.match','match.match'),
                       SOURCE+'const x = 1',SOURCE.replace('label.match','label["match"]'),
                       SOURCE.replace('label.match','getLabel().match')]:
            self.assertEqual(model(dict(source=source,cases=[])),{'parsed':False})
        # Valid native flags are outside the no-flags literal model, not a native SyntaxError.
        source=SOURCE.replace('$/)','$/i)')
        result=model(dict(source=source,cases=[dict(label=[58,105,100])]))
        self.assertEqual(result,{'parsed':False})
        self.assertEqual(native(dict(source=source,cases=[dict(label=[58,105,100])]),NODE),[observation([58,105,100])])
        # Native regex search can begin after index0; this source frontend only
        # admits structurally start-anchored programs, matching actual Hono60.
        source='const match = label.match(/a/)'
        self.assertEqual(model(dict(source=source,cases=[])),{'parsed':False})
        result=native(dict(source=source,cases=[dict(label=[98,97])]),NODE)[0]
        self.assertEqual(result['captures'],[string([97])])
        self.assertEqual(result['view']['index'],descriptor({'kind':'number','value':1}))

    def test05_source_and_artifact_identity(self):
        invoke(['python3','verification/label-match/source.py','--hono',str(HONO)])
        with tempfile.TemporaryDirectory(prefix='hono-label-identity-')as directory:
            root=Path(directory);folder=root/'verification/label-match';folder.mkdir(parents=True)
            generated=root/'HonoLean/Upstream/LabelMatch';generated.mkdir(parents=True)
            for name in ['source.py','source.json','full.ts.txt','call.ts.txt','literal.ts.txt']:
                shutil.copyfile(ROOT/'verification/label-match'/name,folder/name)
            shutil.copyfile(ROOT/'HonoLean/Upstream/LabelMatch/Generated.lean',generated/'Generated.lean')
            command=['python3',str(folder/'source.py'),'--hono',str(HONO)]
            invoke(command,root=root)
            for path in [folder/'full.ts.txt',folder/'source.json',folder/'literal.ts.txt',generated/'Generated.lean']:
                old=path.read_bytes();path.write_bytes(old+b' ')
                self.assertNotEqual(invoke(command,root=root,check=False).returncode,0)
                path.write_bytes(old)
            invoke(command,root=root)

    def test06_native_edition_boundary_preserved(self):
        invoke(['python3','verification/label-match/check-native.py','--hono',str(HONO)])

if __name__=='__main__':unittest.main(argv=['label-match-tests'])
