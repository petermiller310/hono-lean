#!/usr/bin/env python3
"""Pinned prefix evidence; header progress probes use explicit fixture bodies."""
import argparse
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
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
HONO = parser.parse_args().hono.resolve()


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
        input=None if packet is None else json.dumps(packet), timeout=240)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/loop-entry/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/loop-entry/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    result = json.loads(result.stdout)
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['headerBodies'] == 'explicit unverified observation continuations'
    return {key:result[key] for key in ['results', 'probes']}


def partition(path):
    fields, field = [], []
    for unit in path:
        if unit == 47:
            fields.append(field)
            field = []
        else:
            field.append(unit)
    fields.append(field)
    return fields[1:] if fields[0] == [] else fields


def oracle(case):
    parts = partition(case.get('path', []))
    outer = None if not parts else dict(index=0,part=dict(kind='string',units=parts[0]),
        isLast=len(parts) == 1,queueEmpty=True)
    inner = None if not parts else dict(index=0,bound=1,nodeIsRoot=True,nodeUndefined=False)
    snapshot = dict(parts=parts,len=len(parts),offsetsNull=True,collectorEmpty=True,pendingEmpty=True,
        singletonNodes=True,resetShared=True,otherKept=True,methodKept=True,outer=outer,inner=inner)
    return dict(snapshots=[snapshot] * (2 if case.get('repeat') else 1),fresh=True,
        oldArraysKept=True,order=case.get('registrations', 0))


def probe_oracle(case):
    bound = case['length']
    values = list(range(bound))
    action = case.get('action', 'keep')
    cap = case.get('cap', 16)
    trace = []
    for index in range(bound):
        value = dict(kind='number',value=values[index]) if index < len(values) else dict(kind='undefined')
        trace.append(dict(index=index,bound=bound,value=value))
        if action == 'grow':
            values.append(99)
        if action == 'shrink':
            values = values[1:]
        if len(trace) >= cap:
            return dict(trace=trace,capped=True,nodes=values)
    return dict(trace=trace,capped=False,nodes=values)


class LoopEntryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for folder in ['loop-entry','search-setup','iteration-setup','class-installation','private-write','methods-push','splitpath']:
            result = invoke(['python3',f'verification/{folder}/source.py','--hono',str(HONO)])
            if result.returncode:
                raise AssertionError(result.stdout + result.stderr)

    def compare(self,cases=None,probes=None):
        cases,probes = cases or [],probes or []
        packet = dict(cases=cases,probes=probes)
        expected = dict(results=[oracle(c) for c in cases],probes=[probe_oracle(c) for c in probes])
        self.assertEqual(native(packet),expected)
        self.assertEqual(model(packet),expected)

    def test_exhaustive_paths_derive_first_indices(self):
        paths = [list(path) for size in range(6) for path in itertools.product([47,120,0,55296],repeat=size)]
        cases = [dict(path=path,repeat=bool(index % 2),registrations=index % 4) for index,path in enumerate(paths)]
        self.compare(cases)
        print(f'Loop-entry audit: {len(cases)} exhaustive source-derived first-entry contexts',flush=True)

    def test_seeded_repeated_frames_and_empty_guard(self):
        rng = random.Random(314159)
        alphabet = [47,47,47,120,121,0,32,55296,56320,65535]
        cases = [dict(path=[rng.choice(alphabet) for _ in range(rng.randrange(48))],
            repeat=bool(index % 2),registrations=index % 9) for index in range(256)]
        cases += [dict(path=path,repeat=True,registrations=32) for path in [[],[47],[47,47],[47] * 96]]
        self.compare(cases)
        print(f'Loop-entry audit: {len(cases)} generated/repeated/empty/old-state contexts',flush=True)

    def test_saved_length_progress_with_controlled_body(self):
        probes = [dict(length=length,action=action) for length,action in itertools.product(range(17),['keep','grow','shrink'])]
        probes += [dict(length=length,action=action,cap=128) for length,action in itertools.product([32,96],['keep','grow','shrink'])]
        probes += [dict(length=2,action=action,cap=1) for action in ['keep','grow','shrink']]
        self.compare(probes=probes)
        print(f'Loop-entry audit: {len(probes)} controlled header/body/update/saved-length probes',flush=True)

    def test_detected_header_faults_and_prefix_boundaries(self):
        outer = (ROOT/'verification/loop-entry/outer.ts.txt').read_text()
        inner = (ROOT/'verification/loop-entry/inner.ts.txt').read_text()
        cases = [dict(path=[],repeat=True),dict(path=[47,120],registrations=2),dict(path=[120,47,121])]
        probes = [dict(length=length,action=action,cap=8) for length,action in itertools.product([0,1,2,5],['keep','grow','shrink'])]
        expected = dict(results=[oracle(c) for c in cases],probes=[probe_oracle(c) for c in probes])
        variants = [('outerSource',outer.replace('i = 0','i = 1')),
            ('outerSource',outer.replace('i < len','i <= len')),
            ('outerSource',outer.replace('i < len','i < 0')),
            ('innerSource',inner.replace('j = 0','j = 1')),
            ('innerSource',inner.replace('curNodes.length','curNodes.length - 1')),
            ('innerSource',inner.replace('curNodes.length','curNodes.length - -1')),
            ('innerSource',inner.replace('j < len2','j <= len2')),
            ('innerSource',inner.replace('j++','len2++'))]
        for key,variant in variants:
            self.assertNotEqual(variant,outer if key == 'outerSource' else inner)
            packet = dict(cases=cases,probes=probes,**{key:variant})
            observed = native(packet)
            self.assertEqual(model(packet),observed,variant)
            self.assertNotEqual(observed,expected,variant)
            if 'len2++' in variant or 'j <= len2' in variant:
                self.assertEqual(observed['results'],expected['results'])
                self.assertNotEqual(observed['probes'],expected['probes'])
        for key,control in [('outerSource',outer.replace('i++)','i++\n)')),
                            ('innerSource',inner.replace(', len2',',\nlen2'))]:
            packet = dict(cases=cases,probes=probes,**{key:control})
            self.assertEqual(native(packet),expected)
            self.assertEqual(model(packet),expected)
        for source in [outer+'}',outer+' const extra = 0',outer.replace('i++','i\n++')]:
            rejected = invoke(['lake','env','lean','--run','verification/loop-entry/Driver.lean'],
                dict(cases=[],probes=[],outerSource=source))
            self.assertNotEqual(rejected.returncode,0,source)

    def test_source_artifacts_and_hidden_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-loop-entry-') as temporary:
            base=Path(temporary);script=base/'verification/loop-entry/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT/'verification/loop-entry/source.py',script)
            command=['python3',str(script),'--hono',str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode,0)
            self.assertEqual(invoke(command).returncode,0)
            for relative in ['verification/loop-entry/source.json','verification/loop-entry/outer.ts.txt',
                             'verification/loop-entry/inner.ts.txt','HonoLean/Upstream/NodeLoopEntry/Generated.lean']:
                file=base/relative;saved=file.read_bytes();file.write_bytes(saved+b'\n')
                self.assertNotEqual(invoke(command).returncode,0,relative)
                file.write_bytes(saved)
            clone=base/'checkout'
            subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)],check=True)
            source='src/router/trie-router/node.ts'
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged',source],check=True)
            file=clone/source;file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(['python3',str(script),'--hono',str(clone)]).returncode,0)
            self.assertNotEqual(invoke(['bun','verification/loop-entry/native.ts',str(clone)],dict(cases=[])).returncode,0)

    def test_native_header_boundaries(self):
        node=os.environ.get('HONO_NODE') or shutil.which('node')
        self.assertIsNotNone(node,'Node must be on PATH or supplied through HONO_NODE')
        for runtime,version in [('bun','1.4.0'),(node,'22.22.2')]:
            result=invoke([runtime,'verification/loop-entry/boundaries.mjs'])
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            observed=json.loads(result.stdout)
            self.assertEqual(observed['groups'],6)
            self.assertEqual(observed['version'],version)


if __name__=='__main__':
    unittest.main(argv=['loop-entry-tests'])
