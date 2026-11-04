#!/usr/bin/env python3
"""Finite exact-source data-field/preamble evidence, separate from full class adequacy."""
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
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=120,
                          input=None if packet is None else json.dumps(packet))


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/node-initialization/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/node-initialization/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    result = json.loads(result.stdout)
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['transpilation']['verified'] is False
    assert len(result['transpilation']['inputSha256']) == len(result['transpilation']['emittedSha256']) == 64
    return result


def oracle(case):
    owners = [class_index for class_index, count in enumerate(case['counts']) for _ in range(count)]
    instance = dict(methodsLength=0, patternsLength=0, childrenOwnCount=0, childrenNullPrototype=True,
                    pattern='undefined', paramsIsModule=True, methodsPatternsDistinct=True, publicOwnCount=0, prototypeKept=True)
    return dict(instances=[instance]*len(owners), arraysIsolated=True, childrenIsolated=True, sharedParams=True,
                moduleNullPrototype=True, helperCalls=1+len(owners), order=0,
                classBrandMatrix=[[class_index == owner for owner in owners] for class_index in range(len(case['counts']))],
                unbrandedRejected=True)


class NodeInitializationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for name in ['node-initialization', 'nullobject', 'methods-loop']:
            result = invoke(['python3', f'verification/{name}/source.py', '--hono', str(HONO)])
            if result.returncode:
                raise AssertionError(result.stdout+result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        packet = dict(cases=cases)
        self.assertEqual(native(packet)['results'], expected)
        self.assertEqual(model(packet), expected)

    def test_class_identity_and_per_instance_allocations(self):
        cases = [dict(counts=list(counts), baseObjects=1+index%5, baseArrays=index%4,
                      existingStamps=[index, 2*index+17])
                 for index, counts in enumerate(counts for length in range(5) for counts in itertools.product(range(4), repeat=length))]
        self.compare(cases)
        print(f'Private initialization audit: {len(cases)} class/instance contexts, including zero-instance definitions', flush=True)

    def test_seeded_frames_and_long_identity_ranges(self):
        rng = random.Random(1729)
        cases = [dict(counts=[rng.randrange(6) for _ in range(rng.randrange(7))], baseObjects=rng.randrange(1, 12),
                      baseArrays=rng.randrange(12), existingStamps=[rng.randrange(10000) for _ in range(rng.randrange(8))])
                 for _ in range(128)]
        cases += [dict(counts=[0, 32, 0, 16], existingStamps=[999999]), dict(counts=[1]*32), dict(counts=[0]*32)]
        self.compare(cases)
        print(f'Private initialization frame audit: {len(cases)} seeded/long contexts and prior stamps', flush=True)

    def test_source_faults_and_erased_type_controls(self):
        fields = (ROOT/'verification/node-initialization/fields.ts.txt').read_text()
        preamble = (ROOT/'verification/node-initialization/preamble.ts.txt').read_text()
        case = dict(counts=[0, 2, 1])
        faults = [dict(fieldsSource=fields.replace('HandlerSet<T>>[] = []', 'HandlerSet<T>>[] = [null]')),
                  dict(fieldsSource=fields.replace('Node<T>[] = []', 'Node<T>[] = [null]')),
                  dict(fieldsSource=fields.replace('= createNullObject()', '= emptyParams')),
                  dict(fieldsSource=fields.replace('= emptyParams', '= createNullObject()')),
                  dict(fieldsSource=fields.replace('#pattern?: Pattern | string', '#pattern?: Pattern | string = null')),
                  dict(preambleSource=preamble.replace('order = 0', 'order = 7'))]
        for fault in faults:
            packet = dict(cases=[case], **fault)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [oracle(case)])
        for variant in [fields.replace('HandlerSet<T>', 'OtherShape<U>'), fields.replace('#pattern?:', '#pattern:')]:
            packet = dict(cases=[case], fieldsSource=variant)
            self.assertEqual(native(packet)['results'], [oracle(case)])
            self.assertEqual(model(packet), [oracle(case)])

    def test_native_private_add_order_and_boundary_controls(self):
        self.assertEqual(native(dict(scopeProbes=True))['scope'], dict(selfThrows=True, laterThrows=True,
            earlier=1, omittedUndefined=True, privateMethodBeforeField=7, nonextensibleStamp=1,
            duplicateThrows=True, initializerCalls=2, cloneThrows=True))

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-node-initialization-') as temporary:
            base = Path(temporary); script = base/'verification/node-initialization/source.py'
            script.parent.mkdir(parents=True); shutil.copy(ROOT/'verification/node-initialization/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/node-initialization/source.json', 'verification/node-initialization/fields.ts.txt',
                             'verification/node-initialization/preamble.ts.txt', 'HonoLean/Upstream/NodeInitialization/Generated.lean']:
                file = base/relative; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative); file.write_bytes(original)
            clone = base/'checkout'; subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            source = 'src/router/trie-router/node.ts'
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
            file = clone/source; file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(['python3', str(script), '--hono', str(clone)]).returncode, 0)
            self.assertNotEqual(invoke(['bun', 'verification/node-initialization/native.ts', str(clone)], dict(cases=[])).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['node-initialization-tests'])
