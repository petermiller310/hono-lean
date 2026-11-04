#!/usr/bin/env python3
"""Finite pinned-source/model/independent-oracle evidence for search startup."""
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
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/search-setup/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/search-setup/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    result = json.loads(result.stdout)
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['transpilation']['verified'] is False
    assert result['transpilation']['importedPinnedSplit'] == ('splitSource' not in packet)
    return result


def partition(path):
    """Independent delimiter scan over UTF16 units, preserving empty fields."""
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
    receiver = case.get('receiver', 'root')
    if receiver not in ['root', 'other']:
        return dict(ok=False)
    parts = partition(case.get('path', []))
    i = case.get('i', 0)
    outer = None if i >= len(parts) else dict(part=parts[i], isLast=i + 1 == len(parts),
        queueFresh=True, nodeIsReceiver=True)
    snapshot = dict(parts=parts, len=len(parts), offsetsNull=True, collectorEmpty=True,
        pendingEmpty=True, rootAlias=True, singletonNodes=True, resetShared=receiver == 'root',
        otherKept=receiver != 'other', methodKept=True, outer=outer)
    return dict(ok=True, snapshots=[snapshot] * (2 if case.get('repeat') else 1), fresh=True,
        oldArraysKept=True, order=case.get('registrations', 0))


class SearchSetupTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for folder in ['search-setup', 'splitpath', 'iteration-setup', 'class-installation', 'private-write', 'methods-push']:
            result = invoke(['python3', f'verification/{folder}/source.py', '--hono', str(HONO)])
            if result.returncode:
                raise AssertionError(result.stdout + result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        self.assertEqual(native(dict(cases=cases))['results'], expected)
        self.assertEqual(model(dict(cases=cases)), expected)

    def test_exhaustive_utf16_paths_and_source_allocations(self):
        paths = [list(path) for n in range(6) for path in itertools.product([47, 120, 0, 55296], repeat=n)]
        cases = [dict(path=path, registrations=n % 4, repeat=bool(n % 2)) for n, path in enumerate(paths)]
        self.compare(cases)
        print(f'Search startup audit: {len(cases)} exhaustive UTF16 delimiter/allocation contexts', flush=True)

    def test_seeded_frames_repeated_search_and_derived_indices(self):
        rng = random.Random(271828)
        alphabet = [47, 47, 47, 120, 121, 0, 32, 37, 55296, 56320, 65535]
        cases = []
        for n in range(384):
            path = [rng.choice(alphabet) for _ in range(rng.randrange(48))]
            parts = partition(path)
            cases.append(dict(path=path, registrations=n % 9, repeat=bool(n % 2),
                i=rng.randrange(len(parts)) if parts else 0, receiver=rng.choice(['root', 'other'])))
        cases += [dict(path=path, registrations=32, repeat=True, i=i) for path, i in [
            ([47] * 96, 95), ([120] * 128, 0), ([47, 55296, 56320, 47, 55357, 56832, 47], 2),
            ([], 0), ([47], 0), ([47, 47], 1), ([47, 120, 47], 1)]]
        cases += [dict(path=[47, 120], receiver=receiver) for receiver in ['foreign', 'plain', 'u', 'n']]
        self.compare(cases)
        print(f'Search startup audit: {len(cases)} generated/frame/repeated-call/index/boundary contexts', flush=True)

    def test_source_faults_execute_and_metadata_is_retained(self):
        source = (ROOT / 'verification/search-setup/startup.ts.txt').read_text()
        split = (ROOT / 'verification/splitpath/splitPath.ts.txt').read_text()
        cases = [dict(path=[47,120,47], registrations=2, repeat=True, i=1),
                 dict(path=[120,47,121], registrations=1)]
        variants = [
            ('startupSource', source.replace('HandlerParamsSet<T>[] = []', 'HandlerParamsSet<T>[] = [this]')),
            ('startupSource', source.replace('this.#params = emptyParams', 'this.#params = this.#params')),
            ('startupSource', source.replace('curNodes = [curNode]', 'curNodes = []')),
            ('startupSource', source.replace('splitPath(path)', "splitPath('')")),
            ('startupSource', source.replace('curNodesQueue: Node<T>[][] = []', 'curNodesQueue: Node<T>[][] = curNodes')),
            ('startupSource', source.replace('parts.length', 'parts.length - 1')),
            ('startupSource', source.replace('partOffsets: number[] | null = null', 'partOffsets: number[] | null = 0')),
            ('splitSource', split.replace("split('/')", "split('x')")),
            ('splitSource', split.replace("paths[0] === ''", "paths[0] === 'x'")),
        ]
        expected = [oracle(case) for case in cases]
        for key, variant in variants:
            self.assertNotEqual(variant, source if key == 'startupSource' else split)
            packet = dict(cases=cases, **{key:variant})
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed, variant)
            self.assertNotEqual(observed, expected, variant)
        control = source.replace('number[] | null', 'null | number[]')
        packet = dict(cases=cases, startupSource=control)
        self.assertEqual(native(packet)['results'], expected)
        self.assertEqual(model(packet), expected)

    def test_identity_artifacts_and_hidden_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-search-setup-') as temporary:
            base = Path(temporary)
            script = base / 'verification/search-setup/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/search-setup/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/search-setup/source.json', 'verification/search-setup/startup.ts.txt',
                             'HonoLean/Upstream/NodeSearchSetup/Generated.lean']:
                file = base / relative
                saved = file.read_bytes()
                file.write_bytes(saved + b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative)
                file.write_bytes(saved)

            clone = base / 'checkout'
            subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            for source in ['src/router/trie-router/node.ts', 'src/utils/url.ts']:
                subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
                file = clone / source
                saved = file.read_bytes()
                file.write_bytes(saved + b'\n')
                self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
                self.assertNotEqual(invoke(['bun', 'verification/search-setup/native.ts', str(clone)], dict(cases=[])).returncode, 0)
                if source.endswith('node.ts'):
                    self.assertNotEqual(invoke(['python3', str(script), '--hono', str(clone)]).returncode, 0)
                file.write_bytes(saved)

    def test_native_call_boundaries(self):
        node = os.environ.get('HONO_NODE') or shutil.which('node')
        self.assertIsNotNone(node, 'Node must be on PATH or supplied through HONO_NODE')
        for runtime in ['bun', node]:
            result = invoke([runtime, 'verification/search-setup/call-probes.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            observed = json.loads(result.stdout)
            self.assertEqual(observed['groups'], 6)
            self.assertEqual(observed['moduleThis'], 'null' if runtime == 'bun' else 'undefined')


if __name__ == '__main__':
    unittest.main(argv=['search-setup-tests'])
