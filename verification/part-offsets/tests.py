#!/usr/bin/env python3
"""Pinned lazy offsets: split alignment, cache reuse, scope and source faults."""
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
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
HONO = parser.parse_args().hono.resolve()
NODE = os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE = (ROOT / 'verification/part-offsets/full.ts.txt').read_text()
PREPARE = (ROOT / 'verification/part-offsets/prepare.ts.txt').read_text()


def value(kind, **fields):
    return dict(kind=kind, **fields)


U, N = value('undefined'), value('null')
F = value('bool', value=False)
Z = value('number', value=0)
S = lambda units: value('string', units=list(units))
A = lambda ref: value('array', ref=ref)
O = lambda ref: value('object', ref=ref)
NUM = lambda integer: value('number', value=integer)


def parts_of(path):
    """Independent delimiter positions; no native/model split implementation."""
    markers = [-1] + [index for index in range(len(path)) if path[index] == 47] + [len(path)]
    pieces = [path[left + 1:right] for left, right in zip(markers, markers[1:])]
    return pieces[1:] if pieces and not pieces[0] else pieces


def fixture(path, cache=N, indices=None):
    parts = parts_of(list(path))
    return dict(heap=[[O(0), U]], path=list(path), cache=copy.deepcopy(cache), split=True,
                indices=list(range(len(parts))) if parts and indices is None else ([0] if indices is None else indices))


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=300)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/part-offsets/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet, runtime='bun'):
    result = invoke([runtime, 'verification/part-offsets/native.mjs', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    output = json.loads(result.stdout)
    assert output['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert output['checkedPinnedBlobs'] == 315
    assert output['execution']['verified'] is False
    assert output['execution']['fragmentTypeErasure'] is False
    assert output['execution']['importedPinnedSplitModule'] is True
    assert output['execution']['sourceBytes'] == (276 if packet.get('prepareOnly') else 338)
    assert output['execution']['sourceOverride'] == ('source' in packet)
    return [{key: item for key, item in result.items() if key != 'wrapperSha256'} for result in output['results']]


def truthy(item):
    return (item['kind'] not in ['null', 'undefined'] and
            (item['kind'] != 'bool' or item['value']) and
            (item['kind'] != 'number' or item['value'] != 0) and
            (item['kind'] != 'string' or bool(item['units'])))


def oracle(case, prepare_only=False):
    heap, path, cache = copy.deepcopy(case['heap']), case['path'], copy.deepcopy(case['cache'])
    if case.get('split'):
        parts = [S(part) for part in parts_of(path)]
        part_ref, length = len(heap), len(parts)
        heap.append(parts)
    else:
        part_ref = case.get('parts', {}).get('ref')
        length = case.get('len')
    steps = []
    for index in case.get('indices', [0]):
        old = copy.deepcopy(cache)
        fresh = not truthy(cache)
        if fresh:
            if length is None:
                return dict(ok=False)
            count = max(length, 0)
            if count:
                if part_ref is None or not 0 <= part_ref < len(heap) or count > len(heap[part_ref]):
                    return dict(ok=False)
                pieces = heap[part_ref][:count]
                if any(piece['kind'] != 'string' for piece in pieces):
                    return dict(ok=False)
            else:
                pieces = []
            # Independent prefix-size formula, not a simulated offset loop.
            start = int(bool(path) and path[0] == 47)
            table = [NUM(start + at + sum(len(piece['units']) for piece in pieces[:at])) for at in range(count)]
            cache = A(len(heap)); heap.append(table)
        step = dict(cache=copy.deepcopy(cache), reused=cache == old, fresh=fresh, scope=True, heap=copy.deepcopy(heap))
        if not prepare_only:
            if cache['kind'] != 'array' or cache['ref'] >= len(heap) or index < 0:
                return dict(ok=False)
            row = heap[cache['ref']]
            entry = row[index] if index < len(row) else U
            if entry['kind'] == 'undefined':
                cut = 0
            elif entry['kind'] == 'number':
                relative = entry['value']
                cut = max(len(path) + relative, 0) if relative < 0 else min(relative, len(path))
            else:
                return dict(ok=False)
            step['rest'] = S(path[cut:])
        steps.append(step)
    return dict(ok=True, steps=steps, importedSplit=bool(case.get('split')))


def source_cases():
    cases = [fixture(path) for size in range(4) for path in itertools.product([0, 47, 97, 0xD800, 0xDC00], repeat=size)]
    special = [[], [47], [47, 47], [47, 97, 47, 47, 98, 47], [97, 47, 98, 47, 47],
               [0xD83D, 0xDE00, 47, 945, 47], [47, 0xD800, 47, 0xDC00]]
    for path in special:
        for cache in [N, U, F, Z, S([])]:
            cases.append(fixture(path, cache, [0, 0, max(0, len(parts_of(path)) - 1)]))
    rng = random.Random(146154)
    for _ in range(140):
        path = [rng.choice([0, 47, 97, 98, 0xD800, 0xDC00]) for _ in range(rng.randrange(35))]
        cases.append(fixture(path, indices=[0, max(0, len(parts_of(path)) - 1), 0]))
    for size in [32, 127, 512]:
        cases.append(fixture([47] * size, indices=[0, size - 1, 0]))
    return cases


def cached_cases():
    cases = []
    for row in [[], [NUM(0)], [NUM(2)], [NUM(-3)], [NUM(999)], [NUM(-999)], [U], [NUM(0), NUM(2), NUM(6)]]:
        for path in [[97, 98, 99, 47, 100, 101, 102], [47, 97, 47, 47, 98, 47], []]:
            cases.append(dict(heap=[copy.deepcopy(row)], path=path, cache=A(0), indices=[0, 1, 5]))
    for path in [[], [47], [97, 98, 99]]:
        cases.append(dict(heap=[], path=path, cache=N, len=0, indices=[0, 2]))
    for path in [[97, 47, 98], [47, 97, 47, 47, 98, 47]]:
        for length in [-1, 0, 1, 2, 3]:
            cases.append(dict(heap=[[S([97]), S([98])]], parts=A(0), len=length,
                              path=path, cache=N, indices=[0, 1]))
    # Cache is also parts; body must not read the numeric array as string parts.
    cases.append(dict(heap=[[NUM(2)]], parts=A(0), path=[97, 98, 99, 47, 100], cache=A(0), indices=[0]))
    # An incorrect cache can cut inside a surrogate pair; there is no repair.
    cases.append(dict(heap=[[NUM(1)]], path=[0xD83D, 0xDE00, 47, 97], cache=A(0), indices=[0]))
    return cases


class PartOffsetTests(unittest.TestCase):
    def compare(self, cases, runtime='bun', **overrides):
        packet = dict(cases=cases, **overrides)
        modeled = model(packet)
        self.assertTrue(modeled['parsed'])
        observed = native(packet, runtime)
        self.assertEqual(modeled['results'], observed)
        return modeled['results']

    def test_source_split_build_reuse(self):
        cases = source_cases()
        self.assertEqual(self.compare(cases), [oracle(case) for case in cases])
        print(f'Offsets: {len(cases)} actual-split/rawUTF16/fresh/reused/long contexts', flush=True)

    def test_cached_and_zero_loop(self):
        cases = cached_cases()
        self.assertEqual(self.compare(cases), [oracle(case) for case in cases])
        self.assertEqual(self.compare(cases, prepareOnly=True), [oracle(case, True) for case in cases])
        print(f'Cache/zero/wrong-input: {len(cases)} contexts, full and prepare-only', flush=True)

    def test_source_faults_and_admission(self):
        cases = [fixture(path, indices=[0, 1, 2]) for path in [[47, 97, 47, 98, 47], [97, 47, 98, 47, 99], [47, 47]]]
        cases.append(dict(heap=[[NUM(2)]], path=[97, 98, 99, 47, 100], cache=A(0), indices=[0]))
        expected = [oracle(case) for case in cases]
        faults = [SOURCE.replace('? 1 : 0', '? 0 : 0'), SOURCE.replace('length + 1', 'length + 0'),
                  SOURCE.replace('partOffsets[p] = offset', 'partOffsets[0] = offset'),
                  SOURCE.replace('partOffsets[p] = offset', 'partOffsets[p] = offset + 1'),
                  SOURCE.replace('partOffsets[i]', 'partOffsets[0]'), SOURCE.replace('if (!partOffsets)', 'if (partOffsets)'),
                  SOURCE.replace('p < len;', 'p < len - 1;')]
        executed = 0
        for source in faults:
            self.assertTrue(model(dict(cases=[], source=source))['parsed'], source)
            self.assertNotEqual(self.compare(cases, source=source), expected, source)
            executed += 1
        self.assertEqual(executed, 7)
        rejected = [SOURCE.replace('+=', '+ ='), SOURCE.replace('+=', '-='), SOURCE.replace('+=', '??='),
                    SOURCE.replace('p++)', 'p\n++)'), SOURCE.replace('p++)', '++p)'),
                    SOURCE.replace('let offset', 'const offset'), SOURCE.replace('let p = 0', 'const p = 0'),
                    SOURCE.replace('offset +=', 'len +='), SOURCE.replace('offset +=', 'unknown +='),
                    SOURCE.replace('let offset = path[0]', 'let offset = offset[0]'),
                    SOURCE.replace('parts[p].length + 1', 'callback()'), SOURCE + 'unknown\n', SOURCE + '/* trailing */\n']
        for source in rejected:
            self.assertFalse(model(dict(cases=[], source=source))['parsed'], source)
        for source in [SOURCE.replace('\n', '\r\n'), SOURCE.rstrip(),
                       SOURCE.replace('offset += parts[p].length + 1', 'offset += (parts[p].length + 1)')]:
            if source == SOURCE: continue
            self.assertEqual(self.compare(cases, source=source), expected)

    def test_node_and_boundaries(self):
        self.assertIsNotNone(NODE, 'Use HONO_NODE or put Node22.22.2 on PATH')
        cases = source_cases()[::11] + cached_cases()
        self.assertEqual(self.compare(cases, NODE), [oracle(case) for case in cases])
        for runtime in ['bun', NODE]:
            result = invoke([runtime, 'verification/part-offsets/boundary.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            output = json.loads(result.stdout)
            self.assertFalse(output['verified'])
            self.assertEqual(output['cached'], dict(emptyReused=True, emptyRest='abc/def', wrongRest='c/def',
                             holeReadUndefined=True, holeOwn0=False, negativeRest='def', largeRest='', ownUndefinedRest='abc/def'))
            self.assertEqual(output['outsideNumericDomain'], dict(capturedBeforeRHS=3, roundedBeyondSafe=2**53, stringConcatenation='12'))

    def test_identity(self):
        result = invoke(['python3', 'verification/part-offsets/source.py', '--hono', str(HONO)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = ['verification/part-offsets/source.py', 'verification/part-offsets/source.json',
                     'verification/part-offsets/full.ts.txt', 'verification/part-offsets/prepare.ts.txt',
                     'verification/part-offsets/slice.ts.txt', 'HonoLean/Upstream/NodePartOffsets/Generated.lean']
            for file in files:
                path = root / file; path.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(ROOT / file, path)
            for file in files[1:]:
                path = root / file; before = path.read_bytes(); path.write_bytes(before + b'\n')
                result = invoke(['python3', str(root / files[0]), '--hono', str(HONO)])
                self.assertNotEqual(result.returncode, 0, file); path.write_bytes(before)
            clone = root / 'hono'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(HONO), str(clone)], check=True, env=ENV)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '--detach', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True, env=ENV)
            path = clone / 'src/router/trie-router/node.ts'; path.write_bytes(path.read_bytes() + b'\n')
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True, env=ENV)
            result = invoke(['python3', str(root / files[0]), '--hono', str(clone)])
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['part-offsets'])
