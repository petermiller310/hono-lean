#!/usr/bin/env python3
"""Exact count→sparse scheduling, raw UTF16 and independent native controls."""
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
COUNT = (ROOT / 'verification/component-count/count.ts.txt').read_text()
FULL = (ROOT / 'verification/component-count/full.ts.txt').read_text()


def value(kind, **fields):
    return dict(kind=kind, **fields)


U, N = value('undefined'), value('null')
F, T = value('bool', value=False), value('bool', value=True)
Z, ONE = value('number', value=0), value('number', value=7)
S = lambda units: value('string', units=list(units))
A = lambda reference: value('array', ref=reference)
O = lambda reference: value('object', ref=reference)
OPAQUE = dict(internalAccumulator=True)


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=300)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/component-count/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet, runtime='bun'):
    result = invoke([runtime, 'verification/component-count/native.mjs', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    output = json.loads(result.stdout)
    assert output['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert output['checkedPinnedBlobs'] == 315
    assert output['execution']['verified'] is False
    assert output['execution']['fragmentTypeErasure'] is False
    assert output['execution']['countBytes'] == 70
    assert output['execution']['fullBytes'] == 191
    assert output['execution']['sourceOverride'] == ('source' in packet)
    assert output['execution']['accumulatorIDs'] == 'opaque projection; not observed native allocations'
    return output


def truthy(item):
    if item['kind'] in ['null', 'undefined']:
        return False
    if item['kind'] == 'bool':
        return item['value']
    if item['kind'] == 'number':
        return item['value'] != 0
    if item['kind'] == 'string':
        return bool(item['units'])
    return True


def oracle(case, full=True, unit=47):
    """Index-set specification plus own-slot/alias queue transitions.

    No parsed program, scanner, model/native result or source-fault rewrite
    supplies the expected index set or count. Internal slots are masked, never
    asserted to be observable native arrays.
    """
    heap = copy.deepcopy(case['heap'])
    queue, temp = case.get('queue', A(0)), case.get('temp', A(2))
    counts, schedules, advances, retained, traces, opaque = [], [], [], [], [], []

    def array(item):
        return item['kind'] == 'array' and item['ref'] < len(heap)

    def snapshot():
        return copy.deepcopy([OPAQUE if index in opaque else row for index, row in enumerate(heap)])

    for request in case.get('requests', []):
        m = request.get('m', A(1))
        if not array(m):
            return dict(ok=False)
        row = heap[m['ref']]
        if not row or row[0] is None or row[0]['kind'] != 'string':
            return dict(ok=False)
        text = row[0]['units']
        positions = [index for index in range(len(text)) if text[index] == unit]
        count = len(positions)
        counts.append(value('number', value=count))
        opaque.append(len(heap))
        heap.append([S([unit]) for _ in positions])
        traces.append(dict(positions=positions, lastIndexTrace=[0] + [index + 1 for index in positions] + [0],
                           unit=unit, lastIndex=0, match=[[unit] for _ in positions] if positions else None))
        if full:
            if not array(queue):
                return dict(ok=False)
            row = heap[queue['ref']]
            selected = row[count] if count < len(row) and row[count] is not None else U
            if truthy(selected):
                target, fresh = selected, False
            else:
                target, fresh = A(len(heap)), True
                heap.append([])
                row.extend([None] * max(0, count + 1 - len(row)))
                row[count] = target
            if not array(target):
                return dict(ok=False)
            heap[target['ref']].append(copy.deepcopy(request.get('child', O(0))))
            retained.append(copy.deepcopy(target))
            schedules.append(dict(target=copy.deepcopy(target), fresh=fresh, heap=snapshot()))
    for _ in range(case.get('advances', 0)):
        if not array(queue):
            return dict(ok=False)
        row = heap[queue['ref']]
        shifted = row[0] if row and row[0] is not None else U
        heap[queue['ref']] = row[1:]
        if truthy(shifted):
            if not array(temp):
                return dict(ok=False)
            if shifted['kind'] == 'array':
                if not array(shifted):
                    return dict(ok=False)
                suffix = heap[shifted['ref']]
            else:
                suffix = [shifted]
            current = A(len(heap))
            heap.append(copy.deepcopy(heap[temp['ref']] + suffix))
            fresh = True
        else:
            current, fresh = temp, False
        advances.append(dict(shifted=copy.deepcopy(shifted), current=copy.deepcopy(current), fresh=fresh, heap=snapshot()))
    return dict(ok=True, counts=counts, schedules=schedules, advances=advances, retained=retained,
                heap=snapshot(), traces=traces)


def fixture(text, queue=None, repeats=1, advances=0, m=1, child=None, temp=2):
    heap = [copy.deepcopy([] if queue is None else queue), [S(text), S([47, 47])], [O(1)], [O(2)]]
    if m == 0:
        heap[0] = [S(text)]
    return dict(heap=heap, queue=A(0), temp=A(temp), advances=advances,
                requests=[dict(m=A(m), child=O(0) if child is None else child) for _ in range(repeats)])


def raw_cases():
    alphabet = [0, 47, 97, 0xD83D, 0xDE00]
    return [fixture(text) for length in range(5) for text in itertools.product(alphabet, repeat=length)]


def scheduled_cases():
    cases = []
    options = [None, U, N, F, T, Z, ONE, S([]), S([120]), A(0), A(2), A(3)]
    for text in [[], [97], [47], [47, 47], [0xD800, 47, 0xDC00]]:
        for option in options:
            for temp in [0, 2]:
                cases.append(fixture(text, [copy.deepcopy(option)] * 3, repeats=2, advances=2, temp=temp))
    for text in [[], [97], [47], [47, 97, 47], [0xD800, 47]]:
        cases.append(fixture(text, m=0, advances=2))
    for text in [[47] * 32, [47] * 127, [47] * 512, [0] * 32 + [47] + [0xD800, 0xDC00]]:
        cases.append(fixture(text, repeats=3, advances=3, child=A(0)))
    rng = random.Random(176178)
    for _ in range(140):
        text = [rng.choice([0, 47, 97, 0xD800, 0xDC00, 65535]) for _ in range(rng.randrange(30))]
        queue = [copy.deepcopy(rng.choice(options)) for _ in range(rng.randrange(6))]
        cases.append(fixture(text, queue, repeats=rng.randrange(1, 4), advances=rng.randrange(4),
                             child=rng.choice([N, U, A(0), A(1), A(2), O(0)])))
    return cases


class ComponentCountTests(unittest.TestCase):
    def compare(self, cases, runtime='bun', **overrides):
        packet = dict(cases=cases, **overrides)
        modeled = model(packet)
        self.assertTrue(modeled['parsed'])
        observed = native(packet, runtime)
        self.assertEqual(modeled['results'], observed['instrumented'])
        controls = [{key: item for key, item in result.items() if key != 'traces'} for result in modeled['results']]
        self.assertEqual(controls, observed['controls'])
        return modeled['results']

    def test_raw_utf16_count(self):
        cases = raw_cases() + [fixture([47] * 512), fixture([0xD800]), fixture([0xDC00])]
        self.assertEqual(self.compare(cases, full=False), [oracle(item, False) for item in cases])
        atom = COUNT.replace('/\\//g', '/a/g')
        self.assertEqual(self.compare(cases[:80], full=False, source=atom), [oracle(item, False, 97) for item in cases[:80]])
        print(f'Raw UTF16: {len(cases)} count contexts, plus 80 other-unit contexts', flush=True)

    def test_count_schedule_consumer(self):
        cases = scheduled_cases()
        self.assertEqual(self.compare(cases), [oracle(item) for item in cases])
        print(f'Count→schedule→consumer: {len(cases)} initial/repeated/alias/sparse contexts', flush=True)

    def test_source_faults_and_admission(self):
        cases = [fixture([]), fixture([97]), fixture([47]), fixture([47, 97, 47], repeats=2),
                 fixture([47], [A(0), F]), fixture([47], [A(2)] * 3)]
        expected = [oracle(item) for item in cases]
        faults = [FULL.replace('/\\//g', '/a/g'), FULL.replace('m[0]', 'm[1]'), FULL.replace('?? 0', '?? 1'),
                  FULL.replace('[componentCount]', '[0]'), FULL.replace('push(child)', 'push(curNodesQueue)'),
                  FULL.replace('                targetCurNodes.push(child)\n', '')]
        for source in faults:
            self.assertNotEqual(self.compare(cases, source=source), expected, source)
        count_only_fault = COUNT.replace('?.length', '')
        self.assertNotEqual(self.compare(cases, full=False, source=count_only_fault), [oracle(item, False) for item in cases])
        rejected = [COUNT.replace('/\\//g', literal) for literal in ['/\\//', '/\\//gg', '/\\//gi', '/\\//u',
                    '/./g', '/[\\/]/g', '/(a)/g', '/a*/g', '/\\a/g']]
        rejected += [COUNT.replace('m[0].match', 'm[0]?.match'), COUNT.replace('??', '||'),
                     COUNT + 'unknown\n', COUNT + '/* comment */\n', COUNT + 'componentCount = 1\n',
                     COUNT.replace('m[0]', 'unknown[0]')]
        for source in rejected:
            self.assertFalse(model(dict(source=source, full=False, cases=[]))['parsed'], source)
        for source in [FULL.replace('\n', '\r\n'), FULL.rstrip(), FULL + "const label = '/'\n"]:
            self.assertEqual(self.compare(cases, source=source), expected)

    def test_node_and_rejections(self):
        self.assertIsNotNone(NODE, 'Use HONO_NODE or put Node22.22.2 on PATH')
        cases = raw_cases()[:35] + scheduled_cases()[-35:] + [fixture([], repeats=3), fixture([47] * 32, repeats=2)]
        self.assertEqual(self.compare(cases, NODE), [oracle(item) for item in cases])
        invalid = [fixture([]) for _ in range(4)]
        invalid[0]['heap'][1][0] = None
        invalid[1]['heap'][1][0] = U
        invalid[2]['heap'][1][0] = N
        invalid[3]['heap'][1][0] = Z
        self.assertEqual(self.compare(invalid, full=False), [dict(ok=False)] * 4)
        self.assertEqual(self.compare(invalid, NODE, full=False), [dict(ok=False)] * 4)
        for runtime in ['bun', NODE]:
            result = invoke([runtime, 'verification/component-count/boundary.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            observed = json.loads(result.stdout)
            self.assertEqual(observed['standard'], dict(incomingLastIndex=999, slashMatchLength=3,
                             noHit=None, finalLastIndex=0, rawUTF16Count=2, emptyCount=0))
            self.assertEqual(observed['outsideDomain'], dict(objectReceiverCustomMatchCount=77, replacedExecCount=0))
            self.assertFalse(observed['unreachableAccumulatorObserved'])
            self.assertFalse(observed['verified'])

    def test_identity(self):
        command = ['python3', 'verification/component-count/source.py', '--hono', str(HONO)]
        result = invoke(command)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = ['verification/component-count/source.py', 'verification/component-count/source.json',
                     'verification/component-count/count.ts.txt', 'verification/component-count/full.ts.txt',
                     'HonoLean/Upstream/NodeComponentCount/Generated.lean',
                     'verification/queue-schedule/source.json', 'verification/queue-schedule/source.ts.txt']
            for file in files:
                target = root / file
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / file, target)
            for file in files[1:]:
                target = root / file
                before = target.read_bytes()
                if file.endswith('queue-schedule/source.json'):
                    content = json.loads(before); content['fragment']['startByte'] += 1
                    target.write_text(json.dumps(content))
                else:
                    target.write_bytes(before + b'\n')
                result = invoke(['python3', str(root / command[1]), '--hono', str(HONO)])
                self.assertNotEqual(result.returncode, 0, file)
                target.write_bytes(before)
            clone = root / 'hono'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(HONO), str(clone)], check=True, env=ENV)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '--detach', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True, env=ENV)
            source = clone / 'src/router/trie-router/node.ts'
            source.write_bytes(source.read_bytes() + b'\n')
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True, env=ENV)
            result = invoke(['python3', str(root / command[1]), '--hono', str(clone)])
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['component-count'])
