#!/usr/bin/env python3
"""Pinned sparse scheduling/consumption, own holes, aliases and source faults."""
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
SOURCE = (ROOT / 'verification/queue-schedule/source.ts.txt').read_text()


def value(kind, **fields):
    return dict(kind=kind, **fields)


U, N = value('undefined'), value('null')
F, T = value('bool', value=False), value('bool', value=True)
Z, ONE = value('number', value=0), value('number', value=7)
EMPTY, TEXT = value('string', units=[]), value('string', units=[120])
A = lambda reference: value('array', ref=reference)
O = lambda reference: value('object', ref=reference)


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=300)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/queue-schedule/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet, runtime='bun'):
    result = invoke([runtime, 'verification/queue-schedule/native.mjs', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    output = json.loads(result.stdout)
    assert output['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert output['checkedPinnedBlobs'] == 315
    assert output['execution']['verified'] is False
    assert output['execution']['fragmentTypeErasure'] is False
    assert output['execution']['schedulingBytes'] == 121
    assert output['execution']['consumingBytes'] == 109
    assert output['execution']['sourceOverrides'] == [key for key in ['scheduleSource', 'advanceSource'] if key in packet]
    return output['results']


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


def oracle(case):
    """Initial own-slot maps, fresh-slot/reuse rule, then ordered queue removal.

    null transport slots remain holes throughout; an own undefined uses U.
    No parsed program, model/native output or fault rewrite supplies expectations.
    """
    heap = copy.deepcopy(case['heap'])
    queue, temp = case['queue'], case.get('temp', A(2))
    schedules, advances, retained = [], [], []
    for request in case.get('requests', []):
        if queue['kind'] != 'array' or queue['ref'] >= len(heap):
            return dict(ok=False)
        index = request['index']
        if not 0 <= index < 4294967295:
            return dict(ok=False)
        row = heap[queue['ref']]
        selected = row[index] if index < len(row) and row[index] is not None else U
        if truthy(selected):
            target, fresh = selected, False
        else:
            target, fresh = A(len(heap)), True
            heap.append([])
            row.extend([None] * max(0, index + 1 - len(row)))
            row[index] = target
        if target['kind'] != 'array' or target['ref'] >= len(heap):
            return dict(ok=False)
        heap[target['ref']].append(copy.deepcopy(request['child']))
        retained.append(copy.deepcopy(target))
        schedules.append(copy.deepcopy(dict(target=target, fresh=fresh, heap=heap)))
    for _ in range(case.get('advances', 0)):
        if queue['kind'] != 'array' or queue['ref'] >= len(heap):
            return dict(ok=False)
        row = heap[queue['ref']]
        shifted = row[0] if row and row[0] is not None else U
        heap[queue['ref']] = row[1:]
        if truthy(shifted):
            if temp['kind'] != 'array' or temp['ref'] >= len(heap):
                return dict(ok=False)
            if shifted['kind'] == 'array':
                if shifted['ref'] >= len(heap):
                    return dict(ok=False)
                suffix = heap[shifted['ref']]
            else:
                suffix = [shifted]
            current, fresh = A(len(heap)), True
            heap.append(heap[temp['ref']] + suffix)
        else:
            current, fresh = temp, False
        advances.append(copy.deepcopy(dict(shifted=shifted, current=current, fresh=fresh, heap=heap)))
    return dict(ok=True, schedules=schedules, advances=advances, retained=retained, heap=heap)


def case(queue, index, *, child=None, shared=False, repeats=1, advances=0, other=None, temp=None):
    child = O(0) if child is None else child
    requests = [dict(index=index, child=child) for _ in range(repeats)]
    return dict(heap=[queue, [] if other is None else other, [None, O(1)] if temp is None else temp],
                queue=A(0), temp=A(0 if shared else 2), current=A(1),
                requests=requests, advances=advances)


def exhaustive():
    slots = [None, U, N, F, Z, EMPTY, A(0), A(1), A(2), O(0)]
    queues = [list(row) for length in range(3) for row in itertools.product(slots, repeat=length)]
    return [case(queue, index, child=child, advances=4)
            for queue in queues for index in range(4) for child in [O(0), A(0), U]]


def generated():
    rng = random.Random(177178)
    choices = [None, U, N, F, Z, EMPTY, A(0), A(1), A(2), O(0), O(1), T, TEXT,
               value('string', units=[55296, 0, 65535])]
    cases = []
    for _ in range(360):
        rows = [[rng.choice(choices) for _ in range(rng.randrange(9))] for _ in range(3)]
        requests = [dict(index=rng.randrange(12), child=rng.choice([O(0), O(1), A(0), A(1), A(2), U, N, TEXT]))
                    for _ in range(rng.randrange(1, 6))]
        cases.append(dict(heap=rows, queue=A(0), temp=A(rng.randrange(3)), current=O(1),
                          requests=requests, advances=rng.randrange(1, 7)))
    cases += [case([], 5, repeats=3, advances=7), case([A(0)], 0, child=A(0), shared=True, advances=3),
              case([None, U, A(1)], 2, other=[None, O(0)], advances=5),
              case([None, None, A(2)], 2, child=A(2), shared=True, advances=4),
              case([A(1)], 0, child=value('string', units=[55296, 0]), other=[], advances=2),
              case([], 0, child=O(0), repeats=0, advances=3),
              case([None, None], 1, child=N, repeats=2, advances=4)]
    for index in [32, 127, 512]:
        cases.append(case([], index, repeats=3, advances=3))
    return cases


class QueueScheduleTests(unittest.TestCase):
    def compare(self, cases, **overrides):
        packet = dict(cases=cases, **overrides)
        modeled = model(packet)
        self.assertTrue(modeled['parsed'])
        observed = native(packet)
        self.assertEqual(modeled['results'], observed)
        return modeled['results']

    def test_sparse_schedule_and_consume(self):
        cases = exhaustive() + generated()
        self.assertEqual(self.compare(cases), [oracle(item) for item in cases])
        print(f'Sparse schedule: {len(exhaustive())} exhaustive + {len(generated())} seeded/repeated/long contexts', flush=True)

    def test_source_faults_and_admission(self):
        cases = [case([], 2, advances=0), case([None, U], 1, repeats=2),
                 case([A(1)], 0, other=[O(1)]), case([A(0)], 0, child=A(0)),
                 case([A(1), F], 1, other=[O(1)])]
        expected = [oracle(item) for item in cases]
        faults = [SOURCE.replace('[componentCount]', '[0]'),
                  SOURCE.replace('||= []', '||= curNodesQueue'),
                  SOURCE.replace('targetCurNodes.push(child)', 'curNodesQueue.push(child)'),
                  SOURCE.replace('push(child)', 'push(curNodesQueue)'),
                  SOURCE.replace('                targetCurNodes.push(child)\n', ''),
                  SOURCE.replace('||= []', '||= curNodesQueue.shift()')]
        for source in faults:
            results = self.compare(cases, scheduleSource=source)
            self.assertNotEqual(results, expected, source)
        rejected = [SOURCE.replace('||=', '|| ='), SOURCE.replace('||=', '||\n='),
                    SOURCE.replace('||=', '&&='), SOURCE.replace('||=', '??='),
                    SOURCE.replace('curNodesQueue[componentCount]', 'curNodesQueue?.[componentCount]'),
                    SOURCE.replace('componentCount]', '++componentCount]'),
                    SOURCE + 'targetCurNodes = curNodesQueue\n',
                    SOURCE + 'unknown\n', SOURCE + '\n/* unsupported */\n']
        for source in rejected:
            self.assertFalse(model(dict(scheduleSource=source, cases=[]))['parsed'], source)
        for source in [SOURCE.replace('\n', '\r\n'), SOURCE.rstrip(),
                       SOURCE.replace('(curNodesQueue[componentCount] ||= [])', 'curNodesQueue[componentCount] ||= []')]:
            self.assertEqual(self.compare(cases, scheduleSource=source), expected)

    def test_boundary_and_node(self):
        self.assertIsNotNone(NODE, 'Use HONO_NODE or put Node22.22.2 on PATH')
        cases = generated()[:30] + [case([], 4, advances=6), case([A(0)], 0, shared=True, advances=3)]
        self.assertEqual(native(dict(cases=cases), NODE), [oracle(item) for item in cases])
        boundaries = []
        for runtime in ['bun', NODE]:
            result = invoke([runtime, 'verification/queue-schedule/boundary.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            boundaries.append(json.loads(result.stdout))
        recorded = json.loads((ROOT / 'verification/queue-schedule/boundary-results.json').read_text())
        self.assertEqual(recorded['sourceFragmentSha256'], 'f81b14a2daf91271162188b3cb1061728c7dedfdc5581a73eae01caa51c0f198')
        self.assertEqual(boundaries, recorded['observations'])
        # These are model-domain restrictions, not asserted native TypeErrors.
        invalid = [dict(heap=[[A(9)], [], []], queue=A(0), requests=[dict(index=0, child=O(0))]),
                   dict(heap=[[], [], []], queue=A(9), requests=[dict(index=0, child=O(0))]),
                   case([], -1), case([], 4294967295)]
        self.assertEqual(model(dict(cases=invalid))['results'], [dict(ok=False)] * 4)

    def test_identity(self):
        result = invoke(['python3', 'verification/queue-schedule/source.py', '--hono', str(HONO)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = ['verification/queue-schedule/source.py', 'verification/queue-schedule/source.json',
                     'verification/queue-schedule/source.ts.txt', 'HonoLean/Upstream/NodeQueueSchedule/Generated.lean',
                     'verification/queue-advance/source.json', 'verification/queue-advance/source.ts.txt']
            for file in files:
                target = root / file
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / file, target)
            for file in files[1:]:
                target = root / file
                before = target.read_bytes()
                if file.endswith('queue-advance/source.json'):
                    content = json.loads(before); content['fragment']['startByte'] += 1
                    target.write_text(json.dumps(content))
                else:
                    target.write_bytes(before + b'\n')
                result = invoke(['python3', str(root / 'verification/queue-schedule/source.py'), '--hono', str(HONO)])
                self.assertNotEqual(result.returncode, 0, file)
                target.write_bytes(before)
            clone = root / 'hono'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(HONO), str(clone)], check=True, env=ENV)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '--detach', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True, env=ENV)
            source = clone / 'src/router/trie-router/node.ts'
            source.write_bytes(source.read_bytes() + b'\n')
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True, env=ENV)
            result = invoke(['python3', str(root / 'verification/queue-schedule/source.py'), '--hono', str(clone)])
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['queue-schedule'])
