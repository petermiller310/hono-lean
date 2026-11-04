#!/usr/bin/env python3
"""Exact-source queue advance: independent endpoint oracle, aliases and faults."""
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
SOURCE = (ROOT / 'verification/queue-advance/source.ts.txt').read_text()


def value(kind, **fields):
    return dict(kind=kind, **fields)


U, N = value('undefined'), value('null')
F, T = value('bool', value=False), value('bool', value=True)
Z, ONE = value('number', value=0), value('number', value=7)
EMPTY, TEXT = value('string', units=[]), value('string', units=[120])
A = lambda reference: value('array', ref=reference)
O = lambda reference: value('object', ref=reference)


def invoke(command, packet=None, cwd=ROOT):
    return subprocess.run(command, cwd=cwd, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=240)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/queue-advance/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet, runtime='bun'):
    result = invoke([runtime, 'verification/queue-advance/native.mjs', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    output = json.loads(result.stdout)
    assert output['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert output['checkedPinnedBlobs'] == 315
    assert output['execution']['verified'] is False
    assert output['execution']['fragmentTypeErasure'] is False
    assert output['execution']['sourceOverride'] == ('source' in packet)
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
    """Pending head removal, then concatenate CURRENT cells or reuse identity.

    This uses fixture values/identities directly; no parsed syntax, model output,
    source rewrite or native result supplies a readiness fact or expected value.
    """
    heap = copy.deepcopy(case['heap'])
    queue, temp = case['queue'], case['temp']
    steps = []
    for _ in range(case.get('rounds', 1)):
        if queue['kind'] != 'array' or queue['ref'] >= len(heap):
            return dict(ok=False)
        pending = heap[queue['ref']]
        head = pending[0] if pending else U
        heap[queue['ref']] = pending[1:]
        if truthy(head):
            if temp['kind'] != 'array' or temp['ref'] >= len(heap):
                return dict(ok=False)
            if head['kind'] == 'array':
                if head['ref'] >= len(heap):
                    return dict(ok=False)
                suffix = heap[head['ref']]
            else:
                suffix = [head]
            current = A(len(heap))
            heap.append(heap[temp['ref']] + suffix)
            fresh = True
        else:
            current, fresh = temp, False
        steps.append(copy.deepcopy(dict(shifted=head, current=current, fresh=fresh, heap=heap)))
    return dict(ok=True, steps=steps)


def case(queue, temp, *, shared=False, rounds=1, current=None):
    return dict(heap=[queue, temp, [O(1), value('string', units=[0, 55357, 56832, 55296])]],
                queue=A(0), temp=A(0 if shared else 1), rounds=rounds,
                current=U if current is None else current)


def exhaustive():
    choices = [U, N, F, Z, EMPTY, T, ONE, TEXT, A(0), A(1), A(2), O(0)]
    queues = [list(row) for length in range(3) for row in itertools.product(choices, repeat=length)]
    temps = [list(row) for length in range(3) for row in itertools.product([O(0), A(0), A(1)], repeat=length)]
    return [case(queue, temp, shared=shared, current=A(2))
            for queue in queues for temp in temps for shared in [False, True]]


def generated():
    rng = random.Random(209210)
    choices = [U, N, F, Z, EMPTY, T, ONE, TEXT, A(0), A(1), A(2), O(0), O(1),
               value('number', value=-9), value('string', units=[55296, 0, 65535])]
    cases = [case([rng.choice(choices) for _ in range(rng.randrange(15))],
                  [rng.choice(choices) for _ in range(rng.randrange(12))],
                  shared=bool(rng.randrange(2)), rounds=rng.randrange(1, 8),
                  current=rng.choice(choices)) for _ in range(340)]
    # Explicit identity traps: empty shifted array, self/head/temp cycles, reuse
    # on falsy values, retained results, and source-supported rejection branches.
    cases += [case([A(1)], []), case([A(0), O(0)], [O(1)]),
              case([A(0), O(0)], [], shared=True, rounds=3),
              case([A(1), A(0), U, A(2)], [O(0)], rounds=5),
              case([EMPTY, A(2), Z], [O(0)], rounds=4),
              case([value('string', units=[55296, 0])], []),
              case([O(0)], [O(0)]), case([], [], shared=True, rounds=3),
              dict(heap=[[], []], queue=O(0), temp=A(1), current=N),
              dict(heap=[[A(1)], []], queue=A(0), temp=U, current=N),
              dict(heap=[[U], []], queue=A(0), temp=O(0), current=T)]
    for length in [33, 128, 513, 1025]:
        cases.append(case([A(2)] * length, [O(0)] * length, rounds=3))
    return cases


class QueueAdvanceTests(unittest.TestCase):
    def compare(self, cases, source=None):
        packet = dict(cases=cases)
        if source is not None:
            packet['source'] = source
        modeled = model(packet)
        self.assertTrue(modeled['parsed'])
        observed = native(packet)
        self.assertEqual(modeled['results'], observed)
        return modeled['results']

    def test_dense_contract(self):
        cases = exhaustive() + generated()
        results = self.compare(cases)
        self.assertEqual(results, [oracle(item) for item in cases])
        print(f'Queue advance: {len(exhaustive())} exhaustive + {len(generated())} seeded/alias/long/rejection contexts', flush=True)

    def test_faults_and_parser(self):
        cases = [case([A(2), A(1)], [O(0)]), case([], [O(1)]),
                 case([A(0), O(0)], [O(1)]), case([A(1)], []),
                 case([A(0), O(0)], [], shared=True), case([U], [O(0)])]
        expected = [oracle(item) for item in cases]
        faults = [SOURCE.replace('curNodesQueue.shift()', 'curNodesQueue[0]'),
                  SOURCE.replace('shifted ?', '!shifted ?'),
                  SOURCE.replace('tempNodes.concat(shifted)', 'shifted.concat(tempNodes)'),
                  SOURCE.replace('shifted ? tempNodes.concat(shifted) : tempNodes', 'tempNodes'),
                  SOURCE.replace('curNodesQueue.shift()', 'tempNodes.shift()'),
                  SOURCE.replace('tempNodes.concat(shifted)', 'tempNodes.concat(tempNodes)'),
                  SOURCE.replace('shifted ?', 'tempNodes ?')]
        for source in faults:
            results = self.compare(cases, source)
            self.assertNotEqual(results, expected, source)
        # Conservative syntax/authority rejection is separate from runtime faults.
        rejected = [SOURCE + 'shifted = tempNodes\n', SOURCE + 'tempNodes = curNodes\n',
                    SOURCE.replace('curNodes =', 'unknown ='),
                    SOURCE.replace('curNodes =', 'const curNodes ='),
                    SOURCE.replace('concat(shifted)', 'concat()'),
                    SOURCE.replace('concat(shifted)', 'concat(shifted, tempNodes)'),
                    SOURCE.replace('shifted ?', '++curNodes ?'),
                    SOURCE.replace('curNodes =', 'curNodes +='),
                    SOURCE + '\n/* unsupported */\n', SOURCE + 'unconsumed']
        for source in rejected:
            self.assertFalse(model(dict(source=source, cases=[]))['parsed'], source)
        for source in [SOURCE.replace('\n', '\r\n'), SOURCE.replace('const shifted', 'const shifted /* nope */')]:
            if '/*' in source:
                self.assertFalse(model(dict(source=source, cases=[]))['parsed'])
            else:
                self.assertEqual(self.compare(cases, source), expected)

    def test_native_boundaries_and_node(self):
        self.assertIsNotNone(NODE, 'Node22.22.2 is required; use HONO_NODE or put node on PATH')
        cases = generated()[:30] + [case([A(1)], []), case([A(0), O(0)], [], shared=True)]
        self.assertEqual(native(dict(cases=cases), NODE), [oracle(item) for item in cases])
        for runtime in ['bun', NODE]:
            result = invoke([runtime, 'verification/queue-advance/boundary.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # Dangling array references are model-domain errors, not native fixtures.
        invalid = [dict(heap=[[A(9)], []], queue=A(0), temp=A(1)),
                   dict(heap=[[], []], queue=A(9), temp=A(1)),
                   dict(heap=[[A(1)], []], queue=A(0), temp=A(9))]
        self.assertEqual(model(dict(cases=invalid))['results'], [dict(ok=False)] * 3)

    def test_identity(self):
        self.assertEqual(invoke(['python3', 'verification/queue-advance/source.py', '--hono', str(HONO)]).returncode, 0)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for file in ['verification/queue-advance/source.py', 'verification/queue-advance/source.json',
                         'verification/queue-advance/source.ts.txt', 'HonoLean/Upstream/NodeQueueAdvance/Generated.lean']:
                target = root / file
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / file, target)
            for file in ['verification/queue-advance/source.json', 'verification/queue-advance/source.ts.txt',
                         'HonoLean/Upstream/NodeQueueAdvance/Generated.lean']:
                target = root / file
                before = target.read_bytes()
                target.write_bytes(before + b'\n')
                # Whitespace-only JSON metadata changes must also fail freshness.
                result = invoke(['python3', str(root / 'verification/queue-advance/source.py'), '--hono', str(HONO)])
                self.assertNotEqual(result.returncode, 0, file)
                target.write_bytes(before)
            clone = root / 'hono'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(HONO), str(clone)], check=True, env=ENV)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '--detach', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True, env=ENV)
            source = clone / 'src/router/trie-router/node.ts'
            source.write_bytes(source.read_bytes() + b'\n')
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True, env=ENV)
            result = invoke(['python3', str(root / 'verification/queue-advance/source.py'), '--hono', str(clone)])
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['queue-advance'])
