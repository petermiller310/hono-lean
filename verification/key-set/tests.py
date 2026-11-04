#!/usr/bin/env python3
"""Evidence for three source operations on supplied string-add event sequences."""
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
args = parser.parse_args()
HONO = args.hono.resolve()


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def invoke(command, document=None):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(document):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/key-set/Driver.lean'], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native_packet(document):
    result = invoke(['bun', 'verification/key-set/native.ts', str(HONO)], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    packet = json.loads(result.stdout)
    assert packet['runtime'] == '1.4.0'
    assert packet['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert packet['transpilation']['loader'] == 'ts'
    assert packet['transpilation']['verified'] is False
    return packet


def first_occurrences(events):
    # Independent input-index condition, rather than the interpreter's Set fold.
    return [key for index, key in enumerate(events) if key not in events[:index]]


def expected(case):
    first = first_occurrences(case['names'])
    final = first_occurrences(case['names'] + case.get('later', []))
    count, later = len(case['names']), len(case.get('later', []))
    return dict(setRef=1, freshSet=True, outerKept=True, addReturnedAlias=True,
                inputFrameKept=True, snapshots=[dict(ref=count+2, keys=first), dict(ref=count+3, keys=first), dict(ref=count+later+4, keys=final)],
                firstUnchanged=True, distinctArrays=True, setKeys=final, frameKept=True)


class KeySetTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/key-set/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def check_cases(self, cases, **variants):
        packet = dict(cases=cases, **variants)
        oracle = [expected(case) for case in cases]
        self.assertEqual(native_packet(packet)['results'], oracle)
        self.assertEqual(model(packet), oracle)

    def test_first_occurrence_order_utf16_and_snapshots(self):
        alphabet = [units(text) for text in ['', 'id', '__proto__', '\ud800']]
        cases = [dict(names=list(sequence), later=[units('constructor'), units('id')])
                 for length in range(5) for sequence in itertools.product(alphabet, repeat=length)]
        varied = [units(text) for text in ['', '\0', 'constructor', 'é', 'e\u0301', '\ud834\udd1e', '\ud800', '\udc00', '/', ':id']]
        rng = random.Random(1729)
        for _ in range(384):
            cases.append(dict(names=[rng.choice(varied) for _ in range(rng.randrange(20))],
                              later=[rng.choice(varied) for _ in range(rng.randrange(8))]))
        self.check_cases(cases)
        print(f'Set producer audit: {len(cases)} supplied event/snapshot cases', flush=True)

    def test_empty_long_duplicate_alias_and_type_erasure(self):
        cases = [dict(names=[], later=[]), dict(names=[units('a')] * 65, later=[units('b')]),
                 dict(names=[units(str(index)) for index in range(96)], later=[units('0'), units('96')]),
                 dict(names=[units('id'), units('id'), units('constructor'), units('__proto__')])]
        self.check_cases(cases)
        source = (ROOT / 'verification/key-set/create.ts.txt').read_text()
        self.check_cases(cases, createSource=source.replace('new Set<string>()', 'new Factory<string>()'))
        self.check_cases(cases, createSource=source.replace('new Set<string>()', 'new Set()'))

    def test_real_parsed_source_faults(self):
        add = (ROOT / 'verification/key-set/add.ts.txt').read_text()
        spread = (ROOT / 'verification/key-set/spread.ts.txt').read_text()
        case = dict(names=[units('a'), units('b'), units('a')], later=[units('c')])
        variants = [dict(addSource=add.replace('pattern[1]', "'forced'")),
                    dict(addSource=add.replace('possibleKeys.add(pattern[1])', "possibleKeys.add(pattern[1]).add('forced')")),
                    dict(spreadSource=spread.replace('[...possibleKeys]', '[...possibleKeys, ...possibleKeys]')),
                    dict(spreadSource='[]')]
        for variant in variants:
            packet = dict(cases=[case], **variant)
            observed = native_packet(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [expected(case)])

    def test_native_scope_boundaries(self):
        scope = native_packet(dict(cases=[], scopeProbes=True))['scope']
        self.assertEqual(scope, dict(liveFirst='a', liveRemaining=['b', 'c', None], exhaustedStaysDone=True,
                                     overriddenIterator=[units('a'), units('a'), units('b')], boxedDistinct=True, coercions=0))

    def test_source_identity_and_freshness(self):
        with tempfile.TemporaryDirectory(prefix='hono-set-source-') as temporary:
            base = Path(temporary)
            script = base / 'verification/key-set/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/key-set/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/key-set/create.ts.txt', 'verification/key-set/add.ts.txt',
                             'verification/key-set/spread.ts.txt', 'verification/key-set/source.json',
                             'HonoLean/Upstream/NodeKeySet/Generated.lean']:
                file = base / relative
                original = file.read_bytes()
                file.write_bytes(original + b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative)
                file.write_bytes(original)
            clone = base / 'checkout'
            subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            command = ['python3', str(script), '--hono', str(clone)]
            self.assertEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True)
            file = clone / 'src/router/trie-router/node.ts'
            file.write_bytes(file.read_bytes() + b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(command).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['key-set-tests'])
