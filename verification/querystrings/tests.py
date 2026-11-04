#!/usr/bin/env python3
"""Pinned raw-text query evidence, independent oracle and source/semantic faults."""
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
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0')
PIN = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
args = parser.parse_args()
HONO = args.hono.resolve()


def invoke(command, document=None):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def units(text):
    data = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(data[index:index+2], 'little') for index in range(0, len(data), 2)]


def oracle(input):
    query = fragment = None
    for position in range(8, len(input)):
        if input[position] == 63 and query is None:
            query = position
        if input[position] == 35 and fragment is None:
            fragment = position
    if query is None or (fragment is not None and fragment < query):
        return []
    return input[query:fragment]


def model(inputs, source=None):
    document = dict(inputs=inputs)
    if source is not None:
        document['source'] = source
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/querystrings/Driver.lean'], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)['results']


class QueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/querystrings/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def compare(self, cases):
        result = invoke(['bun', 'verification/querystrings/hono_runner.ts',
                         str(HONO / 'src/utils/url.ts')], dict(inputs=cases))
        self.assertEqual(result.returncode, 0, result.stderr)
        observed = json.loads(result.stdout)
        self.assertEqual(observed['runtime'], '1.4.0')
        expected = [oracle(case) for case in cases]
        self.assertEqual(observed['results'], expected)
        self.assertEqual(model(cases), expected)

    def test_upstream_six_examples_and_raw_boundaries(self):
        fixtures = [
            ('https://example.com/hello?name=foo&name=bar&age=20', '?name=foo&name=bar&age=20'),
            ('https://example.com/hello?', '?'), ('https://example.com/hello', ''),
            ('https://example.com/hello?name=foo&name=bar&age=20#hash', '?name=foo&name=bar&age=20'),
            ('https://example.com/hello#?name=probe', ''),
            ('https://example.com/hello?name=foo%23bar#hash', '?name=foo%23bar'),
            ('1234567#?x', '?x'), ('12345678#f?q', ''), ('12345678?x#f', '?x'),
            ('1234567?x', ''), ('12345678?', '?'), ('𝄞𝄞𝄞𝄞?x', '?x'),
            ('12345678?\ud800#\udc00', '?\ud800'), ('12345678?x%23y#z', '?x%23y')]
        cases = [units(input) for input, _ in fixtures]
        self.assertEqual([oracle(case) for case in cases], [units(output) for _, output in fixtures])
        self.compare(cases)

    def test_generated_utf16_and_offset_eight(self):
        cases = [[97] * prefix + list(suffix) for prefix in range(11) for n in range(4)
                 for suffix in itertools.product([63, 35, 97], repeat=n)]
        cases += [[97] * 8 + list(suffix) for n in range(6)
                  for suffix in itertools.product([63, 35, 97, 55296, 56320], repeat=n)]
        rng = random.Random(1729)
        alphabet = [0, 35, 63, 97, 37, 47, 0xD800, 0xDC00, 0xD834, 0xDD1E, 65535, 0xFF03, 0xFF1F]
        cases += [[rng.choice(alphabet) for _ in range(rng.randrange(101))] for _ in range(512)]
        self.compare(cases)
        print(f'Query source audit: {len(cases)} generated UTF-16 inputs', flush=True)

    def test_source_body_faults_change_observable_results(self):
        source = (ROOT / 'verification/querystrings/getQueryStrings.ts.txt').read_text()
        variants = [
            (source.replace("url.indexOf('?', 8)", "url.indexOf('?', 0)"), '?12345678'),
            (source.replace('queryIndex < hashIndex', 'hashIndex < queryIndex'), '12345678?x#f'),
            (source.replace("url.indexOf('#', 8)", "url.indexOf('#', queryIndex)"), '12345678#x?q')]
        for changed, witness in variants:
            self.assertNotEqual(changed, source)
            self.assertNotEqual(model([units(witness)], changed), [oracle(units(witness))])

    def test_signed_search_and_slice_primitives(self):
        strings = [[], [63], [35, 63, 35], [0xD834, 0xDD1E, 63, 0xDC00, 35],
                   [97] * 8 + [63, 0, 35]]
        positions = [-9007199254740991, -10, -2, -1, 0, 1, 2, 8, 10, 9007199254740991]
        stops = [None, -10, -1, 0, 2, 8, 10]
        cases = [dict(units=text, separator=separator, position=position, start=position, stop=stop)
                 for text in strings for separator in [63, 35, 0xDC00]
                 for position in positions for stop in stops]
        expected = []
        for case in cases:
            text = case['units']
            clamp = lambda value: min(len(text), value) if value >= 0 else max(0, len(text) + value)
            cursor = max(0, min(len(text), case['position']))
            index = next((i for i in range(cursor, len(text)) if text[i] == case['separator']), -1)
            start = clamp(case['start'])
            stop = len(text) if case['stop'] is None else clamp(case['stop'])
            expected.append(dict(index=index, slice=text[start:stop]))
        native = invoke(['bun', 'verification/querystrings/hono_runner.ts',
                         str(HONO / 'src/utils/url.ts')], dict(primitives=cases))
        self.assertEqual(native.returncode, 0, native.stderr)
        self.assertEqual(json.loads(native.stdout)['primitives'], expected)
        actual = invoke(['lake', 'env', 'lean', '--run', 'verification/querystrings/Primitives.lean'], cases)
        self.assertEqual(actual.returncode, 0, actual.stderr + actual.stdout)
        self.assertEqual(json.loads(actual.stdout), expected)
        print(f'Query primitive audit: {len(cases)} signed search/slice cases', flush=True)

    def test_identity_artifacts_and_hidden_checkout_faults(self):
        with tempfile.TemporaryDirectory(prefix='hono-query-source-') as temporary:
            base = Path(temporary)
            script = base / 'verification/querystrings/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/querystrings/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/querystrings/source.json',
                             'verification/querystrings/getQueryStrings.ts.txt',
                             'HonoLean/Upstream/GetQueryStrings/Generated.lean']:
                artifact = base / relative
                original = artifact.read_bytes()
                artifact.write_bytes(original + b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative)
                artifact.write_bytes(original)
            clone = base / 'checkout'
            subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            command = ['python3', str(script), '--hono', str(clone)]
            self.assertEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', 'HEAD^'], check=True)
            self.assertNotEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', PIN], check=True)
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/utils/url.ts'], check=True)
            artifact = clone / 'src/utils/url.ts'
            artifact.write_bytes(artifact.read_bytes() + b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(command).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['querystrings-tests'])
