#!/usr/bin/env python3
"""Native evidence for the normalized primitive-step models; not an adequacy proof."""
import argparse
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[2]
DEFAULT = 4294967295
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
args = parser.parse_args()


def invoke(command, document=None):
    result = subprocess.run(command, input=None if document is None else json.dumps(document),
                            cwd=ROOT, env=ENV, text=True, capture_output=True)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return result.stdout


def oracle_split(units, separator, limit):
    fields = [[]]
    for unit in units:
        if unit == separator:
            fields.append([])
        else:
            fields[-1].append(unit)
    return fields[:limit]


def oracle_path(units, limit):
    fields = oracle_split(units, 47, limit)
    return fields[1:] if fields and not fields[0] else fields


def tagged(value):
    return {'undefined': True} if value is None else {'string': value}


def oracle_array(elements):
    size = len(elements)
    indices = [0, 1, size, size + 1]
    values = [elements[index] if index < size else None for index in indices]
    return dict(first=tagged(elements[0] if elements else None), after=elements[1:],
                indices=indices, get=[tagged(value) for value in values],
                equalsEmpty=[value == [] for value in values], length=max(0, size - 1),
                oldLastIsOwn=False)


def model(document):
    return json.loads(invoke(['lake', 'env', 'lean', '--run',
                              'verification/ecma2025/Driver.lean'], document))


def native(document):
    return json.loads(invoke(['bun', 'verification/ecma2025/native.ts'], document))


class PrimitiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Bind every upstream import to exact clean working-file bytes first.
        invoke(['python3', 'verification/splitpath/source.py', '--hono', str(args.hono.resolve())])

    def test_default_path_steps_against_actual_pinned_function(self):
        cases = [list(xs) for n in range(6)
                 for xs in itertools.product([47, 97, 0, 55296, 56320], repeat=n)]
        rng = random.Random(1729)
        alphabet = [0, 47, 97, 233, 0xD800, 0xDC00, 0xD834, 0xDD1E, 0xFF0F, 65535]
        cases += [[rng.choice(alphabet) for _ in range(rng.randrange(65))] for _ in range(256)]
        cases += [[0xD834, 0xDD1E, 47, 0xDC00], [0xDC00, 47, 0xD800], [47] * 1024]
        document = dict(inputs=cases, separator=47, limit=DEFAULT, arrays=[])
        expected = [oracle_path(case, DEFAULT) for case in cases]
        actual = json.loads(invoke(['bun', 'verification/splitpath/hono_runner.ts',
                                   str(args.hono.resolve() / 'src/utils/url.ts')], document))
        self.assertEqual(actual['runtime'], '1.4.0')
        self.assertEqual(actual['results'], expected)
        self.assertEqual(model(document)['paths'], expected)
        print(f'ECMA-step default path audit: {len(cases)} pinned-source/model/oracle cases', flush=True)

    def test_generic_code_unit_separator_and_limit_order(self):
        cases = [list(xs) for n in range(4) for xs in itertools.product([47, 97, 0xD800], repeat=n)]
        cases += [[], [0], [65535], [0xD800, 0xDC00, 47, 0xD800], [47, 97, 47, 98, 47]]
        for separator in [47, 0, 0xD800, 65535]:
            for limit in [0, 1, 2, 3, 4, 7]:
                document = dict(inputs=cases, separator=separator, limit=limit, arrays=[])
                expected = dict(split=[oracle_split(case, separator, limit) for case in cases],
                                paths=[oracle_path(case, limit) for case in cases], arrays=[])
                with self.subTest(separator=separator, limit=limit):
                    self.assertEqual(native(document), expected)
                    self.assertEqual(model(document), expected)
        print(f'ECMA-step generic split audit: {len(cases) * 24} input/separator/limit cases', flush=True)

    def test_dense_copy_delete_get_equality_and_native_alias(self):
        fields = [[], [97], [0xD800], [0xDC00], [0, 47]]
        arrays = [list(xs) for n in range(5) for xs in itertools.product(fields, repeat=n)]
        rng = random.Random(42)
        arrays += [[rng.choice(fields) for _ in range(rng.randrange(16))] for _ in range(128)]
        document = dict(inputs=[], separator=47, limit=DEFAULT, arrays=arrays)
        expected = dict(split=[], paths=[], arrays=[oracle_array(array) for array in arrays])
        self.assertEqual(native(document), expected)
        self.assertEqual(model(document), expected)
        print(f'ECMA-step dense-array audit: {len(arrays)} cases', flush=True)


if __name__ == '__main__':
    unittest.main(argv=['ecma2025-tests'])
