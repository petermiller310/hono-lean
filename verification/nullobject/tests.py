#!/usr/bin/env python3
"""Pinned helper allocation and local descriptor/transfer mechanism evidence."""
import argparse
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


def invoke(command, document=None):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def model(document):
    return invoke(['lake', 'env', 'lean', '--run', 'verification/nullobject/Driver.lean'], document)


class ObjectTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/nullobject/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def test_helper_freshness_transfer_and_actual_d1(self):
        names = ['__proto__', 'id', 'constructor', 'toString', 'hasOwnProperty', '',
                 '__proto__\0', '__defineGetter__', 'prototype', '\ud800', 'é', '0', 'length']
        values = [[], units('alpha'), units('constructor'), [0], [0xD800], [0xDC00],
                  [0xD834, 0xDD1E, 0, 47], [95, 95]]
        transfers = [dict(key=units(name), contents=value) for name in names for value in values]
        rng = random.Random(1729)
        alphabet = [0, 95, 97, 233, 0xD800, 0xDC00, 65535]
        transfers += [dict(key=[rng.choice(alphabet) for _ in range(rng.randrange(12))],
                           contents=[rng.choice(alphabet) for _ in range(rng.randrange(16))]) for _ in range(64)]
        document = dict(allocations=[0, 1, 2, 3, 8, 32], transfers=transfers)
        native = invoke(['bun', 'verification/nullobject/native.ts', str(HONO)], document)
        self.assertEqual(native.returncode, 0, native.stderr)
        observed = json.loads(native.stdout)
        actual = model(document)
        self.assertEqual(actual.returncode, 0, actual.stderr + actual.stdout)
        self.assertEqual(json.loads(actual.stdout), {key: observed[key] for key in ['allocations', 'transfers']})
        self.assertEqual(observed['runtime'], '1.4.0')
        self.assertEqual(observed['realm'], dict(legacyAccessor=True, prototypeHasOtherProperties=True,
                                               prototypeEnumerableKeys=[], prototypeJSON='{}'))
        for record, input in zip(observed['transfers'], transfers):
            special = input['key'] == units('__proto__')
            expected = {'object': 0} if special else {'string': input['contents']}
            self.assertEqual(record['temporaryHasOwn'], not special)
            self.assertEqual(record['readValue'], expected)
            self.assertTrue(record['outputHasOwn'])
            self.assertEqual(record['outputValue'], expected)
            self.assertIsNone(record['outputPrototype'])
            self.assertEqual(record['descriptor'], dict(kind='data', value=expected,
                                writable=True, enumerable=True, configurable=True))
        self.assertEqual(observed['raw'], [
            dict(name=name, handler='capture', own=True, value={'object': 0} if name == '__proto__' else {'string': units('alpha')},
                 prototype=None) for name in ['__proto__', 'id', 'constructor']])
        print(f'Object audit: 6 allocation frames, {len(transfers)} local transfers, exact raw D1 and two controls', flush=True)

    def test_generic_source_and_semantic_faults(self):
        document = dict(allocations=[0], transfers=[])
        valid = 'export const renamed = () => null === null ? Object.create(null) : Object.create(0)'
        self.assertEqual(model(dict(document, source=valid)).returncode, 0)
        for changed in ['export const createNullObject = () => null',
                        'export const createNullObject = () => Object']:
            result = model(dict(document, source=changed))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Wrong return', result.stderr + result.stdout)
        rejected = 'export const Object = () => Object.create(null)'
        result = model(dict(document, source=rejected))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Source parse rejected', result.stderr + result.stdout)

    def test_entire_source_identity_and_hidden_edit(self):
        with tempfile.TemporaryDirectory(prefix='hono-null-object-') as temporary:
            base = Path(temporary)
            script = base / 'verification/nullobject/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/nullobject/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/nullobject/createNullObject.ts.txt',
                             'verification/nullobject/source.json',
                             'HonoLean/Upstream/CreateNullObject/Generated.lean']:
                file = base / relative
                original = file.read_bytes()
                file.write_bytes(original + b'\n')
                self.assertNotEqual(invoke(command).returncode, 0)
                file.write_bytes(original)
            clone = base / 'checkout'
            subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            command = ['python3', str(script), '--hono', str(clone)]
            self.assertEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', 'HEAD^'], check=True)
            self.assertNotEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True)
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/utils.ts'], check=True)
            file = clone / 'src/router/utils.ts'
            file.write_bytes(file.read_bytes() + b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(command).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['null-object-tests'])
