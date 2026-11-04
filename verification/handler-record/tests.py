#!/usr/bin/env python3
"""Finite evidence for the exact Node.insert object argument, not its call."""
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


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i + 2], 'little') for i in range(0, len(raw), 2)]


def invoke(command, packet=None):
    return subprocess.run(command, input=None if packet is None else json.dumps(packet),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/handler-record/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/handler-record/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    result = json.loads(result.stdout)
    assert result['runtime'] == '1.4.0'
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['checkedPinnedBlobs'] == 315
    return result


def first_occurrences(events):
    return [key for index, key in enumerate(events) if key not in events[:index]]


def record(keys, score):
    return dict(outerOwnCount=1, outerHasMethod=True, outerPrototypeStandard=True, outerExtensible=True,
                innerOwnCount=3, innerPrototypeStandard=True, innerExtensible=True, handlerKept=True,
                paramsAbsent=True, freshObjects=True, freshKeys=True, keys=keys, score=score)


def expected(case):
    return dict(first=record(first_occurrences(case['names']), case['order'] + 1),
                second=record(first_occurrences(case['names'] + case['later']), case['order'] + 2),
                firstUnchanged=True, orderAfter=case['order'] + 2, distinctOuter=True,
                otherBindingsKept=True, setKept=True, frameKept=True)


class HandlerRecordTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/handler-record/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def check_cases(self, cases):
        packet = dict(cases=cases)
        oracle = [expected(case) for case in cases]
        self.assertEqual(native(packet)['results'], oracle)
        self.assertEqual(model(packet), oracle)

    def test_utf16_identity_descriptors_and_threaded_order(self):
        alphabet = [units(text) for text in ['', 'id', '__proto__', '\ud800']]
        methods = [units(text) for text in ['GET', 'ALL', '__proto__', 'constructor', 'toString', '', '0', '\0', '\ud800', 'é']]
        handlers = ['object', 'array', 'set', 'function', 'undefined', 'null', 'boolean', 'number', 'string']
        orders = [-9007199254740991, -3, 0, 42, 9007199254740989]
        cases = [dict(method=methods[index % len(methods)], names=list(sequence), later=[units('next'), units('id')],
                      order=orders[index % len(orders)], handler=handlers[index % len(handlers)])
                 for index, sequence in enumerate(sequence for length in range(5)
                     for sequence in itertools.product(alphabet, repeat=length))]
        varied = [units(text) for text in ['', 'id', 'constructor', '__proto__', 'é', 'e\u0301', '\ud800', '\udc00', '\ud834\udd1e']]
        rng = random.Random(1729)
        for _ in range(256):
            cases.append(dict(method=rng.choice(methods), names=[rng.choice(varied) for _ in range(rng.randrange(20))],
                              later=[rng.choice(varied) for _ in range(rng.randrange(8))],
                              order=rng.choice(orders), handler=rng.choice(handlers)))
        self.check_cases(cases)
        print(f'Handler record audit: {len(cases)} two-evaluation contexts', flush=True)

    def test_long_empty_and_every_handler_kind(self):
        cases = [dict(method=units('__proto__'), names=[units(str(i)) for i in range(96)], later=[], order=0, handler='object'),
                 dict(method=units('constructor'), names=[units('id')] * 65, later=[units('id')], order=0, handler='undefined')]
        for method, handler in itertools.product(['__proto__', 'constructor', 'GET', '\ud800'],
                ['object', 'array', 'set', 'function', 'undefined', 'null', 'boolean', 'number', 'string']):
            cases.append(dict(method=units(method), names=[], later=[], order=0, handler=handler))
        self.check_cases(cases)

    def test_parsed_source_faults(self):
        source = (ROOT / 'verification/handler-record/source.ts.txt').read_text()
        case = dict(method=units('GET'), names=[units('id'), units('name')], later=[units('next')], order=7, handler='object')
        variants = [source.replace('[...possibleKeys]', '[]'), source.replace('handler,', 'handler: method,'),
                    source.replace('++order', 'order'), source.replace('[method]', "['fixed']"),
                    source.replace('[...possibleKeys]', '[...possibleKeys, ...possibleKeys]')]
        for variant in variants:
            self.assertNotEqual(variant, source)
            packet = dict(cases=[case], source=variant)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [expected(case)])

    def test_native_scope_boundaries(self):
        self.assertEqual(native(dict(cases=[], scopeProbes=True))['scope'],
            dict(computedKeyEffects=['iterate', 'key'], computedProtoIsOwnData=True, prototypeUnchanged=True,
                 iteratorFailureOrder=0, iteratorFailure='iterator', pushFailureOrder=1, pushFailure='push',
                 inheritedSetterCalls=0, fullCallEffects=['lookup', 'iterate', 'key', 'push'], fullCallOrder=1,
                 precisionScores=[9007199254740992, 9007199254740992], paramsSetterCalls=1,
                 consumerError='TypeError', ownParamsAfterReset=False, appendedHandlers=1))

    def test_preserved_engine_coercion_order_difference(self):
        # This is deliberately not a model-acceptance or comparator exception.
        # The model accepts primitive-string keys; these key-coercion callbacks
        # are outside it. Preserve observations rather than changing the model
        # to match one engine against the standard.
        for engine, expected_effects in [
                ('bun', (['value', 'key'], ['iterate', 'key'], ['lookup', 'iterate', 'key', 'push'])),
                (os.environ.get('HONO_NODE', 'node'), (['key', 'value'], ['key', 'iterate'], ['lookup', 'key', 'iterate', 'push']))]:
            result = invoke([engine, 'verification/handler-record/coercion-probe.mjs', str(HONO)])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            record = json.loads(result.stdout)
            self.assertEqual(record['checkedPinnedBlobs'], 315)
            self.assertEqual((record['minimal'], record['objectArgument'], record['call']), expected_effects)

    def test_source_freshness_and_hidden_checkout_edit(self):
        with tempfile.TemporaryDirectory(prefix='hono-record-source-') as temporary:
            base = Path(temporary)
            script = base / 'verification/handler-record/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/handler-record/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            for relative in ['verification/handler-record/source.ts.txt', 'verification/handler-record/source.json',
                             'HonoLean/Upstream/HandlerRecord/Generated.lean']:
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
    unittest.main(argv=['handler-record-tests'])
