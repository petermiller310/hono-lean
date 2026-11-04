#!/usr/bin/env python3
"""Evidence for actual private push under explicit class/entry conditions."""
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
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def invoke(command, packet=None):
    return subprocess.run(command, input=None if packet is None else json.dumps(packet),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/methods-push/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/methods-push/native.ts', str(HONO)], packet)
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
    count = case['priorCount']
    return dict(firstReturn=count+1, secondReturn=count+2, methodCount=count+2, prefixKept=True,
                first=record(first_occurrences(case['names']), case['order']+1),
                second=record(first_occurrences(case['names']+case['later']), case['order']+2),
                firstUnchanged=True, distinctStoredMaps=True, privateSlotsKept=True, publicShadowKept=True,
                orderAfter=case['order']+2, setKept=True, frameKept=True)


def scope_result(error='', order=0, length=0, returned=None, ownZero=False, privateArrayChanged=False, **extra):
    return dict(error=error, order=order, length=length, returned=returned, ownZero=ownZero,
                privateArrayChanged=privateArrayChanged, **extra)


class MethodsPushTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/methods-push/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def check_cases(self, cases):
        packet = dict(cases=cases)
        oracle = [expected(case) for case in cases]
        self.assertEqual(native(packet)['results'], oracle)
        self.assertEqual(model(packet), oracle)

    def test_supplied_contexts_utf16_aliases_and_prefixes(self):
        alphabet = [units(text) for text in ['', 'id', '__proto__', '\ud800']]
        methods = [units(text) for text in ['GET', 'ALL', '__proto__', 'constructor', 'toString', '', '0', '\0', '\ud800', 'é']]
        handlers = ['object', 'array', 'set', 'function', 'undefined', 'null', 'boolean', 'number', 'string', 'methods-array', 'owner']
        orders = [-9007199254740991, -3, 0, 42, 9007199254740989]
        priors = [0, 1, 3, 33]
        cases = [dict(method=methods[index % len(methods)], names=list(sequence), later=[units('next'), units('id')],
                      order=orders[index % len(orders)], handler=handlers[index % len(handlers)], priorCount=priors[index % len(priors)])
                 for index, sequence in enumerate(sequence for length in range(5)
                     for sequence in itertools.product(alphabet, repeat=length))]
        varied = [units(text) for text in ['', 'id', 'constructor', '__proto__', 'é', 'e\u0301', '\ud800', '\udc00', '\ud834\udd1e']]
        rng = random.Random(1729)
        for _ in range(256):
            cases.append(dict(method=rng.choice(methods), names=[rng.choice(varied) for _ in range(rng.randrange(20))],
                              later=[rng.choice(varied) for _ in range(rng.randrange(8))],
                              order=rng.choice(orders), handler=rng.choice(handlers), priorCount=rng.choice(priors)))
        self.check_cases(cases)
        print(f'Private methods push audit: {len(cases)} two-call contexts', flush=True)

    def test_long_empty_and_feedback_aliases(self):
        cases = [dict(method=units('__proto__'), names=[units(str(i)) for i in range(96)], later=[], order=0, handler='owner', priorCount=96),
                 dict(method=units('constructor'), names=[units('id')]*65, later=[units('id')], order=0, handler='methods-array', priorCount=1)]
        for method, handler in itertools.product(['__proto__', 'constructor', 'GET', '\ud800'],
                ['object', 'array', 'set', 'function', 'undefined', 'null', 'boolean', 'number', 'string', 'methods-array', 'owner']):
            cases.append(dict(method=units(method), names=[], later=[], order=0, handler=handler, priorCount=0))
        self.check_cases(cases)

    def test_real_parsed_source_faults(self):
        source = (ROOT/'verification/methods-push/source.ts.txt').read_text()
        case = dict(method=units('GET'), names=[units('id'), units('name')], later=[units('next')], order=7, handler='object', priorCount=3)
        variants = [source.replace('curNode.#methods', "curNode['#methods']"),
                    source.replace('#methods', '#patterns'), source.replace('[...possibleKeys]', '[]'),
                    source.replace('++order', 'order'), source.rstrip()[:-1]+', null)\n',
                    'curNode.#methods.push(null)\n']
        for variant in variants:
            self.assertNotEqual(variant, source)
            packet = dict(cases=[case], source=variant)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [expected(case)])

    def test_native_private_and_call_boundaries(self):
        self.assertEqual(native(dict(cases=[], scopeProbes=True))['scope'], dict(
            brand=[scope_result(error='TypeError')]*5,
            nullSlot=scope_result(error='TypeError', privateArrayChanged=True),
            noncallable=scope_result(error='TypeError', order=1),
            throwingLookup=scope_result(error='lookup'), throwingPush=scope_result(error='push', order=1),
            frozen=scope_result(error='TypeError', order=1),
            capturedReceiver=scope_result(order=1, length=1, returned=1, ownZero=True, privateArrayChanged=True),
            iteratorRebind=scope_result(order=1, length=1, returned=1, ownZero=True, privateArrayChanged=True),
            argumentMutation=scope_result(order=1, length=2, returned=2, ownZero=True, firstIsSentinel=True, tailScore=1),
            captureEvents=['lookup', 'iterate'],
            inheritedIndex=scope_result(order=1, length=1, returned=1, capturedRecordScore=1),
            inheritedSetterCalls=1, outOfScopeSyntax='SyntaxError', actualNode=dict(matches=1, handlerKept=True, id='alpha')))

    def test_source_freshness_and_hidden_checkout_edit(self):
        with tempfile.TemporaryDirectory(prefix='hono-methods-source-') as temporary:
            base = Path(temporary)
            script = base/'verification/methods-push/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT/'verification/methods-push/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            for relative in ['verification/methods-push/source.ts.txt', 'verification/methods-push/source.json',
                             'HonoLean/Upstream/NodeMethodsPush/Generated.lean']:
                file = base/relative
                original = file.read_bytes()
                file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative)
                file.write_bytes(original)
            clone = base/'checkout'
            subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            command = ['python3', str(script), '--hono', str(clone)]
            self.assertEqual(invoke(command).returncode, 0)
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True)
            file = clone/'src/router/trie-router/node.ts'
            file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(command).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['methods-push-tests'])
