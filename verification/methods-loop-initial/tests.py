#!/usr/bin/env python3
"""Finite source composition evidence; universal theorem scopes are recorded separately."""
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


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=120)


def units(text):
    data = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(data[i:i+2], 'little') for i in range(0, len(data), 2)]


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/methods-loop-initial/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/methods-loop-initial/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    result = json.loads(result.stdout)
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['transpilation']['verified'] is False
    assert len(result['transpilation']['inputSha256']) == len(result['transpilation']['emittedSha256']) == 64
    return result


FALSY = {'u', 'n', 'f', 'z', 'empty'}


def encoded(code):
    if code in ['u', 'n']:
        return dict(kind='undefined' if code == 'u' else 'null')
    if code in ['f', 't']:
        return dict(kind='bool', value=code == 't')
    if code in ['z', 'one']:
        return dict(kind='number', value=0 if code == 'z' else 1)
    if code in ['empty', 'text']:
        return dict(kind='string', units=[] if code == 'empty' else units('x'))
    raise ValueError(code)


def unique(keys):
    return [key for index, key in enumerate(keys) if key not in keys[:index]]


def oracle(case):
    keys = [unique(row['names']) for row in case['registrations']]
    params = dict((tuple(key), value) for key, value in case.get('parameterEntries', []))
    if case.get('parameterMode') in ['null', 'undefined']:
        params = {}
    nodes = dict((tuple(key), value) for key, value in case.get('nodeEntries', []))
    record_params, collectors, allocations = [-1]*len(keys), [], []
    for query in case['queries']:
        selected = []
        for index, row in enumerate(case['registrations']):
            if row['method'] != query and row['method'] != units('ALL'):
                continue
            selected.append(index)
            record_params[index] = len(allocations)
            captures = []
            for at, key in enumerate(keys[index]):
                parameter, node = params.get(tuple(key), 'u'), nodes.get(tuple(key), 'u')
                value = parameter if at == 0 and parameter not in FALSY else parameter if node in ['u', 'n'] else node
                captures.append(dict(key=key, value=encoded(value), writable=True, enumerable=True, configurable=True))
            allocations.append(sorted(captures, key=lambda item: item['key']))
        collectors.append(selected)
    return dict(collectors=collectors, recordParams=record_params,
                collectorParams=[[record_params[index] for index in collector] for collector in collectors],
                allocations=allocations, nullPrototypes=True, keyOrder=keys,
                scores=list(range(1, len(keys)+1)), order=len(keys), collectorsFresh=True, storedShape=True)


def registration(method, *names):
    return dict(method=units(method), names=[units(name) for name in names])


def fixture(registrations, queries=('GET', 'POST')):
    return dict(registrations=registrations, queries=[units(query) for query in queries],
                nodeEntries=[[units('id'), 'text'], [units('name'), 'one']],
                parameterEntries=[[units('id'), 'one'], [units('name'), 'text']])


class InitialLoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/methods-loop-initial/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        self.assertEqual(native(dict(cases=cases))['results'], expected)
        self.assertEqual(model(dict(cases=cases)), expected)

    def test_actual_registration_histories_and_later_collectors(self):
        choices = [registration('GET'), registration('POST', 'id'), registration('ALL', 'id', 'id', 'name'),
                   registration('GET', 'name', 'id'), registration('__proto__', 'constructor')]
        cases = [fixture(list(sequence)) for length in range(5) for sequence in itertools.product(choices, repeat=length)]
        self.compare(cases)
        print(f'Initial-loop registration audit: {len(cases)} exhaustive actual-push/later-collector/full-loop histories', flush=True)

    def test_generated_utf16_keys_and_repeated_queries(self):
        rng = random.Random(1729)
        alphabet = [units(name) for name in ['', 'id', 'name', '__proto__', 'constructor', 'params', '0', 'é', '\ud800']]
        methods = [units(name) for name in ['GET', 'POST', 'ALL', '', 'constructor', 'toString', '__proto__', '\ud800']]
        queries = [units(name) for name in ['GET', 'POST', 'ALL', '', '\ud800']]
        cases = []
        for _ in range(256):
            cases.append(dict(registrations=[dict(method=rng.choice(methods), names=[rng.choice(alphabet) for _ in range(rng.randrange(14))]) for _ in range(rng.randrange(12))],
                              queries=[rng.choice(queries) for _ in range(rng.randrange(1, 5))],
                              nodeEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterMode=rng.choice(['object', 'null', 'undefined'])))
        long = fixture([registration('GET', *[str(i) for i in range(96)]), registration('ALL', 'id', 'name')], ('GET', 'GET', 'HEAD'))
        cases += [long, fixture([registration('ALL', 'id')]*65, ('GET', 'POST')), fixture([], ('HEAD', 'HEAD'))]
        self.compare(cases)
        print(f'Initial-loop capture audit: {len(cases)} generated/long histories and repeated queries', flush=True)

    def test_supported_faults_and_type_metadata_control(self):
        push = (ROOT/'verification/methods-push/source.ts.txt').read_text()
        loop = (ROOT/'verification/methods-loop/loop.ts.txt').read_text()
        case = fixture([registration('GET', 'id', 'name'), registration('ALL', 'name', 'id'), registration('POST', 'name')], ('GET',))
        faults = [dict(registrationSource=push.replace('score: ++order', 'score: order')),
                  dict(registrationSource=push.replace('[...possibleKeys]', '[]')),
                  dict(loopSource=loop.replace('let i = 0, len = node.#methods.length', 'let i = 1, len = node.#methods.length')),
                  dict(loopSource=loop.replace('node.#methods[i]', 'node.#methods[0]')),
                  dict(loopSource=loop.replace('let i = 0, len = handlerSet.possibleKeys.length', 'let i = 1, len = handlerSet.possibleKeys.length')),
                  dict(loopSource=loop.replace('params?.[key] && !i', 'params?.[key] && i')),
                  dict(loopSource=loop.replace('||', '&&'))]
        for fault in faults:
            packet = dict(cases=[case], **fault)
            observed = native(packet)['results']
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [oracle(case)])
        packet = dict(cases=[case], loopSource=loop.replace('HandlerParamsSet<T>', 'OtherShape<U>'))
        self.assertEqual(native(packet)['results'], [oracle(case)])
        self.assertEqual(model(packet), [oracle(case)])

    def test_native_inherited_lookup_and_setter_boundaries(self):
        expected = dict(error=True, appended=1)
        self.assertEqual(native(dict(scopeProbes=True))['scopeProbes'], dict(
            constructor=expected, toString=expected, proto=expected,
            inheritedSetter=dict(calls=1, error=True, appended=1)))

    def test_dependency_artifacts_and_hidden_source_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-initial-loop-') as temporary:
            base = Path(temporary)
            for name in ['methods-push', 'search-entry', 'methods-loop', 'nullobject', 'key-set', 'methods-loop-initial']:
                shutil.copytree(ROOT/f'verification/{name}', base/f'verification/{name}')
            for module in ['NodeMethodsPush', 'SearchEntry', 'MethodsLoop', 'CreateNullObject', 'NodeKeySet']:
                destination = base/f'HonoLean/Upstream/{module}/Generated.lean'; destination.parent.mkdir(parents=True)
                shutil.copy(ROOT/f'HonoLean/Upstream/{module}/Generated.lean', destination)
            command = ['python3', str(base/'verification/methods-loop-initial/source.py'), '--hono', str(HONO)]
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/methods-loop-initial/source.json', 'verification/methods-push/source.ts.txt',
                             'verification/search-entry/collector.ts.txt', 'verification/methods-loop/loop.ts.txt',
                             'HonoLean/Upstream/CreateNullObject/Generated.lean', 'HonoLean/Upstream/NodeKeySet/Generated.lean']:
                file = base/relative; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative); file.write_bytes(original)
            clone = base/'checkout'; subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            for source in ['src/router/trie-router/node.ts', 'src/router/utils.ts', 'src/router.ts']:
                subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
                file = clone/source; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
                self.assertNotEqual(invoke(['python3', str(base/'verification/methods-loop-initial/source.py'), '--hono', str(clone)]).returncode, 0)
                self.assertNotEqual(invoke(['bun', 'verification/methods-loop-initial/native.ts', str(clone)], dict(cases=[])).returncode, 0)
                file.write_bytes(original)


if __name__ == '__main__':
    unittest.main(argv=['initial-loop-tests'])
