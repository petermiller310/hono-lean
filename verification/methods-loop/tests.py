#!/usr/bin/env python3
"""Finite evidence for the exact methods-array loop, guard, and nested capture."""
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
    data = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(data[i:i+2], 'little') for i in range(0, len(data), 2)]


def invoke(command, packet=None):
    return subprocess.run(command, input=None if packet is None else json.dumps(packet), cwd=ROOT,
                          env=ENV, text=True, capture_output=True, timeout=120)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/methods-loop/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/methods-loop/native.ts', str(HONO)], packet)
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


def oracle(case):
    query = tuple(case['method'])
    record_params = [-1]*len(case['records'])
    collector = [-1]*case.get('priorCount', 0)
    allocations = []
    parameters = dict((tuple(k), v) for k, v in case.get('parameterEntries', []))
    if case.get('parameterMode') in ['null', 'undefined']:
        parameters = {}
    nodes = dict((tuple(k), v) for k, v in case.get('nodeEntries', []))
    for row in case['rows']:
        own = dict((tuple(k), v) for k, v in row.get('own', []))
        inherited = {} if row.get('nullPrototype') else dict((tuple(k), v) for k, v in row.get('inherited', []))

        def read(key):
            return own.get(key, inherited.get(key, 'u'))
        selected = read(query)
        if selected in FALSY:
            selected = read(tuple(units('ALL')))
        if selected in FALSY:
            continue
        index = int(selected[1:])
        collector.append(index)
        record_params[index] = len(allocations)
        captures = []
        for position, key in enumerate(case['records'][index]):
            parameter, node = parameters.get(tuple(key), 'u'), nodes.get(tuple(key), 'u')
            value = parameter if position == 0 and parameter not in FALSY else parameter if node in ['u', 'n'] else node
            captures.append(dict(key=key, value=encoded(value), writable=True, enumerable=True, configurable=True))
        allocations.append(sorted(captures, key=lambda entry: entry['key']))
    return dict(collector=collector, recordParams=record_params,
                collectorParams=[record_params[index] if index >= 0 else -1 for index in collector],
                allocations=allocations, nullPrototypes=True, methodsKept=True, keysKept=True,
                handlerFieldsKept=True, scope=['outer-i', 'outer-len', 'outer-m', 'outer-handler', 'outer-key'])


def row(*fields, inherited=(), null=False):
    return dict(own=[[units(key), value] for key, value in fields],
                inherited=[[units(key), value] for key, value in inherited], nullPrototype=null)


def fixture(rows, method='GET'):
    return dict(method=units(method), rows=rows, records=[[units('id'), units('name')], [units('name')]],
                nodeEntries=[[units('id'), 'text'], [units('name'), 'one']],
                parameterEntries=[[units('id'), 'one'], [units('name'), 'text']], priorCount=1)


class MethodsLoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/methods-loop/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)

    def compare(self, cases):
        expected = [oracle(case) for case in cases]
        self.assertEqual(native(dict(cases=cases))['results'], expected)
        self.assertEqual(model(dict(cases=cases)), expected)

    def test_ordered_mixed_rows_and_repeated_references(self):
        choices = [row(('GET', 'r0')), row(('GET', 'f'), ('ALL', 'r1')), row(),
                   row(('ALL', 'r1')), row(inherited=[('GET', 'r1')]), row(('GET', 'r1'), ('ALL', 'r0'))]
        cases = [fixture(list(sequence)) for length in range(5) for sequence in itertools.product(choices, repeat=length)]
        for index, case in enumerate(cases):
            case['priorCount'] = index % 3
        self.compare(cases)
        print(f'Methods-loop ordered audit: {len(cases)} mixed hit/miss/ALL/repeated-reference contexts', flush=True)

    def test_generated_captures_and_nested_scopes(self):
        rng = random.Random(1729)
        alphabet = [units(text) for text in ['', 'id', 'name', '__proto__', 'constructor', '0', 'é', '\ud800']]
        codes = ['u', 'n', 'f', 'z', 'empty', 'r0', 'r1', 'r2']
        cases = []
        for _ in range(384):
            query = rng.choice(['GET', 'POST', 'ALL', '', '__proto__'])
            records = [rng.sample(alphabet, rng.randrange(len(alphabet)+1)) for _ in range(3)]
            rows = [row((query, rng.choice(codes)), ('ALL', rng.choice(codes)),
                        inherited=[(query, rng.choice(codes)), ('ALL', rng.choice(codes))], null=bool(rng.randrange(2)))
                    for _ in range(rng.randrange(13))]
            cases.append(dict(method=units(query), rows=rows, records=records,
                              nodeEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterEntries=[[key, rng.choice(['u', 'n', 'f', 'z', 'empty', 'text', 'one'])] for key in alphabet],
                              parameterMode=rng.choice(['object', 'null', 'undefined']), priorCount=rng.randrange(4)))
        long = fixture([row(('GET', 'r0')), row(), row(('ALL', 'r1')), row(('GET', 'r0'))])
        long['records'][0] = [units(str(i)) for i in range(96)]
        cases += [long, fixture([row()]*96), fixture([row(('GET', 'r0'))]*65)]
        self.compare(cases)
        print(f'Methods-loop capture audit: {len(cases)} seeded/long contexts; inner indices restart', flush=True)

    def test_supported_source_faults_and_type_erasure(self):
        source = (ROOT/'verification/methods-loop/loop.ts.txt').read_text()
        case = fixture([row(('GET', 'r0')), row(('GET', 'z'), ('ALL', 'r1')), row(('GET', 'r1'))])
        variants = [source.replace('let i = 0, len = node.#methods.length', 'let i = 1, len = node.#methods.length'),
                    source.replace('len = node.#methods.length', 'len = 0'),
                    source.replace('node.#methods[i]', 'node.#methods[0]'), source.replace('||', '??'),
                    source.replace('let i = 0, len = handlerSet.possibleKeys.length', 'let i = 1, len = handlerSet.possibleKeys.length'),
                    source.replace('params?.[key] && !i', 'params?.[key] && i')]
        for variant in variants:
            observed = native(dict(cases=[case], source=variant))['results']
            self.assertEqual(model(dict(cases=[case], source=variant)), observed)
            self.assertNotEqual(observed, [oracle(case)])
        variant = source.replace('HandlerParamsSet<T>', 'OtherShape<U>')
        self.assertEqual(native(dict(cases=[case], source=variant))['results'], [oracle(case)])
        self.assertEqual(model(dict(cases=[case], source=variant)), [oracle(case)])

    def test_native_saved_length_live_rows_and_invalid_truthy(self):
        self.assertEqual(native(dict(scopeProbes=True))['scopeProbes'], dict(
            appended=dict(count=1, rows=2, error=False), replaced=dict(count=1, rows=2, error=False),
            shrunk=dict(count=1, rows=0, error=True), truthyInvalid=dict(count=0, rows=1, error=True),
            aliasedCollector=dict(length=2, appendedHandler=True),
            actualNode=dict(GET=[['get', '42'], ['all', '42'], ['second', '42']],
                            POST=[['all', '42'], ['post', '42']], HEAD=[['all', '42']], DELETE=[['all', '42']])))

    def test_source_artifacts_and_hidden_checkout_edits(self):
        with tempfile.TemporaryDirectory(prefix='hono-methods-loop-') as temporary:
            base = Path(temporary); script = base/'verification/methods-loop/source.py'
            script.parent.mkdir(parents=True); shutil.copy(ROOT/'verification/methods-loop/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            generated = base/'HonoLean/Upstream/MethodsLoop/Generated.lean'
            generated.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT/'HonoLean/Upstream/MethodsLoop/Generated.lean', generated)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/methods-loop/loop.ts.txt', 'verification/methods-loop/source.json', 'HonoLean/Upstream/MethodsLoop/Generated.lean']:
                file = base/relative; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative); file.write_bytes(original)
            clone = base/'checkout'; subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            source = 'src/router/trie-router/node.ts'
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
            file = clone/source; file.write_bytes(file.read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
            self.assertNotEqual(invoke(['python3', str(script), '--hono', str(clone)]).returncode, 0)
            self.assertNotEqual(invoke(['bun', 'verification/methods-loop/native.ts', str(clone)], dict(cases=[])).returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['methods-loop-tests'])
