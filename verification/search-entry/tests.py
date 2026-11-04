#!/usr/bin/env python3
"""Finite evidence for source collector/row/selection and explicit activation composition."""
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
    return subprocess.run(command, input=None if packet is None else json.dumps(packet), cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/search-entry/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    return json.loads(result.stdout)


def native(packet):
    result = invoke(['bun', 'verification/search-entry/native.ts', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout+result.stderr)
    result = json.loads(result.stdout)
    assert result['runtime'] == '1.4.0' and result['checkedPinnedBlobs'] == 315
    assert result['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert result['transpilation']['verified'] is False
    return result


FALSY = {'u', 'n', 'f', 'z', 'empty'}
VALUES = ['u', 'n', 'f', 't', 'z', 'one', 'empty', 'text', 'direct', 'all', 'row', 'prototype', 'custom', 'array', 'set', 'function', 'Object', 'Set']


def encoded(code):
    if code in ['u', 'n']:
        return dict(tag=code)
    if code in ['f', 't']:
        return dict(tag='boolean', value=code == 't')
    if code in ['z', 'one']:
        return dict(tag='number', value=0 if code == 'z' else 1)
    if code in ['empty', 'text']:
        return dict(tag='string', value=[] if code == 'empty' else units('x'))
    return dict(tag=code)


def selection_oracle(case):
    own = {tuple(key): value for key, value in case['own']}
    inherited = {tuple(key): value for key, value in case['inherited']}

    def read(key):
        key = tuple(key)
        if key in own:
            return own[key]
        if case['nullPrototype']:
            return 'u'
        if key in inherited:
            return inherited[key]
        return {tuple(units('constructor')): 'Object', tuple(units('toString')): 'function', tuple(units('__proto__')): 'custom'}.get(key, 'u')
    direct = read(case['method'])
    chosen = direct if direct not in FALSY else read(units('ALL'))
    return dict(chosen=encoded(chosen), frameKept=True)


def first_occurrences(events):
    return [key for index, key in enumerate(events) if key not in events[:index]]


def integration_oracle(case):
    keys = first_occurrences(case['names'])
    return dict(collectorFresh=True, collectorLength=1, selectedStoredRow=True, selectedStoredHandler=True,
                collectorHasSelected=True, handlerKept=True, captures=[[key, units('prior' if index == 0 else 'node')] for index, key in enumerate(keys)],
                ownCaptureCount=len(keys), nullPrototype=True, descriptors=True, nextCollectorFreshEmpty=True,
                firstCollectorKept=True, methodsCount=case['priorCount']+1, prefixKept=True, score=8, orderAfter=8, privateArrayKept=True)


class SearchEntryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/search-entry/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout+result.stderr)

    def test_selection_values_prototypes_and_lazy_missing_binding(self):
        cases = []
        methods = [units(text) for text in ['GET', 'POST', 'ALL', 'constructor', 'toString', '__proto__', '', '\ud800']]
        for method, direct, fallback, null_proto in itertools.product(methods, [None]+VALUES, [None]+VALUES, [False, True]):
            own = ([] if fallback is None else [[units('ALL'), fallback]]) + ([] if direct is None else [[method, direct]])
            cases.append(dict(method=method, own=own, inherited=[], nullPrototype=null_proto))
        rng = random.Random(1729)
        for _ in range(256):
            method = rng.choice(methods)
            cases.append(dict(method=method, own=[[method, rng.choice(VALUES)]] if rng.randrange(2) else [],
                              inherited=[[units('ALL'), rng.choice(VALUES)], [method, rng.choice(VALUES)]], nullPrototype=False))
        for code in VALUES:
            if code not in FALSY:
                cases.append(dict(method=units('GET'), own=[[units('GET'), code]], inherited=[], nullPrototype=False, omitAll=True))
        packet = dict(cases=cases)
        oracle = [selection_oracle(case) for case in cases]
        self.assertEqual(native(packet)['results'], oracle)
        self.assertEqual(model(packet)['results'], oracle)
        print(f'Search selection audit: {len(cases)} own/inherited/lazy contexts', flush=True)

    def test_later_collector_row_selection_and_capture_composition(self):
        alphabet = [units(text) for text in ['', 'id', '__proto__', '\ud800']]
        methods = [units(text) for text in ['GET', 'ALL', '__proto__', 'constructor', 'toString', '']]
        cases = [dict(method=methods[index % len(methods)], names=list(sequence), priorCount=index % 4)
                 for index, sequence in enumerate(sequence for length in range(5) for sequence in itertools.product(alphabet, repeat=length))]
        rng = random.Random(1729)
        varied = [units(text) for text in ['é', 'e\u0301', '\ud834\udd1e', '\ud800', 'constructor', 'params', '0']]
        for _ in range(64):
            cases.append(dict(method=rng.choice(methods), names=[rng.choice(varied) for _ in range(rng.randrange(20))], priorCount=rng.randrange(10)))
        cases += [dict(method=units('GET'), names=[units(str(i)) for i in range(96)], priorCount=96),
                  dict(method=units('ALL'), names=[units('id')]*65, priorCount=0)]
        packet = dict(integrations=cases)
        oracle = [integration_oracle(case) for case in cases]
        self.assertEqual(native(packet)['integrations'], oracle)
        self.assertEqual(model(packet)['integrations'], oracle)
        print(f'Search activation audit: {len(cases)} registration/later-collector/selection/capture contexts', flush=True)

    def test_supported_source_faults_and_metadata_variants(self):
        source = (ROOT/'verification/search-entry/selection.ts.txt').read_text()
        case = dict(method=units('GET'), own=[[units('GET'), 'z'], [units('ALL'), 'all']], inherited=[], nullPrototype=True)
        truthy = dict(method=units('GET'), own=[[units('GET'), 'direct'], [units('ALL'), 'all']], inherited=[], nullPrototype=True)
        for variant, selected_case in [(source.replace('||', '??'), case), (source.replace('||', '&&'), truthy),
                (source.replace('m[method] || m[METHOD_NAME_ALL]', 'm[METHOD_NAME_ALL] || m[method]'), truthy)]:
            packet = dict(cases=[selected_case], selectionSource=variant)
            observed = native(packet)['results']
            self.assertEqual(model(packet)['results'], observed)
            self.assertNotEqual(observed, [selection_oracle(selected_case)])
        integration = dict(method=units('GET'), names=[units('id')], priorCount=1)
        for variant in [dict(collectorSource=(ROOT/'verification/search-entry/collector.ts.txt').read_text().replace('[]\n', '[null]\n')),
                        dict(rowSource=(ROOT/'verification/search-entry/row.ts.txt').read_text().replace('[i]', '[0]'))]:
            packet = dict(integrations=[integration], **variant)
            observed = native(packet)['integrations']
            self.assertEqual(model(packet)['integrations'], observed)
            self.assertNotEqual(observed, [integration_oracle(integration)])
        packet = dict(cases=[case], allSource="'POST' as const")
        self.assertEqual(model(packet)['results'], native(packet)['results'])
        self.assertNotEqual(model(packet)['results'], [selection_oracle(case)])
        variant = source.replace('HandlerParamsSet<T>', 'OtherShape<U>')
        self.assertEqual(model(dict(cases=[truthy], selectionSource=variant))['results'], [selection_oracle(truthy)])
        self.assertEqual(native(dict(cases=[truthy], selectionSource=variant))['results'], [selection_oracle(truthy)])

    def test_native_getter_type_and_upstream_boundaries(self):
        self.assertEqual(native(dict(scopeProbes=True))['scope'], dict(repeatedChosen=True, repeatedReads=['ALL', 'ALL'],
            skipped=True, skippedReads=0, falsyFallbacks=[True]*5, inherited=dict(constructor=True, toString=True, proto=True),
            castDoesNotGuard=True, actualNode=dict(GET=['get', 'all'], POST=['all'], HEAD=['all'])))

    def test_source_freshness_and_hidden_edits_in_both_files(self):
        with tempfile.TemporaryDirectory(prefix='hono-search-source-') as temporary:
            base = Path(temporary); script = base/'verification/search-entry/source.py'
            script.parent.mkdir(parents=True); shutil.copy(ROOT/'verification/search-entry/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            for relative in ['verification/search-entry/collector.ts.txt', 'verification/search-entry/row.ts.txt',
                    'verification/search-entry/selection.ts.txt', 'verification/search-entry/all.ts.txt',
                    'verification/search-entry/source.json', 'HonoLean/Upstream/SearchEntry/Generated.lean']:
                file = base/relative; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative); file.write_bytes(original)
            clone = base/'checkout'; subprocess.run(['git', 'clone', '--shared', '--quiet', str(HONO), str(clone)], check=True)
            for source in ['src/router/trie-router/node.ts', 'src/router.ts']:
                subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', source], check=True)
                file = clone/source; original = file.read_bytes(); file.write_bytes(original+b'\n')
                self.assertEqual(subprocess.check_output(['git', '-C', str(clone), 'status', '--porcelain']).strip(), b'')
                self.assertNotEqual(invoke(['python3', str(script), '--hono', str(clone)]).returncode, 0)
                file.write_bytes(original)


if __name__ == '__main__':
    unittest.main(argv=['search-entry-tests'])
