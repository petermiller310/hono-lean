#!/usr/bin/env python3
"""Evidence for the exact chosen-handler block; not whole-Node verification."""
import argparse
import itertools
import json
import os
from pathlib import Path
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
UNDEFINED = dict(kind='undefined')
NULL = dict(kind='null')


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def string(text):
    return dict(kind='string', units=units(text))


def entry(key, value):
    return dict(key=units(key), value=value)


def invoke(command, document=None):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(document):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/param-loop/Driver.lean'], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(document):
    result = invoke(['bun', 'verification/param-loop/native.ts', str(HONO)], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    packet = json.loads(result.stdout)
    assert packet['runtime'] == '1.4.0'
    return packet['results']


def truthy(value):
    kind = value['kind']
    if kind in ['undefined', 'null']:
        return False
    if kind in ['bool', 'number']:
        return bool(value['value'])
    if kind == 'string':
        return bool(value['units'])
    return True


def inherited(key):
    if key == units('__proto__'):
        return dict(kind='object', ref=0)
    if key == units('constructor'):
        return dict(kind='constructor')
    return UNDEFINED


def lookup(entries, key, ordinary):
    for item in reversed(entries):
        if item['key'] == key:
            return item['value']
    return inherited(key) if ordinary else UNDEFINED


def handler_lookup(key):
    # Snapshot AFTER the source resets .params and appends the handler.
    if key == units('params'):
        return dict(kind='object', ref=6)
    if key == units('possibleKeys'):
        return dict(kind='array', ref=0)
    return inherited(key)


def expected(case):
    output = {}
    for index, key in enumerate(case['keys']):
        mode = case.get('parameterMode', 'nullproto')
        parameter = (UNDEFINED if mode in ['undefined', 'null'] else handler_lookup(key)
                     if mode == 'handler' else lookup(case.get('parameterEntries', []), key, mode == 'ordinary'))
        node = (handler_lookup(key) if case.get('nodeMode') == 'handler' else
                lookup(case.get('nodeEntries', []), key, True))
        value = parameter if truthy(parameter) and index == 0 else (
            node if node['kind'] not in ['undefined', 'null'] else parameter)
        output[tuple(key)] = dict(key=key, value=value, writable=True, enumerable=True, configurable=True)
    return dict(output=dict(kind='object', ref=6), fresh=True, nullPrototype=True,
                entries=[output[key] for key in sorted(output)],
                handlerSets=[dict(kind='object', ref=ref) for ref in case.get('priorHandlers', [])] +
                            [dict(kind='object', ref=3)],
                scope=[dict(kind='number', value=55), dict(kind='number', value=66), string('outer')],
                frameKept=True, oldOutputIntact=True)


class LoopTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        for checker in ['verification/nullobject/source.py', 'verification/param-loop/source.py']:
            result = invoke(['python3', checker, '--hono', str(HONO)])
            if result.returncode:
                raise AssertionError(result.stdout + result.stderr)

    def check_cases(self, cases):
        packet = dict(cases=cases)
        oracle = [expected(case) for case in cases]
        self.assertEqual(native(packet), oracle)
        self.assertEqual(model(packet), oracle)

    def test_multikey_selection_and_aliases(self):
        values = [UNDEFINED, NULL, dict(kind='bool', value=False), dict(kind='bool', value=True),
                  dict(kind='number', value=0), dict(kind='number', value=-1), string(''), string('alpha'),
                  dict(kind='object', ref=0), dict(kind='object', ref=3), dict(kind='array', ref=0),
                  dict(kind='array', ref=1), dict(kind='constructor'), dict(kind='function', ref=0)]
        keys = ['id', '__proto__', 'constructor', '\ud800']
        cases = []
        for mode, node_mode, parameter, node in itertools.product(
                ['undefined', 'null', 'nullproto', 'ordinary', 'handler'], ['node', 'handler'], values, values):
            shift = len(cases) % len(keys)
            ordered = keys[shift:] + keys[:shift]
            cases.append(dict(keys=[units(key) for key in ordered], parameterMode=mode, nodeMode=node_mode,
                              parameterEntries=[entry(key, parameter) for key in ordered],
                              nodeEntries=[entry(key, node) for key in ordered],
                              priorHandlers=[3, 5, 3], shadowObject=True))
        self.check_cases(cases)
        print(f'Chosen-handler block audit: {len(cases)} multikey branch/alias contexts', flush=True)

    def test_empty_long_and_post_reset_reads(self):
        cases = [dict(keys=[], parameterMode='undefined', priorHandlers=[3]),
                 dict(keys=[units('params')], parameterMode='handler', nodeMode='handler', priorHandlers=[3]),
                 dict(keys=[units('params')], parameterMode='handler', nodeMode='handler', priorHandlers=[3], oldParamsSelf=True),
                 dict(keys=[units('possibleKeys'), units('params')], parameterMode='handler', nodeMode='handler'),
                 dict(keys=[units('__proto__'), units('constructor'), units('id')], parameterMode='ordinary')]
        for count in [1, 2, 33, 96]:
            keys = [str(index) for index in range(count)]
            cases.append(dict(keys=[units(key) for key in keys], parameterMode='nullproto',
                              nodeEntries=[entry(key, string('node-' + key)) for key in keys],
                              parameterEntries=[entry(key, string('prior-' + key)) for key in keys],
                              priorHandlers=[5, 3]))
        self.check_cases(cases)
        print(f'Chosen-handler scope/bounds audit: {len(cases)} cases including 96 keys', flush=True)

    def test_parsed_real_source_mutants(self):
        source = (ROOT / 'verification/param-loop/loop.ts.txt').read_text()
        case = dict(keys=[units('a'), units('b')], parameterMode='nullproto',
                    nodeEntries=[entry('a', string('node-a')), entry('b', string('node-b'))],
                    parameterEntries=[entry('a', string('prior-a')), entry('b', string('prior-b'))])
        variants = [source.replace('let i = 0', 'let i = 1'),
                    source.replace('len = handlerSet.possibleKeys.length', 'len = 0'),
                    source.replace('handlerSets.push(handlerSet)', 'handlerSets.push(nodeParams)'),
                    source.replace(' && !i', '')]
        for changed in variants:
            self.assertNotEqual(changed, source)
            packet = dict(source=changed, cases=[case])
            observed = native(packet)
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [expected(case)])

    def test_source_and_generated_freshness(self):
        with tempfile.TemporaryDirectory(prefix='hono-loop-source-') as temporary:
            base = Path(temporary)
            script = base / 'verification/param-loop/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/param-loop/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command + ['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/param-loop/loop.ts.txt', 'verification/param-loop/source.json',
                             'HonoLean/Upstream/NodeParamLoop/Generated.lean']:
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
    unittest.main(argv=['param-loop-tests'])
