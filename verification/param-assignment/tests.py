#!/usr/bin/env python3
"""Pinned assignment-fragment evidence; never claims whole-Node execution."""
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


def invoke(command, document=None):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=ROOT, env=ENV, text=True, capture_output=True)


def model(document):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/param-assignment/Driver.lean'], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(document):
    result = invoke(['bun', 'verification/param-assignment/native.ts', str(HONO)], document)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    observed = json.loads(result.stdout)
    assert observed['runtime'] == '1.4.0'
    return observed['results']


def inherited(key):
    if key == units('__proto__'):
        return dict(kind='object', ref=0)
    if key == units('constructor'):
        return dict(kind='constructor')
    return UNDEFINED


def truthy(value):
    kind = value['kind']
    if kind in ['undefined', 'null']:
        return False
    if kind == 'bool':
        return value['value']
    if kind == 'number':
        return value['value'] != 0
    if kind == 'string':
        return bool(value['units'])
    return True


def expected(case):
    parameter = (case['p'] if case['pMode'] == 'own' else inherited(case['key'])
                 if case['pMode'] == 'inherited' else UNDEFINED)
    node = case['node'] if case['nodeOwn'] else inherited(case['key'])
    if truthy(parameter) and case['index'] == 0:
        selected = parameter
    elif node['kind'] not in ['undefined', 'null']:
        selected = node
    else:
        selected = parameter
    return dict(returned=selected, output=selected, own=True, prototype=None, frameKept=True,
                retainedSeed=string('frame') if case.get('prepopulate') else UNDEFINED,
                ownCount=2 if case.get('prepopulate') else 1,
                descriptor=dict(writable=True, enumerable=True, configurable=True))


class AssignmentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        result = invoke(['python3', 'verification/param-assignment/source.py', '--hono', str(HONO)])
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def test_exact_fragment_all_branch_values_and_frame(self):
        values = [UNDEFINED, NULL, dict(kind='bool', value=False), dict(kind='bool', value=True),
                  dict(kind='number', value=0), dict(kind='number', value=1), dict(kind='number', value=-1),
                  string(''), string('alpha'), dict(kind='object', ref=0),
                  dict(kind='array', ref=0), dict(kind='constructor')]
        parameters = [(mode, UNDEFINED) for mode in ['undefined', 'null', 'missing', 'inherited']]
        parameters += [('own', value) for value in values]
        nodes = [(False, UNDEFINED)] + [(True, value) for value in values]
        cases = [dict(key=units(key), index=index, pMode=mode, p=parameter,
                      nodeOwn=own, node=node)
                 for key, index, (mode, parameter), (own, node) in itertools.product(
                     ['id', '__proto__', 'constructor', '\ud800'], [0, 1, 2], parameters, nodes)]
        oracle = [expected(case) for case in cases]
        self.assertEqual(native(dict(cases=cases)), oracle)
        self.assertEqual(model(dict(cases=cases)), oracle)
        print(f'Assignment fragment audit: {len(cases)} branch/context observations', flush=True)

    def test_preserves_earlier_output_entries(self):
        cases = [dict(key=units(key), index=index, pMode=mode, p=string('parent'), nodeOwn=True,
                      node=value, prepopulate=True)
                 for key, index, mode, value in itertools.product(
                     ['id', '__proto__', 'constructor'], [0, 1, 2], ['own', 'null', 'missing'],
                     [UNDEFINED, NULL, dict(kind='bool', value=False), dict(kind='number', value=0), string('')])]
        oracle = [expected(case) for case in cases]
        self.assertEqual(native(dict(cases=cases)), oracle)
        self.assertEqual(model(dict(cases=cases)), oracle)
        print(f'Assignment output-frame audit: {len(cases)} populated-output cases', flush=True)

    def test_real_parsed_source_body_faults(self):
        source = (ROOT / 'verification/param-assignment/assignment.ts.txt').read_text()
        variants = [
            (source.replace(' && !i', ''), 1, string('parent')),
            (source.replace('&& !i', '&& i'), 0, string('parent')),
            (source.replace('nodeParams[key] ?? params?.[key]', 'params?.[key] ?? nodeParams[key]'),
             0, dict(kind='bool', value=False))]
        for changed, index, parameter in variants:
            self.assertNotEqual(changed, source)
            case = dict(key=units('id'), index=index, pMode='own', p=parameter,
                        nodeOwn=True, node=string('node'))
            packet = dict(cases=[case], source=changed)
            observed = native(packet)
            self.assertEqual(model(packet), observed)
            self.assertNotEqual(observed, [expected(case)])

    def test_source_context_and_generated_artifact_identity(self):
        with tempfile.TemporaryDirectory(prefix='hono-parameter-source-') as temporary:
            base = Path(temporary)
            script = base / 'verification/param-assignment/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT / 'verification/param-assignment/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            result = invoke(command + ['--write'])
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/param-assignment/assignment.ts.txt',
                             'verification/param-assignment/source.json',
                             'HonoLean/Upstream/NodeParamAssignment/Generated.lean']:
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
    unittest.main(argv=['parameter-assignment-tests'])
