#!/usr/bin/env python3
"""Pinned whole child loop: descriptor entry, scope, private write and queue."""
import argparse
import copy
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
NODE = os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE = (ROOT / 'verification/child-enumeration/full.ts.txt').read_text()


def value(kind, **fields):
    return dict(kind=kind, **fields)


U, N = value('undefined'), value('null')
F, T = value('bool', value=False), value('bool', value=True)
Z, SEVEN = value('number', value=0), value('number', value=7)
S = lambda units: value('string', units=list(units))
A = lambda ref: value('array', ref=ref)
O = lambda ref: value('object', ref=ref)


def prop(key, enumerable=True, kind='data', item=F):
    result = dict(key=list(key), kind=kind, enumerable=enumerable, configurable=True)
    if kind == 'data':
        result.update(value=copy.deepcopy(item), writable=True)
    return result


def fixture(properties=None, text=(97, 47, 98), queue=None, params=None, alias=False):
    return dict(heap=[copy.deepcopy([] if queue is None else queue), [S(text), S([47, 47])], [O(1)], []],
                objects=[dict(prototype=None, own=[]) for _ in range(5)],
                private=dict(children=O(2), params=O(3), keep=SEVEN),
                bindings=dict(child=O(0), params=O(1) if params is None else params,
                              m=A(0 if alias else 1), curNodesQueue=A(0)),
                _properties=properties)


def prepared(case):
    result = copy.deepcopy(case)
    properties = result.pop('_properties', None)
    result['objects'][2]['own'] = copy.deepcopy([prop([120])] if properties is None else properties)
    return result


def invoke(command, packet=None):
    return subprocess.run(command, cwd=ROOT, env=ENV, text=True, capture_output=True,
                          input=None if packet is None else json.dumps(packet), timeout=300)


def model(packet):
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/child-enumeration/Driver.lean'], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def native(packet, runtime='bun'):
    result = invoke([runtime, 'verification/child-enumeration/native.mjs', str(HONO)], packet)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    output = json.loads(result.stdout)
    assert output['revision'] == '5ca49b0720755c585c9a9835f0a479ceea36fb52'
    assert output['checkedPinnedBlobs'] == 315
    assert output['execution']['verified'] is False
    assert output['execution']['fragmentTypeErasure'] is False
    assert output['execution']['sourceBytes'] == 317
    assert output['execution']['sourceOverride'] == ('source' in packet)
    assert output['execution']['graph'] == 'canonical visible graph; unreachable internal allocations omitted'
    return output


def canonical(result, root_count):
    """Retained initial arrays + final private values, then BFS own-slot edges.

    Unreachable model accumulators are omitted. No unreachable native array or
    internal allocation count is fabricated. Object cells keep their input IDs.
    Descriptor-store order is observed extensionally, independently of for-in.
    """
    if not result['ok']:
        return dict(ok=False)
    state = result['state']
    heap, references = state['heap'], list(range(root_count))

    def encode(item):
        item = copy.deepcopy(item)
        if item['kind'] == 'array':
            reference = item['ref']
            assert 0 <= reference < len(heap)
            if reference not in references:
                references.append(reference)
            item['ref'] = references.index(reference)
        return item

    fields = {name: encode(state['private'][name]) for name in ['children', 'params', 'keep']}
    visible, at = [], 0
    while at < len(references):
        visible.append([None if item is None else encode(item) for item in heap[references[at]]])
        at += 1
    objects = copy.deepcopy(state['objects'])
    for object in objects:
        for property in object['own']:
            if property['kind'] == 'data':
                property['value'] = encode(property['value'])
        object['own'].sort(key=lambda property: property['key'])
    # Initial object descriptors can reference only initial allocated arrays;
    # source never mutates these ordinary properties in the admitted domain.
    assert len(references) == len(visible)
    return dict(ok=True, state=dict(private=fields, heap=visible, objects=objects, scope=state['scope']))


def truthy(item):
    return (item['kind'] not in ['null', 'undefined'] and
            (item['kind'] != 'bool' or item['value']) and
            (item['kind'] != 'number' or item['value'] != 0) and
            (item['kind'] != 'string' or bool(item['units'])))


def oracle(case):
    """Independent descriptor existence, index-set count and own-slot effects."""
    heap, objects, fields = copy.deepcopy(case['heap']), copy.deepcopy(case['objects']), copy.deepcopy(case['private'])
    bindings = case['bindings']
    if bindings.get('child') != O(0):
        return dict(ok=False), []
    children = fields['children']
    if children['kind'] != 'object' or children['ref'] >= len(objects):
        return dict(ok=False), []
    selected = objects[children['ref']]
    if selected['prototype'] is not None:
        return dict(ok=False), []
    traces = []
    if any(property['enumerable'] for property in selected['own']):
        if 'params' not in bindings or 'm' not in bindings or 'curNodesQueue' not in bindings:
            return dict(ok=False), []
        fields['params'] = copy.deepcopy(bindings['params'])
        m, queue = bindings['m'], bindings['curNodesQueue']
        if m['kind'] != 'array' or m['ref'] >= len(heap):
            return dict(ok=False), []
        matched = heap[m['ref']]
        if not matched or matched[0] is None or matched[0]['kind'] != 'string':
            return dict(ok=False), []
        text = matched[0]['units']
        positions = [index for index in range(len(text)) if text[index] == 47]
        count = len(positions)
        heap.append([S([47]) for _ in positions])
        if queue['kind'] != 'array' or queue['ref'] >= len(heap):
            return dict(ok=False), []
        row = heap[queue['ref']]
        target = row[count] if count < len(row) and row[count] is not None else U
        if not truthy(target):
            target = A(len(heap)); heap.append([])
            row.extend([None] * max(0, count + 1 - len(row)))
            row[count] = target
        if target['kind'] != 'array' or target['ref'] >= len(heap):
            return dict(ok=False), []
        heap[target['ref']].append(copy.deepcopy(bindings['child']))
        traces = [dict(positions=positions, lastIndexTrace=[0] + [index + 1 for index in positions] + [0],
                       unit=47, lastIndex=0, match=[[47] for _ in positions] if positions else None)]
    raw = dict(ok=True, state=dict(private=fields, heap=heap, objects=objects, scope=True))
    return canonical(raw, len(case['heap'])), traces


def contexts():
    cases = []
    keys = [[], [120], [48]]
    for size in range(4):
        for flags in itertools.product([False, True], repeat=size):
            for kinds in itertools.product(['data', 'accessor'], repeat=size):
                properties = [prop(keys[index], flag, kind) for index, (flag, kind) in enumerate(zip(flags, kinds))]
                for mode in ['normal', 'missing', 'invalid']:
                    item = fixture(properties)
                    if mode == 'missing': item['bindings'] = dict(child=O(0))
                    if mode == 'invalid': item['bindings'].update(m=N, curNodesQueue=Z)
                    cases.append(prepared(item))
    for length in range(4):
        for text in itertools.product([0, 47, 97, 0xD800, 0xDC00], repeat=length):
            cases.append(prepared(fixture([prop([], True)], text)))
    for params in [U, N, F, T, Z, S([]), O(0), O(2), A(0), A(1)]:
        for queue in [[], [None, U], [A(0), A(2)], [F, A(3)], [T, SEVEN]]:
            cases.append(prepared(fixture([prop([109]), prop([112]), prop([50])], params=params, queue=queue)))
    for text in [[], [97], [47], [47, 97, 47]]:
        cases.append(prepared(fixture([prop([95])], text, [S(text)], alias=True)))
    rng = random.Random(174180)
    options = [None, U, N, F, T, Z, S([]), A(0), A(2), A(3)]
    for _ in range(130):
        text = [rng.choice([0, 47, 97, 0xD800, 0xDC00]) for _ in range(rng.randrange(25))]
        properties = [prop([index, 0xD800], rng.choice([True, False]), rng.choice(['data', 'accessor']),
                           rng.choice([F, Z, N, U, O(0), A(0)])) for index in range(rng.randrange(6))]
        cases.append(prepared(fixture(properties, text, [copy.deepcopy(rng.choice(options)) for _ in range(rng.randrange(5))])))
    for size in [32, 127, 512]:
        cases.append(prepared(fixture([prop([120])], [47] * size)))
    return cases


class ChildEnumerationTests(unittest.TestCase):
    def compare(self, cases, runtime='bun', **overrides):
        packet = dict(cases=cases, **overrides)
        modeled, observed = model(packet), native(packet, runtime)
        self.assertTrue(modeled['parsed'])
        states, traces = [], []
        for case, modeledResult, control, instrumented in zip(cases, modeled['results'], observed['controls'], observed['instrumented'], strict=True):
            expected = canonical(modeledResult, len(case['heap']))
            self.assertEqual(canonical(control, len(case['heap'])), expected)
            self.assertEqual(canonical(instrumented, len(case['heap'])), expected)
            if expected['ok']:
                self.assertEqual(control['state']['getterReads'], 0)
                self.assertEqual(instrumented['state']['getterReads'], 0)
                nativeTraces = [{key: value for key, value in trace.items() if key != 'paramsAtMatch'} for trace in instrumented['traces']]
                self.assertEqual(modeledResult['traces'], nativeTraces)
                traces.append(nativeTraces)
                if 'source' not in overrides and nativeTraces:
                    self.assertEqual(instrumented['traces'][0]['paramsAtMatch'], expected['state']['private']['params'])
            else:
                traces.append([])
            states.append(expected)
        return states, traces

    def test_complete_loop(self):
        cases = contexts()
        states, traces = self.compare(cases)
        expected = [oracle(case) for case in cases]
        self.assertEqual(states, [item[0] for item in expected])
        self.assertEqual(traces, [item[1] for item in expected])
        print(f'Child loop: {len(cases)} descriptor/skip/rawUTF16/alias/long contexts', flush=True)

    def test_source_faults_and_syntax(self):
        cases = [prepared(fixture([prop([120]), prop([121]), prop([122])], text)) for text in [[], [97], [47], [47, 97, 47]]]
        expected, expectedTraces = zip(*(oracle(case) for case in cases))
        faults = [SOURCE.replace('                break\n', ''),
                  SOURCE.replace('child.#params = params', 'child.#params = child'),
                  SOURCE.replace('child.#params = params', 'child.#children = params'),
                  SOURCE.replace('/\\//g', '/a/g'), SOURCE.replace('?? 0', '?? 1'),
                  SOURCE.replace('[componentCount]', '[0]'), SOURCE.replace('push(child)', 'push(params)'),
                  SOURCE.replace('child.#params = params\n', 'child.#params = params\n                break\n')]
        for source in faults:
            states, traces = self.compare(cases, source=source)
            self.assertNotEqual((states, traces), (list(expected), list(expectedTraces)), source)
        rejected = [SOURCE.replace('const _ in', 'let _ in'), SOURCE.replace('const _ in', 'const child in'),
                    SOURCE.replace('const _ in', 'const [x] in'), SOURCE.replace(' in ', ' of '),
                    SOURCE.replace('push(child)', 'push(_)'), SOURCE.replace('break\n', 'break label\n'),
                    SOURCE.replace('child.#params = params', 'child.#params = _'),
                    SOURCE.replace('child.#params = params', 'params = child'), SOURCE + 'unknown\n',
                    SOURCE + '/* trailing */\n', SOURCE.replace('/\\//g', '/./g')]
        for source in rejected:
            self.assertFalse(model(dict(cases=[], source=source))['parsed'], source)
        for source in [SOURCE.replace('\n', '\r\n'), SOURCE.rstrip(), SOURCE.replace('const _ in', 'const unused in')]:
            self.assertEqual(self.compare(cases, source=source), (list(expected), list(expectedTraces)))
        # Native-only order counterexample: same final graph, wrong write timing.
        assignment = '                child.#params = params\n'
        reordered = SOURCE.replace(assignment, '').replace('                break\n', assignment + '                break\n')
        observed = native(dict(cases=cases[:1], source=reordered))
        self.assertNotEqual(observed['instrumented'][0]['traces'][0]['paramsAtMatch'], cases[0]['bindings']['params'])

    def test_node_boundary(self):
        self.assertIsNotNone(NODE, 'Use HONO_NODE or put Node22.22.2 on PATH')
        cases = contexts()[::17]
        states, traces = self.compare(cases, NODE)
        expected = [oracle(case) for case in cases]
        self.assertEqual(states, [item[0] for item in expected])
        self.assertEqual(traces, [item[1] for item in expected])
        for runtime in ['bun', NODE]:
            result = invoke([runtime, 'verification/child-enumeration/boundary.mjs'])
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            output = json.loads(result.stdout)
            self.assertFalse(output['verified']); self.assertEqual(output['getterReads'], 0)
            self.assertEqual(len(output['observations']), 12)
        outside = prepared(fixture())
        outside['objects'][2]['prototype'] = 1
        self.assertEqual(model(dict(cases=[outside]))['results'], [dict(ok=False)])

    def test_identity(self):
        result = invoke(['python3', 'verification/child-enumeration/source.py', '--hono', str(HONO)])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            files = ['verification/child-enumeration/source.py', 'verification/child-enumeration/source.json',
                     'verification/child-enumeration/full.ts.txt', 'verification/child-enumeration/prefix.ts.txt',
                     'verification/child-enumeration/suffix.ts.txt', 'HonoLean/Upstream/NodeChildEnumeration/Generated.lean',
                     'verification/component-count/source.json', 'verification/component-count/full.ts.txt']
            for file in files:
                path = root / file; path.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(ROOT / file, path)
            for file in files[1:]:
                path = root / file; before = path.read_bytes()
                if file.endswith('component-count/source.json'):
                    changed = json.loads(before); changed['fragments']['full']['startByte'] += 1
                    path.write_text(json.dumps(changed))
                else:
                    path.write_bytes(before + b'\n')
                result = invoke(['python3', str(root / files[0]), '--hono', str(HONO)])
                self.assertNotEqual(result.returncode, 0, file); path.write_bytes(before)
            clone = root / 'hono'
            subprocess.run(['git', 'clone', '--quiet', '--shared', '--no-checkout', str(HONO), str(clone)], check=True, env=ENV)
            subprocess.run(['git', '-C', str(clone), 'checkout', '--quiet', '--detach', '5ca49b0720755c585c9a9835f0a479ceea36fb52'], check=True, env=ENV)
            path = clone / 'src/router/trie-router/node.ts'; path.write_bytes(path.read_bytes() + b'\n')
            subprocess.run(['git', '-C', str(clone), 'update-index', '--assume-unchanged', 'src/router/trie-router/node.ts'], check=True, env=ENV)
            result = invoke(['python3', str(root / files[0]), '--hono', str(clone)])
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main(argv=['child-enumeration'])
