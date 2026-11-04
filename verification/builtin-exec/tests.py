#!/usr/bin/env python3
"""Finite evidence for a conditional range-plus builtin exec source connection."""
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
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--hono', type=Path, required=True)
HONO = p.parse_args().hono.resolve()
NODE = os.environ.get('HONO_NODE') or shutil.which('node')
SOURCE = (ROOT / 'verification/builtin-exec/full.ts.txt').read_text()
REVISION = '5ca49b0720755c585c9a9835f0a479ceea36fb52'


def units(text):
    raw = text.encode('utf-16-le', errors='surrogatepass')
    return [int.from_bytes(raw[i:i+2], 'little') for i in range(0, len(raw), 2)]


def tag(kind, **fields): return dict(kind=kind, **fields)
def string(value): return tag('string', units=value)
def function(ref): return tag('function', ref=ref)
def obj(ref): return tag('object', ref=ref)
def array(ref): return tag('array', ref=ref)
def number(value): return tag('number', value=value)


def descriptor(value, writable=True, enumerable=True, configurable=True):
    return dict(kind='data', value=value, writable=writable, enumerable=enumerable, configurable=configurable)


def own(name, value, **flags): return dict(key=units(name), **descriptor(value, **flags))


def match_view(value):
    return dict(zero=descriptor(string(value)), length=descriptor(number(1), enumerable=False, configurable=False),
                index=descriptor(number(0)), input=descriptor(string(value)), groups=descriptor(tag('undefined')))


def normalize(result):
    result = copy.deepcopy(result)
    for cell in result.get('objects', []):
        if 'own' in cell: cell['own'].sort(key=lambda item: item['key'])
    return result


def invoke(command, packet=None):
    result = subprocess.run(command, input=None if packet is None else json.dumps(packet),
                            cwd=ROOT, env=ENV, text=True, capture_output=True, timeout=180)
    if result.returncode: raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)


def model(packet): return invoke(['lake', 'env', 'lean', '--run', 'verification/builtin-exec/Driver.lean'], packet)


def native(packet, engine):
    result = invoke([engine, 'verification/builtin-exec/native.mjs', str(HONO)], packet)
    assert result['revision'] == REVISION and result['checkedPinnedBlobs'] == 315
    assert result['verified'] is False and result['observerVerified'] is False
    assert result['plainJavaScript'] is True and result['typescriptErasure'] is False
    return result['results']


def endpoints(pattern):
    # Independent eight-unit grammar, not an invocation of the Lean parser/VM.
    safe = lambda x: 48 <= x <= 57 or 65 <= x <= 90 or 97 <= x <= 122
    if len(pattern) != 8 or pattern[:2] != [94, 91] or pattern[3] != 45 or pattern[5:] != [93, 43, 36]: return None
    lo, hi = pattern[2], pattern[4]
    return (lo, hi) if safe(lo) and safe(hi) and lo <= hi else None


def accepts(pattern, value):
    lo, hi = endpoints(pattern)
    return bool(value) and all(lo <= unit <= hi for unit in value)


def oracle(case, source=SOURCE):
    """Independent contracts for the admitted closed fixtures; no JS execution."""
    if endpoints(case['pattern']) is None: return dict(parsed=False)
    handle = case.get('handle', 5)
    own_exec = case.get('ownExec', False) or handle != 5 or case.get('calleeKind', 'method') != 'method'
    fields = [own('lastIndex', number(case.get('lastIndex', 0)), writable=case.get('writable', True), enumerable=False, configurable=False),
              own('other', function(3)), own('borrowed', function(5))]
    if own_exec: fields.append(own('exec', number(0) if case.get('calleeKind') == 'number' else function(handle)))
    if 'spoofSource' in case: fields.append(own('source', string(case['spoofSource']), enumerable=False))
    objects = [dict(intrinsic='Object.prototype'), dict(own=fields, prototype=2, extensible=case.get('extensible', True)),
               dict(intrinsic='RegExp.prototype'), dict(own=[own('exec', function(3))], prototype=None, extensible=True)]
    selected = 3 if 'alternate.exec' in source or '.other(' in source else 5 if '.borrowed(' in source else handle
    if 'matcher.exec' in source and case.get('calleeKind') == 'number': return dict(parsed=True, ok=False)
    if selected == 5 and not case.get('brand', True): return dict(parsed=True, ok=False)
    if selected not in [3, 4, 5]: return dict(parsed=True, ok=False)  # model dispatch admission, not native noncallability
    value = units('x') if '(alternateInput)' in source else case['input']
    hit = selected == 5 and accepts(case['pattern'], value)
    heap = [[string(units('prior'))]]
    view = None
    if hit:
        result = array(1); heap.append([string(value)]); view = match_view(value)
    elif selected == 4:
        result = array(1); heap.append([string(value)])
    elif selected == 3: result = string(value)
    else: result = tag('null')
    name = 'result' if 'const result =' in source else 'm'
    m = result if name == 'm' else obj(3)
    guard = m['kind'] != 'null' and not (m['kind'] == 'string' and not m['units'])
    return normalize(dict(parsed=True, ok=True, declaredName=name, declaredValue=result, m=m, guard=guard,
                          heap=heap, objects=objects, view=view, priorView=match_view(units('prior')),
                          scope=True, brandsKept=True, priorKept=True))


def contexts():
    patterns = ['^[0-9]+$', '^[A-Z]+$', '^[a-z]+$', '^[A-z]+$', '^[9-A]+$', '^[0-0]+$', '^[z-z]+$']
    inputs = [units(x) for x in ['', '0', '12', '1234567890', 'Az', 'abc', '[\\]^_`', '9:@A', 'z',
                                '12\n', '12\r', '12\r\n', '12\u2028', '12\u2029', '１２', 'a/b']]
    inputs += [[0], [55296], [56320], [55357, 56832], list(range(128)), [49]*256]
    result = []
    for pattern, value in itertools.product(patterns, inputs):
        for last, writable, extensible, own_exec in [(0, True, True, False), (-7, False, True, False),
                                                    (17, True, False, True), (9007199254740991, False, False, False)]:
            result.append(dict(pattern=units(pattern), input=value, lastIndex=last, writable=writable,
                               extensible=extensible, ownExec=own_exec))
    for handle, branded, kind, value in itertools.product([3, 4, 5], [False, True], ['method', 'number'], inputs[:6]):
        result.append(dict(pattern=units(patterns[0]), input=value, handle=handle, brand=branded, calleeKind=kind))
    result += [dict(pattern=units(patterns[0]), input=value, spoofSource=units('^x$')) for value in inputs]
    rng = random.Random(156161)
    result += [dict(pattern=units(patterns[i % len(patterns)]), input=[rng.randrange(65536) for _ in range(i)]) for i in range(48)]
    return result


class Checks(unittest.TestCase):
    def assert_results(self, actual, expected):
        self.assertEqual(len(actual), len(expected))
        for index, (a, b) in enumerate(zip(actual, expected)):
            with self.subTest(context=index): self.assertEqual(normalize(a), b)

    def test_01_identity_and_tampering(self):
        invoke_command = ['python3', 'verification/builtin-exec/source.py', '--hono', str(HONO)]
        result = subprocess.run(invoke_command, cwd=ROOT, env=ENV, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); (root/'verification').mkdir(); (root/'HonoLean/Upstream').mkdir(parents=True)
            shutil.copytree(ROOT/'verification/builtin-exec', root/'verification/builtin-exec')
            shutil.copytree(ROOT/'HonoLean/Upstream/NodeRegExpExec', root/'HonoLean/Upstream/NodeRegExpExec')
            for relative in ['verification/builtin-exec/full.ts.txt', 'HonoLean/Upstream/NodeRegExpExec/Generated.lean']:
                path = root/relative; original = path.read_text(); path.write_text(original.replace('.exec(', '.other('))
                result = subprocess.run(['python3', str(root/'verification/builtin-exec/source.py'), '--hono', str(HONO)],
                                        cwd=ROOT, env=ENV, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0); path.write_text(original)

    def test_02_parser_compiler_operational_language(self):
        safe = list(range(48, 58)) + list(range(65, 91)) + list(range(97, 123))
        pairs = [(lo, hi) for lo in safe for hi in safe if lo <= hi]
        cases = []
        for lo, hi in pairs:
            pattern = [94, 91, lo, 45, hi, 93, 43, 36]
            cases += [dict(pattern=pattern, input=value) for value in [[], [lo], [hi], [lo, hi, lo], [lo-1], [hi+1]]]
        for start in range(0, len(cases), 1953):
            batch = cases[start:start+1953]
            actual = model(dict(coreCases=batch))
            for case, result in zip(batch, actual):
                lo, hi = endpoints(case['pattern'])
                code = [dict(op='assertStart'), dict(op='consumeRange', lower=lo, upper=hi),
                        dict(op='repeatRange', lower=lo, upper=hi), dict(op='assertEnd'), dict(op='accept')]
                outcome = dict(kind='matched', start=0, stop=len(case['input']), captures=0) if accepts(case['pattern'], case['input']) else dict(kind='noMatch')
                self.assertEqual(result, dict(parsed=True, compiled=code, outcome=outcome))
            self.assertEqual(len(actual), len(batch))
        print(f'{len(pairs)} ordered safe endpoint pairs / {len(cases)} independent VM-language cases')

    def test_03_real_builtin_and_current_ordinary_calls(self):
        cases = contexts(); expected = [oracle(case) for case in cases]
        self.assert_results(model(dict(cases=cases)), expected)
        for engine in ['bun', NODE]: self.assert_results(native(dict(cases=cases), engine), expected)
        print(f'{len(cases)} full-world model/oracle/Bun/Node contexts')

    def test_04_source_faults_and_borrowed_identity(self):
        cases = [dict(pattern=units('^[0-9]+$'), input=units(value)) for value in ['12', '', 'x', '12\n']]
        baseline = [oracle(case) for case in cases]
        faults = [SOURCE.replace('.exec(', '.other('), SOURCE.replace('(restPathString)', '(alternateInput)'),
                  SOURCE.replace('matcher.exec', 'alternate.exec'), SOURCE.replace('const m =', 'const result =')]
        for source in faults + [SOURCE.replace('.exec(', '.borrowed(')]:
            expected = [oracle(case, source) for case in cases]
            if source in faults: self.assertNotEqual(expected, baseline)
            else: self.assertEqual(expected, baseline)  # builtin identity, not method spelling
            packet = dict(source=source, cases=cases)
            self.assert_results(model(packet), expected)
            for engine in ['bun', NODE]: self.assert_results(native(packet, engine), expected)

    def test_05_model_admission_and_resource_boundaries(self):
        unsupported = ['^[0-9]*$', '[0-9]+', '^[0-9]+$x', '^[9-0]+$', '^[-9]+$', '^[0-9]+$\n', '^[0-9]+$/g', '^([0-9]+)$']
        self.assertEqual(model(dict(coreCases=[dict(pattern=units(pattern), input=units('12')) for pattern in unsupported])), [dict(parsed=False)]*len(unsupported))
        fuel = model(dict(coreCases=[dict(pattern=units('^[0-9]+$'), input=units('12'), fuel=0)]))[0]
        self.assertEqual(fuel['outcome'], dict(kind='exhausted'))
        for source in ['const m = matcher.exec()', 'const m = matcher.exec(restPathString, restPathString)',
                       'const m = matcher.exec(++restPathString)', 'const m = matcher.exec(m)']:
            self.assertEqual(model(dict(source=source, cases=[])), dict(parsed=False))
        case = dict(pattern=units('^[0-9]+$'), input=units('12'), handle=0)
        self.assertEqual(model(dict(cases=[case])), [dict(parsed=True, ok=False)])
        for engine in ['bun', NODE]:
            result = native(dict(cases=[case]), engine)[0]
            self.assertTrue(result['ok']); self.assertEqual(result['declaredValue'], number(0)); self.assertFalse(result['guard'])
            # Valid native regex grammar is wider than the declared Lean grammar.
            broader = dict(pattern=units('^[0-9]*$'), input=[])
            self.assertEqual(model(dict(cases=[broader])), [dict(parsed=False)])
            self.assertTrue(native(dict(cases=[broader]), engine)[0]['ok'])

    def test_06_native_boundaries_and_pinned_upstream(self):
        for engine in ['bun', NODE]:
            result = invoke([engine, 'verification/builtin-exec/boundary.mjs', str(HONO)])
            self.assertEqual(result['revision'], REVISION); self.assertEqual(result['checkedPinnedBlobs'], 315)
            self.assertFalse(result['verified']); self.assertTrue(result['nativeOnly']); self.assertEqual(result['sourceBytes'], 51)
            b = result['boundaries']
            self.assertEqual(b['brandBeforeInputCoercion'], [])
            self.assertEqual(b['inputThenLastIndexCoercion'], ['input-ToString', 'lastIndex-valueOf'])
            self.assertEqual(b['spoofSourceAndThrowingPublicFlagsIgnored'], [])
            self.assertTrue(b['readonlyAndFrozenNonglobal']); self.assertTrue(b['ordinaryReplacementSkipsBuiltinChecks'])
            self.assertTrue(b['noncallableHasNoFallback']); self.assertTrue(b['descriptors']['groups']['writable'])
        upstream = invoke(['bun', 'verification/builtin-exec/upstream.mjs', str(HONO)])
        self.assertFalse(upstream['verified']); self.assertFalse(upstream['nativeTypeScriptLoadingVerified'])
        self.assertEqual(upstream['checkedPinnedBlobs'], 315)
        self.assertEqual((upstream['matcherQueryCount'], upstream['routerQueryCount']), (18, 15))
        self.assertTrue(all(row['sameCachedTuple'] and row['lastIndexKept'] for row in upstream['matcherRecords']))


if __name__ == '__main__': unittest.main(argv=['builtin-exec'], verbosity=2)
