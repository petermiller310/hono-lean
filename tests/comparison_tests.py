#!/usr/bin/env python3
"""Failure probes for the comparator, source pin, and own-entry normalization."""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import compare_hono as harness


def observations(expected):
    result = deepcopy(expected)
    result['retained'] = [dict(before=deepcopy(item['matches']), after=deepcopy(item['matches']))
        for item in expected['results'] if 'matches' in item]
    return result


class ComparatorTests(unittest.TestCase):
    def setUp(self):
        self.case = dict(id='probe', routes=[
            dict(method='ALL', pattern='/students/*', handler='log'),
            dict(method='GET', pattern='/students/:id', handler='same'),
            dict(method='GET', pattern='/students/:id', handler='same')], steps=[
            dict(op='lookup', request=dict(method='GET', path='/students/s1')),
            dict(op='register', route=dict(method='POST', pattern='/students/:id', handler='write')),
            dict(op='lookup', request=dict(method='GET', path='/students/s2')),
            dict(op='lookup', request=dict(method='POST', path='/students/s3'))])
        self.expected = harness.expected_trace(self.case)
        self.hono = observations(self.expected)

    def reject(self, *, case=None, lean=None, hono=None):
        with self.assertRaises((ValueError, AssertionError, KeyError, TypeError)):
            harness.compare(case or self.case, self.expected,
                self.expected if lean is None else lean, self.hono if hono is None else hono)

    def test_control_and_object_key_order(self):
        self.assertEqual(harness.compare(self.case, self.expected, self.expected, self.hono), (3, 0))
        self.assertTrue(harness.same_json({'a': 1, 'b': 2}, {'b': 2, 'a': 1}))
        self.assertFalse(harness.same_json(True, 1))

    def test_result_faults_are_not_normalized_away(self):
        for fault in ('missing', 'reversed', 'duplicated', 'wrong_capture', 'wrong_type'):
            with self.subTest(fault=fault):
                bad = deepcopy(self.hono)
                items = bad['results'][0]['matches']
                if fault == 'missing': items.pop()
                elif fault == 'reversed': items.reverse()
                elif fault == 'duplicated': items.append(deepcopy(items[0]))
                elif fault == 'wrong_capture': items[1]['params']['id'] = 'wrong'
                else: items[0]['registration'] = False
                self.reject(hono=bad)
        lean = deepcopy(self.expected)
        lean['results'][0]['matches'].pop()
        self.reject(lean=lean)
        bad = deepcopy(self.hono)
        bad['nextRegistration'] = 99
        self.reject(hono=bad)

    def test_retained_records_are_required_and_compared_to_actual_results(self):
        for fault in ('empty', 'missing', 'reversed', 'wrong_before', 'wrong_after'):
            with self.subTest(fault=fault):
                bad = deepcopy(self.hono)
                if fault == 'empty': bad['retained'] = []
                elif fault == 'missing': bad['retained'].pop()
                elif fault == 'reversed': bad['retained'].reverse()
                elif fault == 'wrong_before':
                    bad['retained'][0]['before'] = bad['retained'][0]['after'] = []
                else: bad['retained'][0]['after'] = []
                self.reject(hono=bad)

    def test_tampered_fixture_expected_is_rejected(self):
        case = deepcopy(self.case)
        case['steps'][0]['expected'] = []
        with self.assertRaises(AssertionError): harness.expected_trace(case)

    def test_d1_is_one_complete_exact_witness(self):
        case = dict(id='parameter-name-is-data', routes=deepcopy(harness.D1_ROUTES),
                    steps=[deepcopy(harness.D1_STEP)])
        expected = harness.expected_trace(case)
        hono = observations(expected)
        hono['results'][0]['matches'] = deepcopy(harness.D1_BASELINE)
        hono['retained'] = [dict(before=deepcopy(harness.D1_BASELINE), after=deepcopy(harness.D1_BASELINE))]
        self.assertEqual(harness.compare(case, expected, expected, hono), (0, 1))
        for fault in ('missing_metadata', 'altered_metadata', 'request', 'method', 'table', 'generated'):
            with self.subTest(fault=fault):
                bad = deepcopy(case)
                if fault == 'missing_metadata': del bad['steps'][0]['baselineExpected']
                elif fault == 'altered_metadata': bad['steps'][0]['baselineExpected'] = []
                elif fault == 'request': bad['steps'][0]['request']['path'] = '/beta'
                elif fault == 'method': bad['routes'][0]['method'] = 'ALL'
                elif fault == 'table': bad['routes'].append(deepcopy(bad['routes'][0]))
                else: bad['id'] = 'generated-000'
                with self.assertRaises(ValueError): harness.compare(bad, expected, expected, hono)
        bad = deepcopy(hono); bad['results'][0]['extra'] = True
        with self.assertRaises(ValueError): harness.compare(case, expected, expected, bad)
        bad = deepcopy(hono); bad['results'][0]['matches'][0]['params']['__proto__'] = None
        with self.assertRaises(ValueError): harness.compare(case, expected, expected, bad)
        with self.assertRaises(ValueError): harness.compare(case, expected, dict(results=hono['results'], nextRegistration=1), hono)


class BoundaryTests(unittest.TestCase):
    def test_pin_and_cleanliness(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'hono'
            harness.command(['git', 'clone', '--quiet', '--shared', str(HONO), str(path)])
            self.assertEqual(harness.verify_checkout(path), path.resolve())
            tracked = path / 'src/router/trie-router/router.ts'
            original = tracked.read_text(); tracked.write_text(original + '\n// dirty probe\n')
            with self.assertRaisesRegex(ValueError, 'changes'): harness.verify_checkout(path)
            tracked.write_text(original)
            (path / 'untracked-probe').write_text('probe')
            with self.assertRaisesRegex(ValueError, 'changes'): harness.verify_checkout(path)
            (path / 'untracked-probe').unlink()
            with patch.dict(harness.BASELINE, revision='0' * 40):
                with self.assertRaisesRegex(ValueError, 'pinned'): harness.verify_checkout(path)
            with self.assertRaises(ValueError): harness.verify_checkout(Path(tmp) / 'missing')

    def test_fetch_never_overwrites_an_existing_directory(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(harness, 'ROOT', Path(tmp)):
            path = Path(tmp) / '.hono-cache'; path.mkdir()
            sentinel = path / 'keep'; sentinel.write_text('keep')
            with self.assertRaises(ValueError): harness.fetch_checkout()
            self.assertEqual(sentinel.read_text(), 'keep')

    def test_fetch_is_isolated_and_uses_the_exact_revision(self):
        # Exercise real Git fetch/checkout without network or edits to the source.
        with tempfile.TemporaryDirectory() as tmp, patch.object(harness, 'ROOT', Path(tmp)), \
                patch.dict(harness.BASELINE, repository=str(HONO)):
            expected = (Path(tmp) / '.hono-cache').resolve()
            self.assertEqual(harness.fetch_checkout(), expected)
            self.assertEqual(harness.fetch_checkout(), expected)

    def test_runner_does_not_drop_undefined_captures(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / 'src/router/trie-router/router.ts'
            source.parent.mkdir(parents=True)
            source.write_text('export class TrieRouter { payload: any; add(_m:any,_p:any,h:any){this.payload=h;} '
                'match(){return [[[this.payload, {id:undefined}]]];}}')
            case = dict(routes=[dict(method='GET', pattern='/:id', handler='read')],
                        steps=[dict(op='lookup', request=dict(method='GET', path='/a'))])
            output = json.loads(harness.command(['bun', str(harness.ROOT / 'comparison/hono_runner.ts'), tmp], input=json.dumps([case])))
            self.assertIn('undefined', output[0]['runnerError'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hono', type=Path, required=True)
    args, rest = parser.parse_known_args()
    HONO = harness.verify_checkout(args.hono)
    unittest.main(argv=[__file__, *rest])
