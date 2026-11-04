#!/usr/bin/env python3
"""Validate source-bound routing worklist and isolated finite method observations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[1]
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0', GIT_OPTIONAL_LOCKS='0')
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
args = parser.parse_args()
HONO = args.hono.resolve()
LEDGER = json.loads((ROOT / 'verification/routing-behaviors.json').read_text())


class RoutingEvidenceTests(unittest.TestCase):
    def test_hashes_references_and_unresolved_evidence(self):
        revision = subprocess.check_output(['git', '-C', str(HONO), 'rev-parse', 'HEAD'], env=ENV, text=True).strip()
        self.assertEqual(revision, LEDGER['targetRevision'])
        snapshots = LEDGER['sourceSnapshots']
        for source, snapshot in snapshots.items():
            raw = (HONO / source).read_bytes()
            pinned = subprocess.check_output(['git', '-C', str(HONO), 'show', revision + ':' + source], env=ENV)
            self.assertEqual(raw, pinned, source)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), snapshot['sha256'], source)
            blob = subprocess.check_output(['git', '-C', str(HONO), 'rev-parse', revision + ':' + source], env=ENV, text=True).strip()
            self.assertEqual(blob, snapshot['gitBlob'])
            self.assertEqual(len(raw.decode().splitlines()), snapshot['lineCount'], source)
        cases = LEDGER['commonFixture']['cases']
        ids = {case['id'] for case in cases}
        self.assertEqual(len(ids), len(cases))
        self.assertEqual(len(cases), LEDGER['summary']['commonLiteralTestCases'])
        units = LEDGER['behaviorUnits']
        self.assertEqual(len({unit['id'] for unit in units}), len(units))
        self.assertEqual(len(units), LEDGER['summary']['candidateBehaviorUnits'])
        checked = sum(unit['proofEvidence']['sourceConnection'] == 'checked' for unit in units)
        self.assertEqual(checked, LEDGER['summary']['sourceConnectedRoutingBehaviorUnits'])
        self.assertIsNone(LEDGER['summary']['coveragePercentage'])
        for unit in units:
            if 'conditionalSourceEvidence' in unit:
                evidence = unit['conditionalSourceEvidence']
                registry = json.loads((ROOT / evidence['registry']).read_text())
                known_slices = {entry['id'] for entry in registry['slices']}
                self.assertTrue(set(evidence['slices']).issubset(known_slices), unit['id'])

        def walk(value, source=None):
            if isinstance(value, list):
                for child in value:
                    walk(child, source)
            elif isinstance(value, dict):
                source = value.get('source', source)
                if 'startLine' in value and 'endLine' in value:
                    self.assertIn(source, snapshots)
                    self.assertLessEqual(1, value['startLine'])
                    self.assertLessEqual(value['startLine'], value['endLine'])
                    self.assertLessEqual(value['endLine'], snapshots[source]['lineCount'])
                for id in value.get('commonCaseIds', []):
                    self.assertIn(id, ids)
                for child in value.values():
                    walk(child, source)
        walk(LEDGER)

    def test_each_reserved_method_observation_in_a_fresh_process(self):
        observations = LEDGER['nativeMethodObservations']['records']
        self.assertEqual(len(observations), LEDGER['summary']['nativeMethodObservations'])
        for record in observations:
            expected = {key: value for key, value in record.items() if key != 'id'}
            with self.subTest(id=record['id']):
                result = subprocess.run(['bun', 'verification/routing-method-probe.ts', str(HONO),
                                         record['router'], record['input']['request']['method']],
                                        cwd=ROOT, env=ENV, text=True, capture_output=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), expected)
        print(f'Routing evidence: {len(observations)} isolated pinned method probes', flush=True)

    def test_pattern_cache_sharing_in_a_fresh_process(self):
        observation = LEDGER['nativePatternCacheObservation']
        result = subprocess.run(['bun', observation['probe'], str(HONO)],
                                cwd=ROOT, env=ENV, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), observation['record'])
        self.assertEqual(LEDGER['summary']['nativePatternCacheObservations'], 1)
        print('Routing evidence: mutable cached pattern/getter sharing reproduced', flush=True)


if __name__ == '__main__':
    unittest.main(argv=['routing-evidence-tests'])
