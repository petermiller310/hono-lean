#!/usr/bin/env python3
"""Semantic/report guards and a small live smoke run; no speed threshold."""
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import run as benchmark

CONFIG = json.loads((benchmark.ROOT / 'benchmarks/config.json').read_text())


class BenchmarkTests(unittest.TestCase):
    def setUp(self):
        self.config = dict(CONFIG, routes=16, queries=8, warmupSamples=1, samples=2,
            buildIterations=2, lookupIterations=8)
        self.work = benchmark.workloads(self.config)
        self.expected = benchmark.expected(self.work)

    def test_workloads_have_distinct_matching_shapes_and_runtime_variants(self):
        for w, oracle in zip(self.work, self.expected):
            self.assertEqual(len(w['banks']), 2)
            self.assertNotEqual(w['banks'][0], w['banks'][1])
            for bank in w['banks']:
                for route in bank['routes']: benchmark.comparison.validate_route(route)
            counts = [len(x) for x in oracle['observations'][0]]
            if w['name'] == 'shared-prefix':
                self.assertEqual(min(counts), 0); self.assertEqual(max(counts), 1)
            else: self.assertGreater(max(counts), 8)

    def test_semantic_preflight_rejects_wrong_labels_captures_order_and_duplicates(self):
        for fault in ['label', 'capture', 'order', 'duplicate']:
            with self.subTest(fault=fault):
                bad = deepcopy(self.expected)
                items = bad[1]['observations'][0][0]
                if fault == 'label': items[0]['handler'] = 'wrong'
                elif fault == 'capture': next(x for x in items if x['params'])['params'] = {}
                elif fault == 'order': items.reverse()
                else: items.pop()
                with self.assertRaisesRegex(ValueError, 'preflight'):
                    benchmark.validate_preflight(bad, self.expected, 'probe')

    def test_timing_guards_reject_bad_counts_clock_values_and_checksums(self):
        good = []
        for w in self.expected:
            banks = [[benchmark.digest(x) for x in bank] for bank in w['observations']]
            output = dict(name=w['name'])
            for phase, count in [('build', self.config['buildIterations']), ('lookup', self.config['lookupIterations'])]:
                output[phase] = []
                for i in range(self.config['samples']):
                    offset = self.config['warmupSamples'] + i
                    checksum = sum(banks[(offset+n) % 2][0] if phase == 'build' else banks[0][(offset+n) % len(banks[0])]
                        for n in range(count)) % 2**32
                    output[phase].append(dict(nanos=10, checksum=checksum))
            good.append(output)
        benchmark.validate_samples(good, self.expected, self.config)
        for fault in ['count', 'zero', 'type', 'checksum']:
            bad = deepcopy(good)
            if fault == 'count': bad[0]['build'].pop()
            elif fault == 'zero': bad[0]['build'][0]['nanos'] = 0
            elif fault == 'type': bad[0]['build'][0]['nanos'] = True
            else: bad[0]['lookup'][0]['checksum'] += 1
            with self.assertRaises(ValueError): benchmark.validate_samples(bad, self.expected, self.config)
        for key, value in [('routes', 0), ('samples', 1), ('lookupIterations', 0), ('seed', True)]:
            with self.assertRaises(ValueError): benchmark.validate_config(dict(self.config, **{key:value}))

    def test_live_smoke_and_wrong_source_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            report = Path(tmp) / 'report.json'
            command = [sys.executable, str(benchmark.ROOT/'benchmarks/run.py'), '--hono', str(HONO),
                '--smoke', '--report', str(report)]
            subprocess.run(command, check=True, text=True, capture_output=True)
            data = json.loads(report.read_text())
            self.assertEqual(data['honoRevision'], benchmark.comparison.BASELINE['revision'])
            self.assertEqual(data['config']['samples'], 2)
            self.assertEqual(set(data['measurements']), {'lean','hono'})
            report.unlink()
            command[command.index(str(HONO))] = str(benchmark.ROOT)
            failed = subprocess.run(command, text=True, capture_output=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn('pinned revision', failed.stderr)
            self.assertFalse(report.exists())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hono', type=Path, required=True)
    args, rest = parser.parse_known_args()
    HONO = benchmark.comparison.verify_checkout(args.hono)
    unittest.main(argv=[__file__, *rest])
