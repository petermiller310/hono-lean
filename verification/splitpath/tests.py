#!/usr/bin/env python3
"""Check source freshness, subset hardening, UTF-16 native agreement and faults."""
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
PIN = '5ca49b0720755c585c9a9835f0a479ceea36fb52'
DEFAULT = 4294967295
parser = argparse.ArgumentParser()
parser.add_argument('--hono', type=Path, required=True)
args = parser.parse_args()
HONO = args.hono.resolve()
ENV = dict(os.environ, ASDF_BUN_VERSION='1.4.0')

def invoke(command, *, document=None, cwd=ROOT):
    return subprocess.run(command, input=None if document is None else json.dumps(document),
                          cwd=cwd, env=ENV, text=True, capture_output=True)

def model(inputs, limit=DEFAULT, source=None):
    doc = dict(inputs=inputs, limit=limit)
    if source is not None:
        doc['source'] = source
    result = invoke(['lake', 'env', 'lean', '--run', 'verification/splitpath/Driver.lean'], document=doc)
    if result.returncode:
        raise AssertionError(result.stdout + result.stderr)
    return json.loads(result.stdout)['results']

def expected(units, limit):
    fields = [[]]
    for unit in units:
        if unit == 47:
            fields.append([])
        else:
            fields[-1].append(unit)
    fields = fields[:limit]
    if fields and fields[0] == []:
        fields.pop(0)
    return fields

class SourceTests(unittest.TestCase):
    def test_exact_source_and_generated_artifacts(self):
        result = invoke(['python3', 'verification/splitpath/source.py', '--hono', str(HONO)])
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        with tempfile.TemporaryDirectory(prefix='hono-source-artifacts-') as temporary:
            base = Path(temporary)
            script = base/'verification/splitpath/source.py'
            script.parent.mkdir(parents=True)
            shutil.copy(ROOT/'verification/splitpath/source.py', script)
            command = ['python3', str(script), '--hono', str(HONO)]
            self.assertEqual(invoke(command+['--write']).returncode, 0)
            self.assertEqual(invoke(command).returncode, 0)
            for relative in ['verification/splitpath/splitPath.ts.txt',
                             'verification/splitpath/source.json',
                             'HonoLean/Upstream/SourceSubset/Generated.lean']:
                file = base/relative
                original = file.read_bytes()
                file.write_bytes(original+b'\n')
                self.assertNotEqual(invoke(command).returncode, 0, relative)
                file.write_bytes(original)

    def test_wrong_and_dirty_pin_reject_without_touching_original(self):
        with tempfile.TemporaryDirectory(prefix='hono-source-pin-') as temporary:
            clone = Path(temporary)/'checkout'
            subprocess.run(['git','clone','--shared','--quiet',str(HONO),str(clone)], check=True)
            command = ['python3','verification/splitpath/source.py','--hono',str(clone)]
            self.assertEqual(invoke(command).returncode, 0)
            subprocess.run(['git','-C',str(clone),'checkout','--quiet','HEAD^'],check=True)
            self.assertNotEqual(invoke(command).returncode, 0)
            subprocess.run(['git','-C',str(clone),'checkout','--quiet',PIN],check=True)
            (clone/'src/utils/url.ts').write_bytes((clone/'src/utils/url.ts').read_bytes()+b'\n')
            self.assertNotEqual(invoke(command).returncode, 0)
            subprocess.run(['git','-C',str(clone),'restore','src/utils/url.ts'],check=True)
            subprocess.run(['git','-C',str(clone),'update-index','--assume-unchanged','src/utils/url.ts'],check=True)
            (clone/'src/utils/url.ts').write_bytes((clone/'src/utils/url.ts').read_bytes()+b'\n')
            self.assertEqual(subprocess.check_output(['git','-C',str(clone),'status','--porcelain']).strip(),b'')
            self.assertNotEqual(invoke(command).returncode, 0)
            subprocess.run(['git','-C',str(clone),'update-index','--no-assume-unchanged','src/utils/url.ts'],check=True)
            subprocess.run(['git','-C',str(clone),'restore','src/utils/url.ts'],check=True)
            (clone/'untracked-source-audit.txt').write_text('audit')
            self.assertNotEqual(invoke(command).returncode, 0)

    def test_utf16_native_upstream_and_independent_oracle(self):
        cases = [list(xs) for n in range(6) for xs in itertools.product([47,97,0,55296,56320],repeat=n)]
        rng = random.Random(1729)
        alphabet = [0,47,45,97,233,0xD800,0xDC00,0xD834,0xDD1E,0xFF0F,65535]
        cases += [[rng.choice(alphabet) for _ in range(rng.randrange(65))] for _ in range(256)]
        cases += [[0xD834,0xDD1E,47,0xDC00], [0xDC00,47,0xD800], [47]*1024]
        native = invoke(['bun','verification/splitpath/hono_runner.ts',str(HONO/'src/utils/url.ts')],
                        document=dict(inputs=cases,limit=DEFAULT))
        self.assertEqual(native.returncode,0,native.stderr)
        observed=json.loads(native.stdout)
        self.assertEqual(observed['runtime'],'1.4.0')
        reference=[expected(case,DEFAULT) for case in cases]
        self.assertEqual(observed['results'],reference)
        self.assertEqual(model(cases),reference)
        print(f'UTF-16 default-limit audit: {len(cases)} actual-source/model/oracle cases',flush=True)
        for limit in [0,1,2,3,4]:
            sample=cases[:160]+[[47,97,47,98],[97,47,47,98]]
            native=invoke(['bun','verification/splitpath/hono_runner.ts',str(HONO/'src/utils/url.ts')],
                          document=dict(inputs=sample,limit=limit))
            self.assertEqual(native.returncode,0,native.stderr)
            reference=[expected(case,limit) for case in sample]
            self.assertEqual(json.loads(native.stdout)['results'],reference)
            self.assertEqual(model(sample,limit),reference)

    def test_real_source_body_faults_are_parsed_and_change_semantics(self):
        source=(ROOT/'verification/splitpath/splitPath.ts.txt').read_text()
        variants=[source.replace('    paths.shift()',''),
                  source.replace('paths[0]','paths[1]'),
                  source.replace("path.split('/')","path.split('-')")]
        for changed in variants:
            self.assertNotEqual(changed,source)
            self.assertNotEqual(model([[47,97]],source=changed),[expected([47,97],DEFAULT)])
        alias="export const f = (path: string): string[] => {\n const paths = path.split('/')\n const alias = paths\n alias.shift()\n return paths\n}"
        self.assertEqual(model([[97,47,98]],source=alias),[[[98]]])

if __name__ == '__main__':
    unittest.main(argv=['splitpath-tests'])
