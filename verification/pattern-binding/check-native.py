#!/usr/bin/env python3
"""Replay exact per-engine frontier records; this is not a conformance allowlist."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--hono', type=Path, required=True)
args = parser.parse_args()
expected = json.loads((ROOT/'verification/pattern-binding/native-evidence.json').read_text())
assert expected['formalBindingTheorem'] is None
node = os.environ.get('HONO_NODE') or shutil.which('node')
environment = dict(os.environ, ASDF_BUN_VERSION='1.4.0', GIT_OPTIONAL_LOCKS='0')
for index, record in enumerate(expected['records']):
    executable = 'bun' if record['runtime'] == 'bun' else node
    script = 'native-boundary.mjs' if index < 2 else 'elision-difference.mjs'
    result = subprocess.run([executable,'verification/pattern-binding/'+script,str(args.hono.resolve())],
                            cwd=ROOT,env=environment,text=True,capture_output=True,check=True)
    actual = json.loads(result.stdout)
    assert actual == record, (script,record['runtime'],actual,record)
print('Four exact native frontier records replayed; ENGINE-ELISION-1 preserved, no formal binding or baseline-allowlist claim.')
