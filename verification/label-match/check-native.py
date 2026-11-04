#!/usr/bin/env python3
"""Replay both exact ENGINE-FLAGS-1 records, without allowing the discrepancy away."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--hono',type=Path,required=True)
args=p.parse_args()
env=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0')
expected=json.loads((ROOT/'verification/label-match/native-evidence.json').read_text())
assert expected['id']=='ENGINE-FLAGS-1' and expected['verified']is False and expected['nativeOnly']is True
assert expected['baselineAllowlistChanged']is False and expected['formalNativeAdequacyTheorem']is None
assert [r['runtime']for r in expected['records']]==['bun','node']
for record in expected['records']:
    command='bun'if record['runtime']=='bun'else os.environ.get('HONO_NODE')or shutil.which('node')
    assert command,'Pinned Node is required'
    actual=subprocess.run([command,'verification/label-match/native-boundary.mjs',str(args.hono.resolve())],
                          cwd=ROOT,env=env,text=True,capture_output=True,timeout=60,check=True)
    assert json.loads(actual.stdout)==record,record['runtime']
print('Both exact ENGINE-FLAGS-1 native records reproduced; no native adequacy theorem or allowlist change.')
