#!/usr/bin/env python3
"""Replay both native-only cache observations in independent fresh Bun processes."""
import argparse
import json
import os
from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parents[2]
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--hono',type=Path,required=True);args=p.parse_args()
evidence=json.loads((ROOT/'verification/getpattern-cache/native-evidence.json').read_text())
assert evidence['verified']is False and evidence['plannedFrontier']is True and evidence['formalCacheTheorem']is None
assert evidence['baselineAllowlistChanged']is False
assert [r['order']for r in evidence['records']]==['plain-first','invalid-first']
for record in evidence['records']:
 result=subprocess.run(['bun','verification/getpattern-cache/native-boundary.mjs',str(args.hono.resolve()),record['order']],cwd=ROOT,
    env=dict(os.environ,ASDF_BUN_VERSION='1.4.0',GIT_OPTIONAL_LOCKS='0'),capture_output=True,text=True,check=True,timeout=60)
 assert json.loads(result.stdout)==record
print('Both fresh-process native cache records reproduced; formal cache/TS-loading theorem remains open.')
