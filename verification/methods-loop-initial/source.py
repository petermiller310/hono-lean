#!/usr/bin/env python3
"""Check the existing exact source artifacts used by the initial-layout composition."""
import argparse
import hashlib
import json
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parents[2]
REVISION = '5ca49b0720755c585c9a9835f0a479ceea36fb52'


def expected(checkout):
    for name in ['methods-push', 'search-entry', 'methods-loop', 'nullobject', 'key-set']:
        checker = runpy.run_path(str(ROOT/f'verification/{name}/source.py'))
        for path, data in checker['artifacts'](checkout).items():
            if not path.exists() or path.read_bytes() != data:
                raise ValueError(f'Stale or changed dependency: {path.relative_to(ROOT)}')
    push = json.loads((ROOT/'verification/methods-push/source.json').read_text())
    search = json.loads((ROOT/'verification/search-entry/source.json').read_text())
    loop = json.loads((ROOT/'verification/methods-loop/source.json').read_text())
    fragments = {}
    for name, metadata, source_copy in [
        ('registration', push['fragment'], 'verification/methods-push/source.ts.txt'),
        ('collector', search['fragments']['collector'], 'verification/search-entry/collector.ts.txt'),
        ('loop', loop, 'verification/methods-loop/loop.ts.txt')]:
        fragments[name] = dict(sourcePath='src/router/trie-router/node.ts', sourceCopy=source_copy,
            startByte=metadata['startByte'], endByteExclusive=metadata['endByteExclusive'],
            sha256=hashlib.sha256((ROOT/source_copy).read_bytes()).hexdigest())
    return dict(schemaVersion=1, revision=REVISION, sourcePath=loop['sourcePath'],
        sourceSha256=loop['sourceSha256'], fragments=fragments,
        dependencyChecks=['verification/methods-push/source.py', 'verification/search-entry/source.py', 'verification/methods-loop/source.py', 'verification/nullobject/source.py', 'verification/key-set/source.py'],
        claim='Initial structural layout derives prefix readiness for the existing parsed loop; registration, later collector and helper activation remain explicit separate stages.',
        sourceBoundary='These are three exact existing source fragments, not one lexical block. Class construction, module/helper linking, caller activation/arguments and intervening search effects remain open.',
        testsBoundary='Finite multi-registration and repeated-query composition evidence is separate from the scope of the universal initial-layout and registration bridge theorems.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hono', type=Path, required=True)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    data = (json.dumps(expected(args.hono), indent=2)+'\n').encode()
    destination = ROOT/'verification/methods-loop-initial/source.json'
    if args.write:
        destination.write_bytes(data)
    elif not destination.exists() or destination.read_bytes() != data:
        raise SystemExit('Stale or changed initial-loop composition metadata')
    print('Existing registration, later collector, full loop and Lean embeddings checked.')


if __name__ == '__main__':
    main()
