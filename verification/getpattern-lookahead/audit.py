#!/usr/bin/env python3
"""Resolve every advertised declaration and check source links/axiom boundaries."""
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
registry = json.loads((ROOT/'verification/proofs.json').read_text())
cluster = next(entry for entry in registry['slices'] if entry['id'] ==
               'url.getPattern.literal-lookahead-constructor.source-subset.v1')
theorems = cluster['contractTheorems'] + cluster['mechanismTheorems'] + [
    name for group in cluster['witnessGroups'] for name in group['checkedTheorems']]
definitions = cluster['mechanismDefinitions']
assert len(theorems + definitions) == len(set(theorems + definitions)), 'Duplicate name'
assert set(cluster['axiomAuditedTheorems']) == set(theorems), 'Audit every theorem'

# These files use explicit top-level namespaces and mutual/section blocks.
# Keep anonymous block ends separate from namespace ends when extracting names.
actual = {'theorem': set(), 'def': set()}
for folder in ['ECMA2025/LiteralLookahead', 'SourceSubset/LookaheadRegExp', 'GetPatternLookahead']:
    for path in sorted((ROOT/'HonoLean/Upstream'/folder).glob('*.lean')):
        stack = []
        for line in path.read_text().splitlines():
            namespace = re.match(r'namespace (\S+)', line)
            if namespace:
                stack.append(('namespace', namespace[1]))
                continue
            if re.match(r'(mutual|section)(\s|$)', line):
                stack.append(('block', ''))
                continue
            if re.match(r'end(\s|$)', line):
                assert stack, (path, line)
                stack.pop()
                continue
            declaration = re.match(r'\s*(private )?(?:noncomputable )?(def|theorem) (\w+)', line)
            if declaration and not declaration[1]:
                actual[declaration[2]].add('.'.join(
                    [value for kind,value in stack if kind == 'namespace'] + [declaration[3]]))
        assert not stack, path
assert actual['theorem'] == set(theorems), 'Theorem registry differs from source'
assert actual['def'] == set(definitions), 'Definition registry differs from source'

source = '''import HonoLean
import HonoLeanUpstream
import Lean.Meta.Basic
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
set_option maxRecDepth 8192
open Lean in
run_meta do
  let environment ← getEnv
'''
for kind,names in [('thmInfo', theorems), ('defnInfo', definitions)]:
    for name in names:
        assert all(part.isidentifier() for part in name.split('.')), name
        source += f'  match environment.find? `{name} with\n  | some (.{kind} _) => pure ()\n  | _ => throwError "Missing or wrong kind: {name}"\n'
source += '''  let some parsed ← pure (environment.find? `HonoLean.Upstream.GetPatternLookahead.parses_source_body_nodes) | throwError "Missing source parse theorem"
  unless parsed.type.getUsedConstants.contains `HonoLean.Upstream.GetPatternLookahead.pinnedBody do
    throwError "Wrong retained body source"
  if parsed.type.getUsedConstants.contains `HonoLean.Upstream.SourceSubset.pinnedSource then
    throwError "Unexpected splitPath source"
  let some (.defnInfo nodes) ← pure (environment.find? `HonoLean.Upstream.GetPatternLookahead.parsedNodes) | throwError "Missing source projection"
  for expected in #[`HonoLean.Upstream.GetPatternLookahead.pinnedBody, `HonoLean.Upstream.SourceSubset.parsePatternCacheBody, `HonoLean.Upstream.GetPatternLookahead.selectNodes] do
    unless nodes.value.getUsedConstants.contains expected do
      throwError "Projection lacks {expected}"
  let some (.defnInfo runner) ← pure (environment.find? `HonoLean.Upstream.GetPatternLookahead.sourceSelectedTuple) | throwError "Missing selected runner"
  for expected in #[`HonoLean.Upstream.GetPatternLookahead.parsedNodes, `HonoLean.Upstream.SourceSubset.LookaheadRegExp.executeDeclaration, `HonoLean.Upstream.SourceSubset.LookaheadRegExp.evalExpr] do
    unless runner.value.getUsedConstants.contains expected do
      throwError "Runner lacks {expected}"
'''
for name in cluster['axiomAuditedTheorems']:
    source += f'\n#print axioms {name}\n'
    source += f'open Lean in\nrun_meta do\n  let dependencies ← Lean.collectAxioms `{name}\n  for dependency in dependencies do\n    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do\n      throwError "Unapproved axiom {{dependency}}"\n'
with tempfile.TemporaryDirectory(prefix='hono-lookahead-audit-') as directory:
    path = Path(directory)/'Audit.lean'
    path.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, check=True)
print(f'Resolved {len(theorems)+len(definitions)} actual names: '
      f'{len(theorems)} theorems/{len(definitions)} definitions; all theorems standard-only.')
