#!/usr/bin/env python3
"""Resolve this cluster's advertised names/kinds and enforce its axiom boundary."""
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
registry = json.loads((ROOT/'verification/proofs.json').read_text())
cluster = next(entry for entry in registry['slices'] if entry['id'] == 'url.getPattern.lexical-arrow-invocation.source-subset.v1')
theorems = cluster['contractTheorems'] + cluster['mechanismTheorems'] + [
    name for group in cluster['witnessGroups'] for name in group['checkedTheorems']]
definitions = cluster['mechanismDefinitions']
assert len(theorems + definitions) == len(set(theorems + definitions)), 'Duplicate registry name'
assert set(cluster['axiomAuditedTheorems']) <= set(theorems), 'Unknown audited theorem'
source = 'import HonoLean\nimport HonoLeanUpstream\nimport Lean.Meta.Basic\nimport Lean.Util.CollectAxioms\nimport Lean.Util.FoldConsts\nset_option maxRecDepth 8192\nopen Lean in\nrun_meta do\n  let environment ← getEnv\n'
for kind, names in [('thmInfo', theorems), ('defnInfo', definitions)]:
    for name in names:
        # Only identifier components enter generated Lean source.
        assert all(part.isidentifier() for part in name.split('.')), name
        source += f'  match environment.find? `{name} with\n  | some (.{kind} _) => pure ()\n  | _ => throwError "Missing or wrong kind: {name}"\n'
source += '  let some checked ← pure (environment.find? `HonoLean.Upstream.GetPatternInvocation.parses_setup) | throwError "Missing setup parse theorem"\n'
source += '  unless checked.type.getUsedConstants.contains `HonoLean.Upstream.GetPatternInvocation.pinnedSetup do\n    throwError "Wrong retained setup source"\n'
source += '  if checked.type.getUsedConstants.contains `HonoLean.Upstream.SourceSubset.pinnedSource then\n    throwError "Unexpected splitPath source"\n'
source += '  let some (.defnInfo setup) ← pure (environment.find? `HonoLean.Upstream.GetPatternInvocation.sourceSetup) | throwError "Missing executable source setup"\n'
source += '  unless setup.value.getUsedConstants.contains `HonoLean.Upstream.GetPatternInvocation.pinnedSetup do\n    throwError "Source setup lacks actual pinned setup"\n'
source += '  unless setup.value.getUsedConstants.contains `HonoLean.Upstream.LexicalArrow.initializeModule do\n    throwError "Source setup lacks lexical creation"\n'
for name in cluster['axiomAuditedTheorems']:
    source += f'\n#print axioms {name}\n'
    source += f'open Lean in\nrun_meta do\n  let dependencies ← Lean.collectAxioms `{name}\n  for dependency in dependencies do\n    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do\n      throwError "Unapproved axiom {{dependency}}"\n'
with tempfile.TemporaryDirectory(prefix='hono-getpattern-invocation-audit-') as directory:
    path = Path(directory)/'Audit.lean'
    path.write_text(source)
    subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, check=True)
print(f'Resolved {len(theorems)+len(definitions)} exact names: {len(theorems)} theorems/{len(definitions)} definitions; '
      f'{len(cluster["axiomAuditedTheorems"])} standard-only axiom audits.')
