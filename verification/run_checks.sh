#!/usr/bin/env bash
# Runs every upstream source-model check against a pinned Hono checkout.
set -euo pipefail
HONO="${1:-.hono-cache}"
cd "$(dirname "$0")/.."
npm ci --prefix verification --ignore-scripts --silent
node --test verification/tests/inventory.test.mjs
node verification/inventory.mjs --hono "$HONO" --check
python3 verification/splitpath/source.py --hono "$HONO"
python3 verification/splitpath/tests.py --hono "$HONO"
python3 verification/ecma2025/tests.py --hono "$HONO"
python3 verification/querystrings/tests.py --hono "$HONO"
python3 verification/nullobject/tests.py --hono "$HONO"
python3 verification/param-assignment/tests.py --hono "$HONO"
python3 verification/param-loop/tests.py --hono "$HONO"
python3 verification/key-set/tests.py --hono "$HONO"
python3 verification/handler-record/tests.py --hono "$HONO"
python3 verification/methods-push/tests.py --hono "$HONO"
python3 verification/search-entry/tests.py --hono "$HONO"
python3 verification/methods-loop/tests.py --hono "$HONO"
python3 verification/methods-loop-initial/tests.py --hono "$HONO"
python3 verification/registration-history/tests.py --hono "$HONO"
python3 verification/node-initialization/tests.py --hono "$HONO"
python3 verification/private-call/tests.py --hono "$HONO"
python3 verification/class-installation/tests.py --hono "$HONO"
python3 verification/private-write/tests.py --hono "$HONO"
python3 verification/literal-branch/tests.py --hono "$HONO"
python3 verification/iteration-setup/tests.py --hono "$HONO"
python3 verification/search-setup/tests.py --hono "$HONO"
python3 verification/loop-entry/tests.py --hono "$HONO"
python3 verification/first-literal/tests.py --hono "$HONO"
python3 verification/queue-advance/tests.py --hono "$HONO"
python3 verification/queue-schedule/tests.py --hono "$HONO"
python3 verification/component-count/tests.py --hono "$HONO"
python3 verification/child-enumeration/tests.py --hono "$HONO"
python3 verification/part-offsets/tests.py --hono "$HONO"
python3 verification/capture-guard/tests.py --hono "$HONO"
python3 verification/params-init/tests.py --hono "$HONO"
python3 verification/capture-collect/tests.py --hono "$HONO"
python3 verification/exec-call/tests.py --hono "$HONO"
python3 verification/builtin-exec/tests.py --hono "$HONO"
python3 verification/builtin-exec/audit.py
python3 verification/pattern-construct/tests.py --hono "$HONO"
python3 verification/pattern-construct/audit.py
python3 verification/pattern-binding/check-native.py --hono "$HONO"
python3 verification/pattern-binding/tests.py --hono "$HONO"
python3 verification/pattern-binding/audit.py
python3 verification/label-match/tests.py --hono "$HONO"
python3 verification/label-match/audit.py
python3 verification/getpattern-cache/check-native.py --hono "$HONO"
python3 verification/getpattern-cache/tests.py --hono "$HONO"
python3 verification/getpattern-cache/audit.py
python3 verification/getpattern-terminal-cache/tests.py --hono "$HONO"
python3 verification/getpattern-terminal-cache/audit.py
python3 verification/getpattern-body/tests.py --hono "$HONO"
python3 verification/getpattern-body/audit.py
python3 verification/getpattern-invocation/tests.py --hono "$HONO"
python3 verification/getpattern-invocation/audit.py
python3 verification/getpattern-lookahead/tests.py --hono "$HONO"
python3 verification/getpattern-lookahead/audit.py
bun verification/regex-exec/native-boundary.mjs "$HONO"
python3 verification/routing-tests.py --hono "$HONO"
bun verification/trust_probe.ts --hono "$HONO"
