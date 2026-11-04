# Retained plan: getPattern cache decisions and persistent identity

This is the retained plan from the label checkpoint. The
[cache walkthrough](getpattern-cache-walkthrough.md) and
[audit](getpattern-cache-audit.md) now record completed warm DATA/plain/miss/init
source-model claims and persistent collision histories. The universal cold
terminal branch, wildcard/function/module connection and reached lookahead stay
open; the [next plan](getpattern-terminal-cache-plan.md) states those obligations.
The original planned scope below remains useful for reviewing what is complete.

## Bind complete source control

At pin `5ca49b0720755c585c9a9835f0a479ceea36fb52`, src/utils/url.ts contains:

| Source | Bytes | SHA-256 |
| --- | --- | --- |
|50 cache object declaration|52, `[1127,1179)`|`aaf509b80f7785784036948ed957b7a94474fad18696c5e597b0175cef1016e9`|
|62–74 cache block|440, `[1461,1901)`|`6708db3236d21830f5b739727a68a100a8125297ee4deb25c5f4b3bcea77ab18`|
|60–77 post-wildcard body|533, `[1387,1920)`|`0ce62880eb018a718c7d3f32bb413e31bf5b8c42e31bba1e289d280529a47cf5`|

Prefer the complete440B block or533B body with its real nested conditions,
assignments and returns. Retain the actual 67 lookahead construction syntax
including its multiple template substitutions, even while execution of that
unproved cold branch remains an explicit refusal. Do not paste source headers
around fabricated empty bodies or rename leaf composition a whole-function proof.

## First coherent domain

Prove these paths from actual computed source 60 data:

- A warm truthy current DATA cache hit skips all cold construction readiness and
  returns the retained current value. It may be any truthy runtime Value; the
  erased Pattern annotation does not validate tuples.
- A cold plain parameter (`match[2]` is undefined) executes actual 70, allocating
  `[label, match[1], true]`, ordinary Set and actual 74's current return Get.
- Add cold terminal safe-range68 using the existing constructor connection when
  its real next/branch conditions can be derived. A reached cold lookahead 67 is
  still open until genuine lookahead semantics is implemented.
- If the complete533B body is retained, source 60's computed miss can execute the
  actual final null return. The earlier wildcard guard remains separately open
  unless its actual full source is included.

Execute actual 50's `{}` allocation and preserve the resulting cache object across
selected calls where practical. Module closure creation/import/bootstrap remains
an explicit source link until implemented. Do not reset or reconstruct the cache
between registration histories.

## Independent key, lookup and write contract

The key is raw UTF16 label + `#` + primitive ToString(next). No escaping occurs.
Undefined and the string `undefined` collide. So do plain labels `:a#b` with
next `c`, and `:a` with next `b#c`: both keys are `:a#b#c`. Both registration orders
must retain the FIRST tuple identity, label and name once a truthy DATA entry is
stored. Derive this from source execution and descriptor frames, not a supplied
first-wins map or lookup result.

Source 63 tests truthiness, not presence: existing0/false/empty-string/null/
undefined take the store branch; an empty array is truthy and returned unchanged.
Source 74 performs a SECOND current Get. Do not return a saved first-read value
or claim stable identity for arbitrary accessor effects. Native getters can
return different values between reads. Ordinary Set must use current writable/
setter/prototype/extensibility semantics, not CreateDataProperty or a hidden map.
State exact ordinary DATA/no-relevant-mutation assumptions for stable first-wins.

The source 50 typed index signature is grammar metadata. Retain/parse it if its
full declaration is included; do not hide a trusted TypeScript erasure step.
Unmodeled general coercion/getter/custom-setter/proxy effects must remain visible
rather than being reported as native errors or atomic rollback.

## Meaningful cases

Retain plain-label undefined/stringundefined and raw# collisions in BOTH orders,
current DATA truthy/falsy values, old shared aliases, nonwritable/nonextensible
cache boundaries, multiple current reads and source mutations. Keep the existing
regex terminal-versus-lookahead undefined/stringundefined native observations.

A useful further native probe: cold plain `:id` with next `{(}#undefined` stores
a true tuple at `:id#{(}#undefined`; label `:id#{(}` with next undefined then has
a valid label capture whose future regex body is invalid `(`, but the cache hit
returns the old tuple without constructing it. Reverse order reaches a cold
constructor error. Independent review and root replay now reproduce both orders
in separate fresh pinned Bun processes. The [script](../../verification/getpattern-cache/native-boundary.mjs),
[exact records](../../verification/getpattern-cache/native-evidence.json) and
[replay check](../../verification/getpattern-cache/check-native.py) retain the
evidence. TypeScript loading is unverified and the private key is a source-formula
expectation, not a native storage observation. This remains native-only with
no formal cache theorem, full-router claim or D1 compatibility allowance.

The entire fixed runtime catalog and native/frontend/realm/host adequacy remain
part of the active full-Hono goal.
