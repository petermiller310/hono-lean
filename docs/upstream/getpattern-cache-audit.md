# Cache control: checked claim and remaining boundary

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52` (4.13.13).
The [source metadata](../../verification/getpattern-cache/source.json) pins exact
533-byte source 60–77, its complete440-byte cache block 62–74, typed52-byte
initialization 50, and the key/guard/plain/return leaves. The real nested 67
lookahead and 68 terminal branches remain in the parsed syntax. The wildcard
guard 56–58, function entry, lexical closure and module bootstrap are outside
these spans. Source copying/hash/clean-checkout tools remain trusted tooling.

## Universal and closed claims

The [registry](../../verification/proofs.json) adds the conditional cluster
`url.getPattern.cache-control.source-subset.v1`. Its six headline theorems are:

| Theorem in `HonoLean.Upstream.PatternCache` | Claim |
| --- | --- |
| `source_block_warm_satisfies` | Exact block returns any initially truthy DATA value and preserves the entire state, with no match or constructor readiness |
| `source_warm_satisfies` | Full body derives actual captures, then returns the retained DATA value and frames old state |
| `source_miss_satisfies` | Independent label-language miss yields null without any next/cache/constructor inputs |
| `source_plain_satisfies` | Computed absent body yields a fresh plain tuple, strict ordinary store, second return Get and independent value/descriptor/frame contract |
| `source_init_satisfies` | Actual typed initialization allocates an empty ordinary Object.prototype-linked cache |
| `source_init_then_plain_satisfies` | Initial root descriptor facts derive readiness after actual initialization, then execution uses that same cache |

The normal next domain is arbitrary UTF16 strings or undefined. General object
coercion, custom accessors/proxies, broad constructor behavior and error-state
adequacy are open. Initial finite descriptor paths and writability conditions
are structural facts, not successful Get/Set or desired-result premises. Warm
values need not be tuples; neither writability nor extensibility is required
when the cold branch is skipped. Replacing an existing writable own DATA field
works on a non-extensible receiver; creating a new own field requires extension.

Eleven generic and seventeen concrete kernel witnesses cover inhabited arbitrary
normal domains, arbitrary plain names, malformed retained values, inherited
read-only/non-extensible warm hits, initial source 50, same-cache both-order raw#
and undefined/stringundefined histories, caller aliases and explicit frontiers.
They execute repeated calls on the entire carried heap, not reset cache fixtures.
The source 50 composition still hands off between selected source activations;
closure/module creation has not been proved.

Cold terminal 68 has a closed execution witness and 1,958 finite contexts including
all 1,953 ordered safe endpoint pairs. There is **no universal whole-cache cold
terminal theorem** here. Reached cold 67 retains its actual AST but explicitly
refuses in the model, beside a successful native control. A miss for this
post-wildcard body does not imply that full getPattern returns null for `*`.

## Executable evidence and observer limits

The new [tests](../../verification/getpattern-cache/tests.py) run nine groups.
There are 3,478 comparison contexts/histories:384 warm,48 exact-block warm,812 cold
descriptor cases,260 persistent histories,1,958 terminal,7 miss and 9 additional
primitive two-call histories. An independent Python raw-key/descriptor/history
oracle uses independent label decomposition. The model parses actual source;
native Bun1.4.0 and Node22.22.2 run the unwrapped actual533B or440B body in a
fixture closure with an explicit persistent cache. All 315 pinned blobs are
checked. Native main does not execute TypeScript's actual52B initializer.

Returned and cache-exposed references both enter the visible identity graph.
Six admitted source faults alter plain true/name/label, invert the cold guard,
store under the wrong key, or return match instead of the cache value. This
detects tuples exposed only through the wrong cache key. Hidden captures/literal
identities, physical IDs/counts and internal protocol records are model-only.
The Driver checks caller restoration before the explicit next-activation reset,
old allocated metadata and trace prefixes. Native observations have less access;
their transport/observer/realm/frontend/engine interpretation remains unproved.

Six [native controls](../../verification/getpattern-cache/control-evidence.json)
per engine retain second-Get changes, inherited get/set/get, an escaped tuple
before a throwing setter, mutation during next's primitive conversion, an array
cache and the legacy prototype setter. The array-RHS legacy setter succeeds
natively and changes the prototype; the old model refuses it. No TypeError is
invented for that case. DATA rejection checks compare failure and native
TypeError; an Except error is not a rollback or partial-error-state theorem.
Public RegExp.source display escapes `/`; raw constructor input does not.

The original three native preflight files remain byte unchanged and native-only.
Their formalCacheTheorem fields stay null. They are historical evidence distinct
from the new conditional source-model cluster, not a new D1 allowance.

## Reproducibility

Focused generic 50654 and combined 61711 gates passed40/56jobs respectively;
the root build passed697jobs with warnings as errors. The normal suite 92748
passed9groups in9.995s. Existing comparison 11687 retained467agreements, one exact
D1,98 appends and zero unexpected failures; label suite 70961 passed7groups.

Declaration audit 54205 completed exit0:155actual names,90theorems/65definitions
and25transitive standard-only targets, including all12in-file guard targets.
Fresh 38288 completed terminalexit 0 after the frozen697-job managed build. The
audit resolves actual Lean environment declaration kinds, checks duplicate
absence and collects transitive axioms. Only propext, Classical.choice and
Quot.sound are allowed; no custom axioms, sorry or native proof shortcut.

The prior34clusters/33additional slices, all30original assumption statuses and
theorem arrays, all36full-routing statuses, prior tracked Lean modules/shared
ABI, fixed SPEC/target/catalog/D1/comparison/benchmarks and historical engine
records remain preserved. There are no unconditional upstream runtime claims.

See the [walkthrough](getpattern-cache-walkthrough.md),
[editable diagram](../diagrams/getpattern-cache.excalidraw) and
[next plan](getpattern-terminal-cache-plan.md).
