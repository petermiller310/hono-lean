# Sparse scheduling and consumer-bridge audit

This is a conditional source-subset result for pinned Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. It adds a real sparse producer and
relative consumer bridge, not complete regexp, for-in, loop or search coverage.

## Source identity and original operator

The producer is `src/router/trie-router/node.ts`177–178, bytes `[5546,5667)`,
length 121, SHA-256
`f81b14a2daf91271162188b3cb1061728c7dedfdc5581a73eae01caa51c0f198`.
The external checker verifies clean pin, working bytes versus Git, source copy,
metadata and Generated embedding. It also checks the existing consumer 209–210
span `[6428,6537)`,109 bytes, SHA-256
`c24807d3575aeca85813064c40bb8b44ca1287699c984e081847bb8ed45a3e8e`.

The only shared-parser change is maximal munch for adjacent `||=` before `||`.
Spaced `|| =` remains different syntax and rejects. Older entry points still
reject the logical assignment; no old Expr/Stmt/State/AssignmentReference ABI
changes. New `SparseInitializer.logicalOrAssign` retains the original operator.
The source parse equations consume the complete producer and consumer texts.
There is no synthetic body, generic TypeScript erasure or rewritten source
equivalence assumption.

## Authoritative sparse state and independent contracts

`IndexedArray` stores length and `Nat → Option Value` own slots. None is a hole;
Some undefined is an own data value. `WellFormedIndexed` excludes own indices
beyond length. New indexed set extends length and writes exactly the addressed
slot, preserving gaps. Push creates one own value at current length. Sparse
shift reuses the earlier indexed copy/delete steps; sparse concat preserves own
absence in its left/right ranges. These operations use no dense execution cache.

The selected normal domain supplies actual INITIAL queue/count/child bindings,
an allocated well-formed/legal queue, and a valid pushable array if its selected
slot is truthy. The index is primitive, nonnegative and below 2^32−1; the value
2^32−1 is a named property rather than an array index and remains outside this
specialization. Target append capacity and native length/resource restrictions
are explicit. No future target, successful operation or desired output is a
premise. Child values are copied opaquely; this fragment does not inspect their
private fields or prove their insertion/regexp origin.

Independent `OwnWrite`/`OwnAppend` and result contracts state exact selected
reference, own presence, length, copied child value, allocation and heap/env
frames. The truthy case skips RHS and Put; the falsy case derives fresh target
allocation before writing the saved queue/index, then pushes to that CURRENT
target. Existing-target=queue aliases retain the original selected own slot
while appending at the queue's old length. No blanket unchanged-queue-length
claim is made.

The generic saved-reference witness evaluates effectful base/index expressions
once, allows further RHS array effects, then still writes the originally saved
numeric reference. This is not a claim that arbitrary object-valued key
coercion is effect-free or necessarily happens once in every engine.

## Relative consumer bridge

`consumer_source_erases` executes actual sparse 209–210 in all admitted
falsy/array/scalar cases. Initial cells derive current post shift reads and
concat-length readiness, including queue/temp/head aliases. It relates the
read-value embedding to the previous parsed dense source theorem and contract.

`observe` maps holes to undefined only at the READ interface. The authoritative
sparse heap and ownership remain unchanged by observing it. A checked
counterexample distinguishes a hole from Some undefined, so the bridge cannot
be read as own-property equality. `embedIndexedState ambient` carries explicitly
supplied ordinary-object/private/function/Set/this fields; default erasure alone
is merely an observer and does not reconstruct a prior Node state.

`schedule_then_first_hole` begins BEFORE scheduling with an empty queue, positive
count, actual temp cell and first curNodes binding. It derives the sparse gap,
selected target and consumer readiness, then executes the actual consumer's
falsy first-hole branch. Generic consumer theorems separately cover other
normal arms. This specific universal composition is not arbitrary whole-loop
reachability; the intervening source control flow is still omitted explicitly.

## Native language boundaries and preserved observations

The [ECMA-2622025 property-reference operation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluate-property-access-with-expression-key)
retains a referenced-name value; [GetValue/PutValue](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-getvalue)
handle property-key conversion. The 2025 GetValue text updates the referenced
name after conversion. The new model specializes to primitive numeric indices;
it does not prove the general object-coercion/Reference Record algorithms.

Exact pinned 177–178 boundary probes with an object-valued componentCount observe
different behavior in Bun1.4.0 and Node22.22.2. With a converting key and accessor,
Bun logs key/Get/Put; Node logs key/Get/key/Put. A second probe returns 2 then 3
from coercion: Bun writes the index 2 setter while Node creates own index 3 and
changes array length. The [recorded outputs](../../verification/queue-schedule/boundary-results.json)
and [boundary reproducer](../../verification/queue-schedule/boundary.mjs) preserve
each runtime's exact events and resulting ownership/length. The suite checks
them independently.
No cross-runtime normalization, new Hono D2 claim or general engine-conformance
verdict follows. These inputs are outside the primitive numeric formal domain;
the existing exact D1 artifact and allowlist remain intact.

Native probes also cover own holes versus undefined, retained target reuse,
get-once/truthy-no-setter, falsy setter receiving the actual fresh target,
inherited numeric targets, highest array index versus named 2^32−1 and custom
push behavior. Getters/proxies, numeric prototypes, custom intrinsics/species,
general coercion and resource/partial-error/native adequacy remain open. The
count-producing code at source 176 and enclosing body must eventually establish suitable inputs.

## Executable evidence and gates

The native runner checks all 315 pinned source/package blobs and both source
artifacts. Both fragments are plain JavaScript, inserted verbatim into strict
dynamic wrappers without TypeScript erasure. Wrappers, fixture construction,
observers, JSON/extraction tooling and engines remain unverified evidence.
Counterfactual producer/consumer source overrides and wrapper hashes are explicit.

Model and native runners execute repeated producers and consumers in one heap,
recording every own slot after each call, reference identity, freshness, retained
targets and final graph. The model also compares each successful consumer's
read-value embedding with the old dense interpreter. The independent Python
oracle constructs own slots, lazy allocation/reuse, target append and pending
tail directly from fixture identities; expected answers never come from faulted
syntax or interpreter outputs. Failures compare rejection only, not rollback
or exact native exception/partial-state traces.

The corpus has 1,332 exhaustive and 370 seeded/repeated/long contexts, with six
supported producer faults, separate maximal-munch/authority/syntax controls,
four explicit model-only restrictions and 32 Node comparisons. The first full
run 54424 passed three groups but timed out after 300 seconds in the main model
batch. An isolated index512/three-scheduling case completed without consumption
in0.437 seconds, while one consumption exceeded the diagnostic20-second budget.
The repair adds a direct own-index formula with an unconditional equality proof
to the unchanged reference shiftSteps/copyForward calculation, including empty
and malformed beyond-length own maps. Sparse execution uses this equal endpoint;
no native implementation override or domain/case reduction is used. The same
isolated0/1/2/3-consumption cases now completed in0.428/0.383/0.423/0.395 seconds.
The unchanged 1,702-case suite passed 4 groups in9.331 seconds (89175, closed),
including the long case and all source-fault/boundary/identity controls.

The first integrated build passed 461 jobs (46916). Final corrected generic
replay passed 19 jobs (17386), and concrete source/bridge/examples replay
passed 28 jobs (64631, Examples1.9s). Final corrected integrated build passed 461 jobs (59493, closed). All 88
registered names resolve in the actual imported Lean environment as 80 theorems
and 8 definitions. The eight source/bridge/composition headlines and two equal
shift endpoint theorems use only `propext`, `Classical.choice` and `Quot.sound`.
Fresh root kernel replay 10611 completed successfully with exit 0 after that
final461-job managed build. Connected queue-advance4,437/loop-entry1,685 regressions, main 468
lookups/98appends with the same exact D1 discrepancy,13 inventory fixtures,
byte-identical inventory and routing evidence checks passed.

The generic gate passed 19 jobs (46350), with 14 public examples and four exact
standard-axiom guards. The source/consumer bridge gate passed 27 jobs (85668),
and the final concrete gate passed 28 jobs (48272, Examples2.2s), with 11 public
witnesses including two inhabited universal initial-domain applications.
All fixed obligations, old proof clusters, complete routing statuses and
historical benchmarks will be reconciled before commit. The full goal stays
active; no whole-Hono or native-language completion is claimed.

The final native scheduling/consuming wrapper SHA-256 values are
`db4cf04d5504c0e91728cdf72a85ef0169d9e93fb4d556711f8bf799f9d2c8cf`
and `47edfbb58b6eb2186c1039c6fbfd0add003e2f4d95676258663d90eab8c43424`.
These are unverified evidence wrappers, not proved emitted Hono artifacts.
Independent review has checked the source/contracts/proofs/witnesses/harness/
oracle/boundary record/diagram and unconditional optimization. All final gates and independent fixed-ledger bookkeeping/freeze reconciliation
are clean.
