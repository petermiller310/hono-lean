# Initial-state readiness for the stored-method loop: independent audit

This checkpoint strengthens the conditional proof for pinned Hono's
[`Node.#pushHandlerSets` loop, lines 71–83](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L71).
The selected source remains unchanged at revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, with fragment SHA-256
`9c2ace978dfc44df5b7046c74c808861a495d0e5f360b43762a08163340a5e19`.
The existing [source identity record](../../verification/methods-loop/source.json)
and [loop audit](methods-loop-audit.md) retain their scope.

## Obligation under review

The earlier loop theorem assumes `NormalPrefixes`: current selection reads and
capture-entry conditions hold at every independently specified reachable prefix.
That is a trajectory-wide condition. Moving it into a field named “initial
layout” would not discharge it.

The new argument must instead start from facts about one initial state, prove
which cells the capture operation can change, preserve the facts needed for
later selections and captures, and derive `NormalPrefixes`. The final source
theorem may then use that derived fact. A successful future evaluator call,
completed output, desired selected handler or prefix-wide readiness condition
must not appear as an input to the new initial layout.

## Review criteria

- Row maps, node/optional-parameter receivers and every prototype cell consulted
  by their reads must be protected from all mutable handler records, not merely
  the currently selected record. Their references must be inside the initial
  object heap, below later allocation identities.
- Handler reset must distinguish an absent own `params` field from safe ordinary
  dispatch. An inherited setter or nonwritable descriptor can prevent the desired
  write. Existing own fields must satisfy the flags required by the capture
  theorem; repeated resets must preserve their permitted shape.
- Key arrays must keep their unique primitive-string contents and be distinct
  from the collector. The methods array must also be distinct from the collector.
  Capacity must cover the initial collector plus every possible row capture.
- Object/prototype closure and stable read witnesses must survive handler-field
  replacement and fresh null-prototype output allocation. A returned reference
  can alias a handler without changing that reference value; this does not imply
  that the referenced object's other fields are immutable.
- A falsy chosen operand skips capture. An undefined/null row, a throwing lookup
  or an unsupported truthy value does not become valid merely because the source
  has an `if` guard or a TypeScript assertion.
- Repeated handler references must remain repeated collector references. Later
  resets replace the one shared handler's current params rather than preserving
  independent collector snapshots.
- A registration bridge must derive source-created outer maps, inner records,
  key snapshots and later-collector separation from executed source contracts.
  Actual class initialization, helper/caller activation, module binding identity,
  argument transport and search traversal may remain explicit separate gaps.

## Initial contract inspection

The new [initial layout](../../HonoLean/Upstream/MethodsLoopInitial/Contract.lean)
contains only facts about the origin state: bindings, allocated cells, initial
property reads, handler/key records, protected prototype closure and a collector
capacity bound. It has no `Processed`, `Ready`, `NormalPrefixes`, later `Entry`
or source-execution-success field. Initial selection facts use the independent
ordinary-read/branch relation, rather than source evaluator execution.

Its protected references are below the initial heap length and distinct from
every mutable handler reference. Rows, node params, object-valued optional params
and their prototype chains are protected. Record prototypes also enter this
protected graph. This is a declared restriction: the earlier generic loop can
admit additional aliases when its stronger prefix-wide domain happens to hold.

The layout supplies the actual ALL-valued binding unconditionally, even when a
direct hit would skip fallback. This is a stronger static domain than the earlier
lazy selection theorem, not a claim that the skipped source operand is evaluated.
Module import identity remains an explicit boundary.

The [registration facts](../../HonoLean/Upstream/MethodsLoopRegistration/Facts.lean)
construct the actual singleton private-push source execution and the actual later
collector declaration execution. Stored map/handler/key cells, empty collector
and ordinary loop inputs follow from those source endpoints. They do not stage
an `m` or `handlerSet` result. The computed endpoint definitions are accompanied
by source-existence equations; those definitions alone are not substituted for
the source connection.

## Preservation and readiness

The [preservation proof](../../HonoLean/Upstream/MethodsLoopInitial/Invariant.lean)
has been inspected. It frames protected property chains and specialized getter
receivers, maps current choices back to admitted initial records, frames key
arrays/functions, preserves global prototype closure, and updates every record
descriptor sharing the selected reference. No uniqueness restriction on handler
references is introduced. Captured output objects have null prototypes and fresh
identities above the old heap bound.

The [readiness proof](../../HonoLean/Upstream/MethodsLoopInitial/Correctness.lean)
has also been inspected. An unchanged handler reuses the initial safe reset
dispatch through protected parents; a changed handler has its own writable,
enumerable, configurable params data. Initial reads transfer to the current
post-reset/push state through the protected frame. The strict pre-append capacity
bound follows from `selected.length ≤ count < rows.length` and the initial
collector-plus-row bound. `layout_normalPrefixes` derives the earlier domain;
it is not a layout field. `parsed_initial_satisfies` then constructs the existing
full-loop source execution and independent trace.

The source [layout bridge](../../HonoLean/Upstream/MethodsLoopRegistration/Layout.lean)
has been inspected. It derives the actual singleton row, record and key array,
ordinary prototype-zero shapes, unique keys from the supplied Set trace contract,
and empty later collector. Its query domain distinguishes exact own hits, own
ALL fallback with an explicit inherited query miss, and genuine misses with both
query and ALL inherited misses. Inequality of method names alone is never used
as an inherited-property absence argument.

## Inhabited initial domains

The [initial examples](../../HonoLean/Upstream/MethodsLoopInitial/Examples.lean)
prove `fixture_layout` for any row-reference sequence drawn from a miss map,
an exact GET map and an own-ALL fallback map, with arbitrary repetition and an
arbitrary initial collector prefix satisfying capacity. Every hit may select the
same ordinary prototype-zero handler with two keys. Optional params and node
params are separate allocated objects with explicit initial reads.

`arbitrary_mixed_initial_satisfies` applies the source theorem to this parametric
layout. It neither evaluates the whole source as its proof nor assumes a
prefix-wide validity predicate. Its row count is arbitrary within the declared
Array capacity bound. This establishes an inhabited multirow/multikey/alias
family for the new static-domain theorem, rather than a small closed execution
standing in for a general invariant argument.

## Actual registration pipeline

The [combined theorem](../../HonoLean/Upstream/MethodsLoopRegistration/Correctness.lean),
`parsed_pipeline_satisfies`, includes three conclusions: execution of the actual
registration push from its input facts, execution of the actual later collector
declaration, and existence of full source-loop execution satisfying its
independent contract. Registration success is constructed, rather than supplied
as a premise. The derived initial layout supplies the loop's readiness argument.

The [source witness](../../HonoLean/Upstream/MethodsLoopRegistration/Examples.lean)
proves `actual_all_two_key_layout` and `created_all_two_key_pipeline`. It includes
actual Set creation, duplicate caller-supplied add events, the actual private
registration call, later source allocation and the full parsed loop. A GET query
misses the source-created map's own ALL key and reaches its ALL handler through
the proved fallback reads. The two-key capture retains a truthy optional first
id and preserves the node's numeric zero for the second key. Separate stale
`m`, `handlerSet`, `i` and `len` caller bindings do not select the result.

The generic source-storage bridge currently covers one registration into an
empty methods array, with arbitrary admitted unique keys and old context. The
static invariant covers general multirow layouts. These are different scopes:
the checkpoint does not prove that an arbitrary actual insertion history
constructs the full multirow layout.

The supplied Set events remain supplied events. The real insertion path and
`getPattern` branches that produce them are not established by the trace
scaffolding. Likewise, the explicit search/helper activation handoff is not a
proof of native calls, argument transport or intervening search mutations.

## Checks and remaining boundaries

Independent source identity replays passed for `methods-loop`, `methods-push`
and `search-entry`. They checked the selected source copies and Lean embeddings
against the same clean pinned checkout. The upstream working tree remained
clean. A scan of both new Lean module families found no unfinished proofs,
custom axiom declarations, native proof shortcuts, unsafe replacements or
leftover `trace_state` diagnostics.

The implementation agents reported clean focused builds of the initial and
registration example roots. The parent confirmed a complete root build of 233
jobs and successful fresh root kernel replay, recorded in
the project progress log at the time. Independent contract inspection
and external identity checks are not substitutes for those commands or for a
native language-adequacy argument.

The [new harness](../../verification/methods-loop-initial/tests.py) compares actual
registration pushes, later collectors and the full loop with a Lean driver and
an independent selection/capture oracle. The parent reported five passing groups:
781 exhaustive and 259 generated/long contexts, seven semantic faults, a type-name
control, dependency-artifact freshness and hidden edits in node/router/helper
sources. Its guarded dependency checker covers registration, search entry, the
full loop, null-object helper and Set-source artifacts. Finite multi-registration
and repeated-query tests do not enlarge the singleton universal source bridge
into an arbitrary-history theorem.

The model harness supplies compact Set cells from the independent event-trace
representation; the native wrapper supplies native Sets. This does not establish
the source path that produced those events. The named formal pipeline witness
separately includes checked Set creation/add operations under supplied events.

Independent replay of the durable native scope probes checked Bun 1.4.0, all
315 pinned blobs and wrapper/emitted hashes. Requests for inherited constructor,
toString and prototype values each failed after one append. A prototype params
setter was called once and the subsequent capture failed after append. These
preserved partial-mutation observations justify keeping lookup/root-dispatch
conditions visible; they are not universal exception-state proofs or new
comparison allowlist entries.

This checkpoint changes the proof's input boundary: it derives future readiness
from declared initial structure. It does not prove the entire JavaScript heap
model, frontend, type erasure, native property/array/realm interpretation,
resource sufficiency, mutable lexical/module cells or exception-state traces.
Protected pure reads remain a restriction; arbitrary effectful getters, proxies,
handler-as-prototype relationships and node/params aliases with mutable handlers
are not silently included. Raw list representations are not thereby proved to
be legal native heaps in every case.

Actual class/private initialization, module import identity, helper/caller
reachability, intervening frames, general source-produced registration histories,
temporary captures, path traversal and final result construction remain open.
The earlier restricted contract, D1 reproducer/allowlist, generated whole-runtime
coverage denominator and historical timings are not changed by this argument.

Final independent review found no unresolved defect in the stated initial-domain
preservation and source-pipeline claims. This is a conditional source/model
result, not whole-Node, whole-router or whole-Hono completion.
