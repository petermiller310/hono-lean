# Queue-advance source and model audit

This is a conditional source-subset result for Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. It verifies a selected continuation,
not the complete preceding body, outer iteration, search or router.

## Exact artifact and parser entry

The artifact is `src/router/trie-router/node.ts`209–210, bytes `[6428,6537)`,
length 109, SHA-256
`c24807d3575aeca85813064c40bb8b44ca1287699c984e081847bb8ed45a3e8e`.
The containing file's Git blob is `580b859a912a8c2d10982d430de9357da241048a`.
The external checker verifies clean revision, actual working bytes against Git,
the source copy, all metadata bytes and the generated Lean source string.
Lean checks `parses_source` and the parsed source's model execution. External
Git/extraction/hash tooling is distinct from the checked parse equation.

`MutableSequence` reuses the shared raw lexer, expressions and real statement
boundaries. Complete consumption is required. The pinned text retains its
original `concat` AST and bare lexical assignment. The separate admission
adapter projects one-argument concat to the existing push admission rule only
to validate bindings/private syntax; the projected AST is never executed.
Visible lexical increments, unknown writes and wrong concat arity reject.
Older block/function/private-control admission entries are unchanged and their
continued rejection is checked by generic examples.

Only existing outer names supplied in the mutable allowlist can be rebound.
Fresh declarations are removed from that authority, including `let` declarations
in this deliberately conservative entry. The evaluator retains allowed outer
writes and local declarations; it does not blanket-restore the environment and
thereby lose `curNodes`. The saved first binding slot comes from before RHS
evaluation, and the write happens afterward. The source contract supplies an
existing mutable `curNodes` interpretation. Full lexical cells, TDZ, const,
imports, closures and module adequacy remain open.

## Independent contract and aliases

`Inputs` describes before-state queue/temp bindings and actual dense array cells,
plus the first existing `curNodes` lexical entry with arbitrary old Value. If
the queue head is an array, its initial cell must exist. No completed shift,
future heap/layout, copied result, desired final binding or helper success is
an input.

`Contents` distinguishes falsy reuse, array concat and nonarray append-one.
The copy contract independently specifies result length and each left/right
index. `Contract` additionally fixes the saved shifted local, exact first-entry
replacement with unrelated/shadowed bindings retained, queue tail, optional
fresh allocation and old-cell/nonarray frames.

`currentValues` is an identity case split: a reference equal to the queue sees
its tail; every other reference sees its initial cell. `cell_after_shift`
derives that law from the original heap lookups. Consequently queue=temp,
shifted=queue, shifted=temp and all-three aliases use post-shift contents.
An empty shifted array is truthy and allocates; falsy heads reuse temp without
allocation. Copying is shallow and preserves nested object/array identities.

The universal source theorem covers all three modeled outcomes under the
initial domain. Closed source-prepared examples execute earlier installation,
registration, reset/startup/headers and a first nonfinal literal branch, then
activate this separate selected continuation. Explicit pending-queue preparation
is a fixture input. These examples do not execute or establish reachability
through the omitted pattern body and remaining inner loop.

## Language and native interpretation

The [ECMA-2622025 concat algorithm](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.concat)
creates its result before inspecting item indices and consults species and
spreadability. Our dense endpoint appends the resulting list after effect-free
reads. The per-index model contract does not prove equivalence to the complete
ECMAScript abstract operations. Native interpretation requires fixed standard
lookup/species/spreadability, own dense data indices, valid native array lengths
and successful resources. Sparse holes, inherited indices, getters, proxies and
observable constructor/read/error effects remain separate obligations.

The [simple-assignment algorithm](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-assignment-operators-runtime-semantics-evaluation)
resolves a reference before evaluating its RHS and performs PutValue afterward.
Unresolved-reference failure must consequently follow RHS effects. The new
runtime correction preserves the saved optional slot and evaluates RHS before
rejecting a missing binding without insertion. Native const failures also
follow RHS effects, but const interpretation is outside this mutable entry.
Model errors do not expose partial exception states or native exception identity.

Source 177 can create a sparse outer `curNodesQueue` with an indexed assignment.
No claim here says every queue produced by that body is dense. A sparse model
or suitable refinement/producer invariant is required before full composition.
The earlier shift indexed-copy refinement remains its own dense specialization;
the new concat result is specified by independent index relations, without a
claim of a complete operational frontend/engine derivation.

## Executable evidence

The native runner verifies all 315 pinned source/package blobs and the selected
source artifact. The109-byte fragment is already JavaScript and is inserted
verbatim into a strict wrapper: no TypeScript erasure is applied to it. The
wrapper/input construction and engines are unverified evidence tooling. Its
baseline wrapper SHA-256 is
`0fc8622ac49de3c6aa53367273884d4e12a8436d683ea4153493d49473c3b591`.
Counterfactual source overrides are reported explicitly with distinct hashes.

The model Driver parses the same source and executes the generic mutable entry.
The independent Python oracle removes the pending head and constructs current
post-shift cells and shallow output directly from fixture identities. Neither
model/native output nor a faulted parser result supplies its expected answer.
Observers compare every array cell after every invocation, fresh/reused identity,
shifted/current values and retained results, including cycles. Separate lexical
canaries retain older shadowed `curNodes` values; model frames are also checked.

The final suite passed 4 groups in10.303 seconds:4,082 exhaustive and 355
seeded/alias/long/rejection contexts, totaling 4,437. Seven supported source
faults change shift, branch choice, concat receiver/order, reuse, mutation target
or concat argument. Separate parser controls reject authority/arity/visible
lexical-write/unsupported-syntax gaps. Three dangling-array cases are model-only
rejections, not claimed native fixtures. A32-case subset also runs on Node22.22.2.
Both Bun1.4.0 and Node run boundary probes for empty-array freshness, scalar
append, sparse pending/temp arrays, spreadability, species, shift failure effects
and unresolved/const assignment effects. Node comes from `HONO_NODE` or PATH.

## Replay and review

The final corrected generic gate passed 16 jobs (38578, closed), with allocated
positive fixtures and RHS-before-unresolved-error checks. The symbolic source
gate passed 19 jobs; the final concrete gate rebuilt 130 jobs (52413, closed),
including all seven witness theorems in5.4 seconds. Initial elaboration repairs
concerned explicit Bool/Int conversions and closed conjunction/Except pattern
normalization; no case, expected result or initial-domain premise was removed.

The integrated managed build passed 443 jobs (24961, closed). All 48 registered
names resolve in the actual imported Lean environment, classified as 45 theorems
and 3 definitions. All four public source cases and two RHS-order helpers depend
only on `propext`, `Classical.choice` and `Quot.sound`. Primitive-step regression
88498 passed 3 groups in 78.016 seconds (4,165 path, 1,080 separator/limit and
909 array cases). Fresh kernel replay 33999 completed successfully with exit 0
after that443-job managed build.

The connected first-literal suite passed 3,895 contexts again. Main comparison
retains 467 agreements and the same exact D1 discrepancy across 468 lookups/
98 appends. The 13 inventory fixtures, byte-identical inventory and routing
partial-evidence checks passed. No remote CI or new npm installation is claimed.

The [diagram](../diagrams/queue-advance.excalidraw) contains 9 semantic nodes and 9
bound arrows, with a committed PNG. Independent review checked the actual
source/contract/alias/domain, generic entry, witnesses, harness/oracle, diagram
and preservation of the fixed full-Hono obligations. Final independent
bookkeeping/freeze reconciliation is clean. Whole-runtime verification
and all 36 complete routing behavior units remain open.
