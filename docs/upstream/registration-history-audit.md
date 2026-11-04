# Registration histories: independent audit

Independent contract, proof and example review is complete. No unresolved defect
was found under the advertised source-subset, caller-context and native
interpretation boundaries. Whole-Hono verification remains open.

## Pinned source and checked composition

The target remains Hono commit
`5ca49b0720755c585c9a9835f0a479ceea36fb52`.
The source fragments used by this composition are:

| Fragment | Pinned source | Existing identity record |
| --- | --- | --- |
| Full private registration push | `src/router/trie-router/node.ts:55–61` | [private-push metadata](../../verification/methods-push/source.json) |
| Later fresh collector | `src/router/trie-router/node.ts:87` | [search-entry metadata](../../verification/search-entry/source.json) |
| Complete methods loop | `src/router/trie-router/node.ts:71–83` | [loop metadata](../../verification/methods-loop/source.json) |

The [composition identity checker](../../verification/methods-loop-initial/source.py)
was independently replayed successfully. It verifies registration,
search-entry, methods-loop, null-object helper and Set artifact/Lean-embedding
families, including actual working-file bytes against pinned Git blobs.
The upstream checkout was clean at review time.

The class declaration and containing functions remain provenance. The history
runner invokes the exact parsed registration-push expression repeatedly under
explicit caller activations. It is not a translation of complete `Node.insert`
calls, the path traversal selecting `curNode`, or the branch producing key
events. Search and helper activation/argument handoffs remain explicit too.

## History contract and constructive induction

The reviewed [contract](../../HonoLean/Upstream/RegistrationHistory/Contract.lean)
has two distinct parts. `runSourceHistory` executes a supplied expression;
the headline source theorem maps the actual pinned parser result into that
runner. `HistoryContract` independently describes appended object pairs, copied
key arrays, methods-row order, preserved tables and the carried score binding.
It does not define the result by evaluating the source runner.

`Seed` contains only the initial order binding, allocated root and owner,
lexical private-name/slot facts and current methods-array contents. `stage`
supplies a new caller method/handler context and a fresh supported Set cell.
Its keys are the independent first-occurrence contents of the supplied events.
It transports the current order binding; it does not install a desired next
score or manufactured method map/handler record.

The reviewed [facts](../../HonoLean/Upstream/RegistrationHistory/Facts.lean) derive
the full per-step `NodeMethodsPush.Inputs` and preserve `Seed` for the next step.
Induction in [correctness](../../HonoLean/Upstream/RegistrationHistory/Correctness.lean)
uses the earlier exact-source one-append theorem to construct the complete
finite history. No successful future registration,
per-prefix `Inputs`, completed storage or whole-history execution is an input.

For registration index `i`, the independent storage formulas place the outer
map at `initialObjectCount + 2*i`, the inner record at the next address, and
the copied key array at `initialArrayCount + i`. Score is the initial counter
plus `i + 1`. The proof checks these formulas, the ordered methods prefix,
all old object cells and every other preexisting array cell. The empty-history
case derives that setting the methods cell to its already recorded contents
leaves the heap unchanged.

The core theorem permits an initial dense methods prefix. The complete history
to loop-layout bridge currently starts from an empty methods array, so every
row passed to that bridge is source-created by the proved history. The program
uses one fixed supplied private owner/slot; histories distributed across path
nodes or interleaved with other framework effects remain separate work.

## Derived initial layout and full loop

The reviewed bridge modules are
[heap frames](../../HonoLean/Upstream/RegistrationHistoryLoop/Heap.lean),
[context and indexing facts](../../HonoLean/Upstream/RegistrationHistoryLoop/Facts.lean),
[layout construction](../../HonoLean/Upstream/RegistrationHistoryLoop/Layout.lean)
and [source composition](../../HonoLean/Upstream/RegistrationHistoryLoop/Correctness.lean).

`Context` contains old-only receiver/read/prototype facts, caller/helper/ALL
bindings, legal row/key counts and per-request inherited-query conditions.
Its reads refer to objects allocated before registration begins. Their closed
prototype chains cannot lead into the newly allocated handler records.

The bridge derives every final map, record, possible-key field, copied key
cell and collector separation from the history storage contract. It proves
the protected initial layout for all source-created rows, with unique keys
derived from the supplied event contents. No final `Layout`, selected-handler
binding, capture `Entry`, `NormalPrefixes` or successful loop premise is supplied.

The layout helper accepts an independent `HistoryContract` as a compositional
premise. The main `parsed_pipeline_satisfies` theorem constructs that contract
and exact history execution from `Seed`, executes the actual later collector,
and applies the initial-layout/full-loop theorem. Thus the headline pipeline
does not assume the completed history that it is meant to establish.

Per-request query conditions preserve the three relevant cases. An exact own
hit needs no unrelated prototype miss. ALL fallback requires the reached direct
lookup to miss at the root. A genuine miss accounts for both the query and ALL
lookups. Mere string inequality is not used to erase truthy inherited values.
For an empty history, the per-request query condition is vacuous.

The derived layout retains its sufficient restrictions: old read cells are
separate from mutable new handlers, all relevant prototype chains are closed,
params reset dispatch is absent or writable data, and the collector can hold
at most one append per row. The ALL binding is supplied even for direct hits;
the source evaluator still preserves the earlier lazy-OR behavior.

## Inhabited source witnesses

The [core example](../../HonoLean/Upstream/RegistrationHistory/Examples.lean)
`mixed_three_registration_history` applies the universal source theorem to
three registrations, including duplicate key events and equal supplied handler
values. Its independent observations check ordered row references, copied keys,
scores 8/9/10 and the carried counter.

Distinct registration calls construct distinct inner records even when their
opaque handler values are equal. This is different from a synthetic methods
array that repeats the same mutable handler-record reference. The general
initial-layout theorem admits such repeated references; ordinary source
registration allocates a fresh record for each append.

The [loop example](../../HonoLean/Upstream/RegistrationHistoryLoop/Examples.lean)
proves `mixed_history_initial_layout` and `mixed_history_pipeline` for GET,
POST and ALL registrations under a GET query. It establishes the initial
`Context` directly and applies the universal pipeline, rather than merely
evaluating an example or assuming the final layout.

GET gives an own direct hit, POST is a genuine miss, and ALL supplies a fallback.
Different key orders exercise two captures: the optional first id is retained
for the direct handler, zero remains a non-nullish node value, and the ALL
handler's later id uses the node value. A separate closed observation checks
collector references `[5, 9]`, captures and the final object count. No binding
chooses either source-created handler in advance.

## Native and finite evidence

The new [history tests](../../verification/registration-history/tests.py) reuse the
exact-source [native runner](../../verification/methods-loop-initial/native.ts)
and [Lean driver](../../verification/methods-loop-initial/Driver.lean). Their new
prefix observations check each push result, stored length, old rows/records/
key arrays, fresh identities, copied order, supplied handler value and score.
Native descriptor/value observations and model heap projections are bounded
evidence, not a universal native-heap refinement proof.

The complete new suite was independently replayed: four groups passed, covering
1,365 exhaustive prefix histories and 260 generated/long/empty histories,
including equal supplied handlers, negative/positive safe starting counters,
UTF-16 keys, repeated queries, three supported registration-source faults and
the native boundary observations below. This finite corpus remains separate
from the universal conditional history and layout theorems.

The final guarded native scope probes were independently replayed with Bun
1.4.0, the fixed revision and all 315 pinned source/package blobs. Wrapper
input/emitted hashes for that replay were
`f686317825d431de5ad6be7be21ac20239eef7d0283e8b58f36b83c8d6be5012`
and `f05d436ed090afc25ec169e979d5062f8edf6eee7f51be035fecc8a4a6b3f5ac`.
Transpilation is explicitly unverified.

The replay preserved the following boundaries:

- Starting the supplied counter at `2^53 - 1` produced two equal native scores
  `2^53`; the mathematical integer sequence is not a full IEEE-754 model.
- A custom supplied Set iterator changed an earlier record's score during the
  second registration. Old-cell framing therefore requires the supported
  standard iterator interpretation, rather than arbitrary native callbacks.
- An ALL registration queried by inherited `constructor`, `toString` or
  `__proto__` failed after one collector append. An inherited params setter ran
  once and discarded the fresh output; the subsequent key write failed after
  one append. These remain outside the normal protected/resettable domain.
- An actual exported Node using the same supplied function for GET/ALL/POST
  returned two GET results with the same function but distinct params objects.
  A later search allocated fresh params while earlier returned result pairs
  retained their old ids. Final result-pair mapping remains outside the current
  universal helper-body proof.

`NativeHistoryBounds` records arithmetic and size restrictions for interpreting
the model. It does not prove native realm/iterator/array/resource adequacy,
class installation or persistent mutable module-cell linking. The scope probes
are bounded counterexample/observation evidence, not whole-Hono defect theorems
or new comparator exceptions.

## Final checks and remaining scope

Independent review covered all nine new Lean modules. The source-facing
headline axiom guards list only `propext`, `Classical.choice` and `Quot.sound`.
Shortcut/debug scans found no unfinished proofs, custom axioms, native proof
shortcuts or debug commands in these modules. Source identity checks and the
independent native replay passed.

The parent confirmed the complete root build passed all 251 jobs and
`lake env leanchecker --fresh HonoLean` completed successfully. Parent replays
of the new 1,625-history suite and preceding 1,040-history suite also passed.
The pinned main comparison retained 468 lookups, the same exact D1 difference
and zero unexpected failures; routing checks and byte-identical structural
inventory regeneration passed as well. No proof source changed after final
review, build and fresh replay.

Remaining obligations include actual insertion traversal and Set event
production, class/private installation, source-level call/module/helper
linking, shared mutable order cells, native Number/heap/array/exception adequacy,
search traversal and temporary captures, final sorting/result mapping and the
rest of Hono's fixed published runtime catalog. No complete-router/package
coverage claim follows from this conditional history composition.
