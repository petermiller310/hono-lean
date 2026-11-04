# Methods-array loop: independent audit

## Exact source boundary

The selected source is the complete counted loop at
[`node.ts:71–83`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L71),
including the lazy method/ALL selection, `if (handlerSet)`, reset/append and
nested key loop. Its 556 bytes occupy `[1870, 2426)` in the pinned file and have
SHA-256 `9c2ace978dfc44df5b7046c74c808861a495d0e5f360b43762a08163340a5e19`.

The [source record](../../verification/methods-loop/source.json) also stores the
whole-file hash and Git blob, and the containing private method at lines 64–84
as provenance. The [identity checker](../../verification/methods-loop/source.py)
requires the exact revision, clean checkout and direct working-byte equality
with the pinned Git blob. It checks the committed text and Lean embedding;
Git status alone would miss assume-unchanged or skip-worktree edits. The
`--write` mode refreshes source/metadata only; it does not overwrite another
agent's Lean source.

Class initialization, installation of the lexical private name/brand, the
method's parameter declarations and actual callers are outside these selected
bytes. A proof of the body under its entry context does not establish those
connections or the path traversal that chooses a node.

## Control-flow and alias obligations

The source snapshots `node.#methods.length` once before iterating. It loads a
row on every outer iteration and performs ordinary inherited reads for method
selection. The existing `Choice` relation correctly returns an operand rather
than a Boolean and requires fallback-read success only on its reached branch.
The new guard tests the selected operand's truthiness separately. Falsy
selection must skip allocation, reset, append and every capture-key read.
A missing or null row is different: `m[method]` is evaluated before that guard
and can throw. A dense-object-row domain must remain an explicit restriction.

The inner and outer loops both name their variables `i` and `len`. The inner
loop must restore the outer counter/length, and key-index-zero precedence must
restart for each selected handler. The shared value-environment model restores
saved environments on loop exit and iteration completion. This particular
source changes these scoped counters and heap fields, but does not justify
the model's general behavior for mutable captured variables, module cells or
const assignment. Those adequacy obligations remain open.

Collector elements are references. Two rows can select the same handler
object. Each reached body creates a fresh params object and assigns it to that
same handler; both earlier and later collector references then expose the
last params object. A contract that silently snapshots each collector element's
params or requires all selected references distinct would miss this behavior.

Collector/methods-array aliasing can change the methods array during the loop.
Effectful getters can append or remove rows after the length snapshot. Likewise,
aliasing a row with a selected handler can make a params reset change later
method reads. A stable dense-array domain must state its actual separation and
read/frame restrictions, or its contract must account for these effects. A
TypeScript assertion supplies none of these facts.

## Independent native observations

An independent probe verified Bun 1.4.0, the fixed revision and all 315 source and
package blobs, then transpiled the exact selected source inside a supplied
private-class wrapper. Its wrapper SHA-256 was
`e603ba225b2fef8d59f76537f9c37e0b775f332c100f9df406310669b38c8a38`
and emitted JavaScript SHA-256 was
`08ee7af671384dafa12d4b32c60a830cca3ae9b9527bcc48e3b8e20c2369bba7`.
This is finite execution evidence; Bun TypeScript transpilation is unverified.

The probe checked these observations:

- Two rows selecting the same record append that same reference twice, allocate
  two distinct params objects, and leave both references pointing to the second.
- A first-row getter appends another row, increasing methods length from one to
  two. The saved length processes only the original row.
- A collector identical to the methods array grows from one to two entries;
  the appended handler is not visited beyond the original snapshot length.
- A first-row getter truncates an initially two-row methods array to zero.
  The next row access throws a native TypeError after the first handler has
  already been appended. Normal-completion proofs do not establish this
  partial-failure trace.
- A two-key record followed by a one-key record both execute. The second record
  uses key-index-zero precedence again, confirming nested counter shadowing.
- Undefined, null, false, zero and empty-string selections with no truthy ALL
  fallback skip a deliberately throwing allocation helper entirely.

These are supplied private-class contexts, not full router traces. Arbitrary
native getters, array exotic setters, proxies, exceptions carrying partial
states, class construction and host/native adequacy remain separate obligations.

The durable [native harness](../../verification/methods-loop/native.ts) was also
independently replayed with its pin/all-blob checks. It preserved saved-length
append behavior, a changed future row, truncation after one append, a truthy
numeric selection's failure and collector/methods aliasing. Its actual exported
Node smoke check observed stored GET/ALL/POST/second-GET registration order:
GET selects GET, ALL, second-GET; POST selects ALL, POST; raw HEAD and DELETE
select ALL. This is bounded Node evidence, not application-level HEAD dispatch
or a proof of complete path traversal.

The durable wrapper input/emitted hashes in that replay were
`fff2a2609ac4237ea808c2bd170e4de4912c3f8e2e2dd10a9d85a7fa20273ac1`
and `93c5e8f09ba0736d2d361cf9a90e8ecb9c5089f36cd05d7e9e43935595133a52`.
The scope observations can be replayed from the repository root with:

```sh
printf '%s\n' '{"cases":[],"scopeProbes":true}' | ASDF_BUN_VERSION=1.4.0 bun verification/methods-loop/native.ts /path/to/pinned/hono
```

## Contract and proof review

The final review read the full [contract](../../HonoLean/Upstream/MethodsLoop/Contract.lean),
[correctness proof](../../HonoLean/Upstream/MethodsLoop/Correctness.lean),
[support lemmas](../../HonoLean/Upstream/MethodsLoopSupport.lean) and
[examples](../../HonoLean/Upstream/MethodsLoop/Examples.lean). The implementation
agent's focused build passed 29 jobs. No unresolved contract/proof defect was
found in this final review under the stated domain and interpretation limits.

The first independent review found an underconstrained trace constructor:
`Processed.capture` accepted an arbitrary old handler object and snapshot with
an endpoint `BlockContract`, without checking that those described the current
heap and reads. That admitted spurious prefixes and could make the universal
normal-domain predicate much stronger than intended. The constructor now
requires the structural `NodeParamLoop.Entry` facts at the actual selected
state. This adds no successful-evaluation or desired-output premise.

`NormalPrefixes` is a trajectory-wide structural admissibility condition over
every independent prefix. It contains no source-evaluator invocation or desired
completed output, but it does constrain readiness at prefixes reached later.
It must not be presented as a proved derivation of every such fact from one
initial heap. The current normal domain therefore remains a material hypothesis,
with a future general initial-state invariant derivation still open.

The independent `Processed` relation preserves indexed row order and records
either no heap change for a falsy choice or the prior independent capture
endpoint for a truthy admitted record. `Entry` connects the latter to the
actual current handler, key array, collector and parameter reads. The trace
retains repeated references; it does not snapshot params values into separate
collector objects. Its array/private/object-length frames derive from those
endpoints, rather than assuming the next source iteration succeeds.

The proof first initializes the actual saved length from the private array,
then constructs one current row read, lazy selection and guarded capture/skip
step. Induction on the remaining row count reaches that saved length. Extra
capture fuel lets every nested key loop execute within the enclosing budget.
`parsed_loop_satisfies` constructs successful normal execution and a completed
independent trace. `parsed_loop_correct` is forward correctness for an observed
execution under the same hypotheses; no iff or general completeness theorem is
claimed. `processed_collector` derives the original collector prefix followed
by the selected references, including duplicates. Final environment restoration
is a modeled scope observation, with the general lexical-cell limitations above.

The named `mixed_repeated_satisfies` example applies the universal parsed-loop
theorem to a proved `NormalPrefixes` domain. It covers an initial miss followed
by two hits selecting the same record, whose possible-key list is empty. The
prefix proof considers every Entry-linked independent prefix, rules out wrong
selection branches using choice uniqueness, and derives the first capture's
actual old handler, empty keys and collector contents. It is not merely one
successful evaluation and establishes that this multi-hit domain is inhabited.

Separate closed parsed-execution examples use two capture keys, check repeated
record identity and first-key precedence restarting at zero, and retain the
caller environment. The additional named `all_multikey_satisfies` example also
applies the universal theorem: one row has an own ALL record and no GET value,
so a GET request reaches fallback and captures two keys with object-valued
optional params. Its complete `NormalPrefixes` proof reduces every in-range
prefix to the initial state and proves current selection, shapes and reads;
it assumes no successful source execution. This establishes an inhabited
formal fallback/multikey domain as well as the repeated-reference domain.

These examples do not derive a general multikey, multirow initial-state
invariant. The universal theorem handles supported fallback choices under its
supplied binding/read domain, while finite conformance exercises additional
ALL cases. The actual initializer value is proved in the earlier source slice;
module import identity and actual helper call transport remain open here.

The parent reported all five finite harness groups passed: 1,555 exhaustive
mixed/repeated-reference contexts, 387 generated/long contexts, six supported
source faults plus type erasure, source/artifact/hidden-edit rejection and the
durable native probes independently replayed above. Those observations support
the conditional proof but do not discharge its runtime/native adequacy boundary.
The headline axiom guard records only `propext`, `Classical.choice` and
`Quot.sound`. No unfinished proofs, custom axioms or native proof shortcuts were
introduced. Full class/module/caller/traversal/exception-state semantics and
whole-Hono verification remain open.
