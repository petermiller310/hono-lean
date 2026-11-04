# Search startup audit

This is a conditional source-subset result for Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. The full runtime goal remains open.
The independent review and local replay record below must be read together with
the formal domain; finite native agreement is separate evidence.

## Exact source and execution boundary

`verification/search-setup/source.py` checks the clean pinned checkout, actual
working bytes against Git, full source identity, extraction, JSON metadata,
source copy and Lean embedding. The contiguous startup is `node.ts`87–97,
bytes `[2489,2849)`, SHA-256
`5010dd28d22d490760e62ef2ffd029727bf11e08b404dd99cf53f2028c513088`.
Blank lines, comment 90, indentation and final LF remain in the embedded text.
The Lean outer parser must consume this entire fragment.

The called `splitPath` declaration is the existing `url.ts`8–14 source copy,
bytes `[106,256)`, SHA-256
`53f73636562b6189de735c3bcd587941b6de4f4038e1651c616ce9c5a0b48652`.
Its parsed statement body runs in the current array heap. The composing runner
does not call the old contents-only `run` wrapper or supply a replacement array.

External extraction/embedding checks remain trusted identity tools. Parsing the
specific source text in Lean is not a proof of general TypeScript parsing,
type erasure, bundling, native module linking or JavaScript engine correctness.

## Function-call reference audit

The primary reference is ECMA-262 2025. The reviewed
[EvaluateCall rule](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluatecall)
evaluates arguments before checking callability and invoking the function; the
callee value is obtained earlier. The new entry preserves that order for its
supported callee/argument expressions. Unsupported receiver references are
excluded explicitly, rather than treated as bare calls with a lost receiver.

The source is an arrow function. The
[arrow creation rule](https://tc39.es/ecma262/2025/multipage/ecmascript-language-functions-and-classes.html#sec-runtime-semantics-instantiatearrowfunctionexpression)
captures lexical scope and lexical `this`. The selected body has no `this`
expression; the model uses an explicit module-undefined specialization and
restores the caller's runtime `this`. This is not a general arrow/ordinary-call
adequacy theorem. Frozen value captures do not establish live module cells.

Function-table ranges are checked against current ordinary functions and the
supplied private-method table after argument evaluation. The fixture uses the
latest table after its two source class definitions, so a second definition's
method handle is included in this check. Completeness of an external callable
registry remains an environment obligation.

A native probe found a runtime boundary: this standalone `.mjs` fixture observes
top-level `this` as `null` in Bun1.4.0 and `undefined` in Node22.22.2. Each arrow
retains its actual enclosing value when called with another receiver. The
suite asserts these two observations separately; it does not normalize them.
The actual selected `splitPath` body never reads `this`, so its startup
observations agree. This result reinforces the absence of a general native
module/arrow adequacy claim.

## State and domain audit

The independent startup contract must relate the actual returned array reference
to contracted split contents and its post-call heap. It must expose all four
allocations, old-array frames, private reset and preservation of other raw
private entries, caller scope, runtime `this`, ordinary objects, functions and
Set cells. The initial state may contain old arrays and nonempty registrations.
No completed startup state, path parts array, preallocated collector or future
helper layout is an input.

The mathematical input is a finite list of UTF-16 units. Native interpretation
additionally requires legal string/array sizes, standard intrinsic lookup and
prototype behavior, represented private/callable state and adequate resources.
The existing primitive refinements remain model results; full ECMAScript and
native heap/prototype/coercion/error adequacy remain open.

The empty input returns an allocated empty array, so startup is meaningful when
no outer iteration is possible. Downstream iteration composition requires an
actual in-range supplied index. That condition does not assert the desired
startup output or require every path to be nonempty.

Only the explicit call initializer is dispatched through the new extension.
The ordinary expression evaluator and private-call extension retain their old
interfaces and do not acquire arbitrary nested block-function invocation.
Except failures expose no partial state, native exception identity or rollback
guarantee. Headers99/104, pattern interleaving, loop progress, final sorting and
complete `search` remain open.

Independent native review also ran the exact startup with the imported function
on seven paths and checked its returned-array identity and earlier reset. A
noncallable function dependency threw after the reset had already taken effect.
This observation is preserved as a failure boundary; the model's Except result
does not expose that partial state or imply rollback.

## Native/model/oracle harness

`verification/search-setup/native.ts` verifies the pin and all 315 tracked
source/package blobs before loading upstream dependencies. Unmodified cases
call the actual imported pinned `splitPath`; function-fault controls execute
the supplied edited declaration. Class fields, method, module preamble,
registration pushes and the fixed stale-params seed come from checked earlier
source artifacts. Child traversal or `Node.insert` is not inferred from fixture
construction.

The wrapper inserts the contiguous startup and retains its declarations for
observation. Bun1.4.0 TypeScript erasure and wrapper construction are unverified;
wrapper input/emitted hashes are reported. The Lean Driver parses source again
and invokes the generic source-function entry. Its arrays are produced by
execution. Its observer reads actual bindings and heap cells.

The Python oracle scans delimiter units independently and observes startup
state. Cases include empty/leading/trailing/consecutive slash paths, NUL and
lone/pair surrogates, existing registrations, repeated fresh startup, distinct
receivers, invalid brands and separately supplied in-range outer indices.
Deliberate faults test allocation, reset, singleton nodes, call argument,
pending-queue aliasing, saved length, offsets and both function-body branches.
Identity controls reject changed generated artifacts and hidden working-file
edits, including the imported URL module. A nullable-type-order control retains
runtime behavior while changing retained syntax metadata.

## Checked declarations and replay

The central checked declarations are:

- `SourceSubset.parsed_splitPath_call_satisfies`: actual parsed function body,
  returned array reference, independent contents contract and caller/heap frames.
- `NodeSearchSetup.startup_satisfies`: full parsed 87–97 execution and the
  independent startup contract, from initial bindings/private kind/source
  closure facts.
- `NodeSearchSetup.startup_iteration_satisfies`: source-produced arrays feed
  actual 100–102 and the first parsed 105 leaf, with explicit i/j=0 activations.
- `NodeSearchSetup.Examples.source_prepared_input_has_universal_startup_contract`:
  actual parsed preamble/class/two owners/push/source202 establish an inhabited
  initial domain for every mathematical path.

The other three concrete witnesses retain empty-array identity, trailing/raw
UTF16 contents, and the full first literal branch with shared handler aliases.
The new generic examples cover argument effects/order, post-argument caller
restoration, table collisions, rejected scope/reference forms, modeled module
`this`, and fresh result identity after an ignored argument allocates.

Managed gates passed 17 initial runtime jobs,94 parser/contract,17 stateful
function proof,96 symbolic startup/composition,18 generic examples and 111
source-prepared examples. The integrated root build passed 393 jobs. Both headline
axiom guards retain only `propext`, `Classical.choice` and `Quot.sound`. All 45
new registry declarations were checked in the actual imported Lean environment.
Fresh root kernel replay completed successfully after that393-job build
(`lake env leanchecker --fresh HonoLean`, session 9445 closed, exit 0).

The new five-group suite passed 1,760 contexts in8.449 seconds, comprising 1,365
exhaustive UTF16 paths and 395 generated/repeated/frame/index/brand contexts,
plus nine detected source faults, a retained nullable-type-order control and
source/artifact/hidden-edit checks. The six native call-boundary groups passed
in both pinned runtimes. Baseline wrapper hashes are input
`24ab665c05f1e5857034a0e16cc60b7ac9a2bcf81621f8eefdcd2646f5ab1416`
and emitted
`432fd634177c4f9a807a68f891cc1d62a0ae67cf1485bb9585fc72e1f8b3d1ce`.

The earlier iteration suite passed 2,991 contexts/4 groups in10.938 seconds and
standalone split suite 4,165 original-source cases/4 groups in4.649 seconds.
The main comparison retains 467 agreements and the same one exact D1 discrepancy
across 468 lookups/98 appends. Adapter checks and the20-scenario CLI suite passed.
Generated inventory is byte-identical, with zero unconditional source-connected
runtime claims. Updated routing evidence passed 3 groups in1.229 seconds; all 36
complete routing behavior units remain unresolved.

Independent review checked the source spans, actual stateful execution proof,
independent contracts, inhabited preparation bridge, shared-handler example,
harness/oracle and diagram. It also reproduced the native wrapper hashes and
both runtime-specific module-this observations. A portability review found a
hard-coded macOS Node path; the harness now uses `HONO_NODE` or PATH, and the
boundary test passed again with PATH resolution. The Ubuntu workflow already
pins Node22.22.2. Remote CI was not observed here.

The initial generic example gate needed an expected axiom-message line-wrap
repair. Initial concrete example elaboration needed record indentation,
Option-bind/preparation rewrite normalization and a definitional numeric bound
instead of a decision procedure over a free path. All original cases and proof
domains were retained. The root harness also repaired an early observer draft
that discarded its optional iteration queue before repeated startup: the final
Driver threads that actual retained heap forward. No runtime/parser/State ABI
was changed, no source discrepancy was erased, and the original 30 assumption
IDs/order/status/source-proof arrays and historical 18 clusters remain intact.
