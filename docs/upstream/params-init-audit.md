# Params-initializer source and contract audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Exact source and interpreter boundary

The complete line 123 is 81 bytes, `[3672,3753)`, SHA-256
`6b7b4f3a523c4226e9a766dfadf996c15d130b51ab5ad96d47a61cf64b4e46c2`.
The checker compares exact working/Git bytes, source copy, metadata and generated
Lean string. The kernel equation parses the original declaration with both
literal arms and private reads retained. Neither branch is substituted away.

New ObjectInit syntax represents ordinary expression leaves, conditional
initializers, and literal property/spread items. It delegates ordinary/private
expressions and literal allocation/data definition to existing semantics.
Computed property items define data; unsupported uncomputed prototype-setter
literal syntax is not silently reinterpreted. Old Expr/Stmt/Value/State ABI and
existing parser/interpreter entries remain unchanged. All new modules disable
automatic implicit parameters. This is a conservative selected-source frontend,
not a general TypeScript/JavaScript frontend correctness claim.

Target allocation precedes spread-source evaluation, matching the fixed
[2025 object-literal evaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-object-initializer-runtime-semantics-evaluation).
Copying inspects own keys/descriptors, skips nonenumerable fields, reads the
selected data value and uses data definition, following the relevant
[CopyDataProperties specialization](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-copydataproperties).
General getters/proxies/symbols/boxing/coercion and full native semantics remain
outside that specialization. Nullish spread handling is separately modeled.

## Initial-only contracts

HeaderInputs records actual node/emptyParams bindings, allocated shared object
and intrinsic root, and the scoped raw private DATA field/pointer. Shared pointer
equality derives the true branch without any source descriptor/readiness facts.
Allocated shared identity also lets freshness imply a distinct new reference.

CopyInputs adds initial pointer inequality, an allocated ordinary source,
unique own keys and enumerable-DATA eligibility. Inherited descriptors and
nonenumerable accessors need no getter readiness. Source allocation supplies
its strict separation from the fresh target; allocation/private-store frames
derive the second source read. No future clone, Set result or interpreter-success
premise is an input to the source contracts.

InitContract specifies a single fresh ordinary result with prototype O0 and
extensibility. For every own descriptor, copied fields exist iff the original
owns an enumerable DATA field, with identical Value and new W/E/C attributes.
There are no extra own fields. Source self/nested/array/function references stay
shallow. All old objects and array/private/function/Set/this fields are framed,
the private pointer remains original, and the new params binding is retained.

OwnStringKeyOrder is complete and duplicate-free over all modeled own string
keys, not for-in/inherited enumeration. Copy-ready DATA reads permit the same
extensional contract for every such order. Raw target own-list equality across
orders is deliberately not claimed; an example demonstrates the distinction.
Native OwnPropertyKeys ordering and its adequacy remain open.

## Composition and provenance

Actual startup/reset establishes the shared branch. The init→capture→actual 202
private-write→child-init protocols use created, ignored and existing-own skip
outcomes. Data readiness is derived from actual earlier source outputs and
preserved through the real private write. The ignored-string case yields a
nonshared empty-map clone by identity; skip avoids a match-readiness assumption.
A successful-guard invariant handles every modeled successful guard case.
Reject/unsupported outcomes are not treated as successful continuations.

These are separate activations across omitted pattern/control-flow windows.
They do not prove actual 175, matcher.exec, Node.insert traversal, the complete
containing search or native/class/module interpretation. Source-prepared
witnesses demonstrate inhabited domains without supplying future private slots
or clones. Local ordinary params and later null-prototype handler output stay
distinct; existing D1 is neither normalized away nor claimed fixed.

## Native and finite evidence

The native wrapper declares a real fixture private field, seeds it before the
selected source, then inserts the exact original 81 bytes unchanged. The wrapper,
private setup and fixture/JSON transport are unverified. Native execution checks
all 315 pinned source/package blobs; no TypeScript erasure is required for this
plain-JavaScript fragment. A separate whole-router probe uses unverified Bun
TypeScript loading for eight multi-segment scenarios.

Every referenced fixture object/array is allocated on both sides. O0 denotes
native `%Object.prototype%`; the model uses its existing nonenumerable intrinsic
projection. Sentinel observation and full native-root descriptor framing are
separate from exact model-root framing. This does not equate full root own-key
spaces. Source=O0 copies nothing under the checked all-nonenumerable realm fact.
Copied O0 values retain identity. The observer compares other own descriptors
and prototype references extensionally, not native enumeration order or all
engine/internal allocation counts. Getter/setter counts are actual native
fixture observations, removed from model comparison rather than invented events.

There are 386 shared and 1,411 copy contexts, 54 Node cases, six required admitted
source faults, eight whole-router contexts, and separate syntax/identity controls.
Sixteen particular throwing getters compare finite rejection with model refusal.
They establish no universal native getter-failure claim: missing and legacy
getters, effectful successful getters, symbols and proxies are demonstrated
separately in native-only boundary controls. Errors expose neither matching
exception taxonomy nor partial-state/rollback guarantees.

Focused/root warnings-as-errors builds, fresh kernel replay, actual imported
names/kinds, standard-axiom audits and independent review are recorded in the
proof registry. No unfinished proofs, custom axioms or native proof shortcuts
are accepted. CI is configured; remote CI and a fresh parser installation are
unvalidated environment checks. All fixed runtime/full routing/native-adequacy
obligations remain open.
