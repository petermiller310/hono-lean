# Search collector and method selection: independent audit

This checkpoint connects four noncontiguous pinned source fragments at Hono
commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`:

| Fragment | Actual source | SHA-256 |
| --- | --- | --- |
| Fresh typed collector | [`node.ts:87`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L87) | `1ea9120b7217f11add1f8e423040d71aaaa291284a32e19bf763e424c52afb66` |
| Private methods-array row | [`node.ts:72`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L72) | `25a1f62882ae6b9395a2835ed8228f9f719b9fa60719e8332b579e07d5998bb7` |
| Typed selection declaration | [`node.ts:73`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L73) | `a23a8cc583f5cf4ecc62fd222e6f1b9a7d4015063410eaa1fa150fcb0a9461b9` |
| ALL initializer | [`router.ts:9`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router.ts#L9) | `dbe058367f32b84d12e5553209e5e423df157a281f6d14329f19301ae1f7ff18` |

The actual collector is line **87**; line 90 is an eslint comment. The
[source metadata](../../verification/search-entry/source.json) records exact
byte spans, both source-file hashes and containing functions as provenance.
The ALL span is only `'ALL' as const`, excluding its export/declaration prefix
and following LF. The other spans retain their whole declaration lines.
Reading or storing a containing function does not translate its traversal.

The selected source is:

```ts
const handlerSets: HandlerParamsSet<T>[] = []
const m = node.#methods[i]
const handlerSet = (m[method] || m[METHOD_NAME_ALL]) as HandlerParamsSet<T>
```

These declarations do not occupy one lexical block in Hono. The collector is
local to `search`; `m` and `handlerSet` are local to the separate
`#pushHandlerSets` activation. METHOD_NAME_ALL is imported from another module.
Fragment composition must make activation, argument and import transport
explicit rather than inventing one shared native scope.

## Selection means truthiness and ordinary lookup

ECMA-262 2025 evaluates the left operand of `||` once, obtains its value,
and returns that same value when it is truthy. Only a falsy left operand causes
evaluation and reading of the right operand. Its result is an operand value,
not a Boolean. `&&` binds more tightly than `||`; the grammar rejects mixing
`??` with either operator without grouping.
See [binary logical operators, §13.13](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-binary-logical-operators).

For this source, `m[method]` is an ordinary property read, including inherited
descriptors. If it is truthy, no `METHOD_NAME_ALL` binding or fallback read is
needed at all. If it is falsy, the source reads that binding and then reads
the fallback property. An empty array or object is truthy; empty string, zero,
false, null and undefined are falsy in the admitted value domain. This differs
from a check for null/undefined alone. General JavaScript Numbers, host exotics
and arbitrary native getter effects are outside the current value model.

When `method` equals `ALL` and the first read is falsy, the source reads the
same key **again**. Native getters can produce different values on those two
reads. A proof must not replace the source by a cached single read. The
ordinary-object model currently admits repeatable pure reads and specific
modeled accessors, not arbitrary effectful getters; its repeated read does
not establish adequacy for every native accessor.

An inherited truthy `constructor`, `toString` or `__proto__` can win over an
own ALL record. Own-key absence is therefore insufficient for a fallback
theorem. The standard Object prototype remains an ordinary source of inherited
values, even when JSON serialization displays `{}`. The model's relevant
prototype projection and explicit property frame do not enumerate every
native Object.prototype property.

## Type syntax adds no runtime validation

The TypeScript annotation and `as HandlerParamsSet<T>` do not inspect the
selected value or guarantee a handler-record shape at runtime. `'ALL' as const`
likewise leaves the string value unchanged; it is not a freeze or a runtime
validator. The official [TypeScript Handbook on assertions](https://www.typescriptlang.org/docs/handbook/2/everyday-types.html#type-assertions)
explains their compile-time removal and absence of runtime checks.

The shared syntax now retains named, generic and array type metadata, typed
declarations and assertions. The declared evaluator erases that metadata;
this is explicit model semantics, not a verified TypeScript compiler,
typechecker or module linker. Type names inhabit a different namespace from
runtime variable bindings. A claimed handler shape must come from executed
record construction and property reads, never from the annotation.

The reviewed evaluator preserves OR's laziness; the parser preserves precedence and rejects unsupported
unparenthesized nullish mixtures. It also rejects a line break **before** `as`;
newlines after `as` can continue the type. Independent inspection and parsing
with the cached TypeScript 6.0.3 frontend confirmed this distinction. Parser
acceptance does not establish all TypeScript early errors, resolved types or
native adequacy for every accepted program. Existing const/let, captured-cell
and block-environment-restoration limitations remain open.

## Independent local contracts

The [contract](../../HonoLean/Upstream/SearchEntry/Contract.lean) distinguishes
allocation, row binding and choice rather than defining a result as evaluation:

- The collector extends the old array heap with one empty array and binds
  `handlerSets` to its old heap length. All old array cells remain present;
  the fresh address was absent before allocation.
- A row declaration binds the value read at the supplied private methods-array
  index. The row can be an arbitrary value; the later ordinary-object selection
  theorem has its own admitted receiver/read domain. `RowInputs` records the
  allocated owner/array, lexical private identity and a natural-number index;
  its list-read witness is a structural read fact, not an assumed handler
  selection or completed declaration. Out-of-range dense reads yield undefined.
  Negative ordinary property names, sparse/proxy arrays and arbitrary native
  indexed accessors are outside this row model.
- `Choice` describes a normal direct property read and disjoint truthy-direct
  or falsy-plus-fallback cases. `ChoiceDomain` supplies successful reads only
  along the executed branch. It neither names a desired selected result nor
  requires the skipped fallback binding/read to exist.
- `ChoiceContract` binds the selected operand as `handlerSet`, preserving the
  other state components. Ordinary inherited values remain visible; the type
  assertion contributes no record-validity fact.

The declaration environment is a flat fragment-scope representation. Creating
a local binding there is not a theorem of the entire native search activation,
caller scope restoration, import binding identity or const mutability rules.

The [collector proof](../../HonoLean/Upstream/SearchEntry/Collector.lean) establishes
unconditional construction and an iff with `CollectorContract`. The
[row proof](../../HonoLean/Upstream/SearchEntry/Row.lean) checks its actual private
read and natural-index expression before binding the result. The
[selection proof](../../HonoLean/Upstream/SearchEntry/MethodChoice.lean) establishes
the two branch executions, constructs a choice from `ChoiceDomain`, and gives
the actual declaration's iff contract. Existence needs fallback-read
admissibility only when the direct value is falsy; the truthy branch needs
none. The actual ALL initializer
is separately checked to produce the unchanged string value and state;
connecting it to the import binding remains a separate handoff.

These local declarations execute after removing their own incoming same-name
fragment binding. That models entry into a fresh local scope; it is not a
source translation of activation records or evidence that a native caller's
outer bindings are destroyed. Statement observations retain state and normal
completion without modeling ECMAScript's general completion value.

## Registration-to-search handoff

The [bridge](../../HonoLean/Upstream/SearchEntry/Bridge.lean) replaces the earlier
preallocated-collector composition with a later allocation. It
models separate `searchActivation` and `pushActivation` handoffs, carrying
the registered heaps/tables while supplying distinct caller environments.
The latter receives the actual newly allocated collector as its argument.
This closes the previous collector allocation restriction, without asserting
that activation creation, argument passing or intervening source has been
fully translated.

From actual registration storage, the bridge derives the private array cell
and row at the appended index. It then proves the actual selection declaration
returns the newly constructed inner record for an **exact registered-method
request**, including special names whose matching own data property wins over
the prototype. The resulting `entryState` describes that executed declaration's
endpoint; it is not a premise supplying a preselected `handlerSet` binding.

This direct-hit composition needs no ALL binding because the source skips
the fallback. Arbitrary requests against an ALL registration require the
separate generic choice domain. In particular, query inequality or absence
of an own query property cannot exclude inherited truthy values. The actual
ALL initializer theorem does not silently establish a module import link.

The caller still supplies the selected node and index, matching request and
helper/read context. The bridge retains heaps across its explicit activation
handoffs; connecting that frame to every actual intervening search operation
remains open. The outer methods-array loop, its `len` snapshot and the
surrounding `if (handlerSet)` have not been parsed by these local declarations.

`parsed_pipeline_satisfies` connects checked registration execution, actual
collector allocation, actual private row declaration, actual typed selection
and the prior parameter loop. Its consumer `Remainder` contains no preallocated
collector, staged row or selected-handler binding, record/key shape,
resettable own shape or assumed uniqueness. The later empty collector derives
its contents, separation and capacity; source construction and the supplied
Set-event trace derive the record and key facts. Remaining helper,
descriptor-level prototype dispatch, prototype closure, key bounds and
post-reset read witnesses are explicit. Those witnesses constrain actual
reads, not a desired final capture or a future successful loop iteration.

The pipeline is conditional on an earlier checked registration execution;
its separate registration theorem already establishes existence from input
bindings and allocated cells. This is composition of completed source stages,
not an assumed handler-selection outcome. General native scope/call adequacy,
the real intervening search operations and source production of the supplied
Set events remain outside the theorem.

The [inhabited examples](../../HonoLean/Upstream/SearchEntry/Examples.lean)
check actual typed Set creation and two supplied duplicate `id` adds, actual
registration, then apply the universal pipeline theorem. No collector exists
before registration. It produces key snapshot array 3, allocates collector 4
later, reads stored outer row 4, and derives inner handler record 5. Caller
contexts deliberately contain stale null/false `m` and `handlerSet` values;
the actual declarations replace them. The consumer receives the actual
new collector and source-derived handler, not manually manufactured fields.

Additional controls cover the universal ALL fallback with explicit import
correspondence, each admitted falsy category, truthy array/number results,
missing ALL binding and skipped unsupported fallback accessor, inherited
constructor/prototype values, pure repeated-key reads and a wrong-operator
`??` mutant. Headline guards for source choice and the composed pipeline list
only Lean's ordinary `propext`, `Classical.choice` and `Quot.sound`.

## Independent finite observations

An independent exact-line probe asserted Bun 1.4.0, the pinned revision and all
315 source/package blob hashes, then transpiled the literal line-73 declaration
inside a supplied wrapper. A method-ALL getter returning zero then a record
logged two reads and selected the second result. A truthy empty-array direct
value skipped a throwing fallback getter entirely. Undefined, null, false,
zero and empty string selected an own ALL record. With an otherwise ordinary
`{ALL: record}`, reserved method names selected inherited constructor/toString
functions or Object.prototype through `__proto__` instead of that record.

These are bounded observations of the source expression under explicit
wrapper contexts. They do not prove arbitrary getter behavior, typechecker
correctness, the complete subsequent consumer, a router-wide counterexample
or a new comparison exception.

The durable [native harness](../../verification/search-entry/native.ts) preserves
these scope probes and records wrapper/emitted hashes while marking TypeScript
transpilation unverified. Independent replay of that harness also confirmed
that a selected numeric `17` stays numeric through the source's type assertion.
Its real exported Node smoke check observed GET's own handler plus ALL, with
POST and raw HEAD selecting ALL. This is bounded raw-Node evidence, not a
proof of the Hono app's HEAD/request behavior or of the complete search algorithm.

From the repository root, the guarded scope observations can be replayed with:

```sh
printf '%s\n' '{"cases":[],"scopeProbes":true}' | ASDF_BUN_VERSION=1.4.0 bun verification/search-entry/native.ts /path/to/pinned/hono
```

Source extraction/byte freshness remains external tooling evidence. Class
initialization, module linking, search traversal, the outer methods-array loop,
its length snapshot, node/index choice, final sorting and result construction
still require source proofs. Retained containing-function provenance is not
evidence that those operations have been verified.
