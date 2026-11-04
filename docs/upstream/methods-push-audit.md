# Private methods-array append: independent audit

The target is the complete call at
[`src/router/trie-router/node.ts:55–61`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L55-L61),
Hono commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`:

```ts
curNode.#methods.push({
  [method]: {
    handler,
    possibleKeys: [...possibleKeys],
    score: ++order,
  },
})
```

The [source metadata](../../verification/methods-push/source.json) binds all 144
bytes, including indentation and the final LF. SHA-256 is
`47cdbb194d9bd2dbd7c024e2d56e01e2d9bb3c10971e5af82ae0c5ecfaa7ab1b`.
The containing method is recorded as provenance, not translated wholesale.
The real class declares an array-valued **private data field**
[`#methods` at line 21](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L21).
This fragment starts with that field and the selected `curNode` already present;
it does not prove their initialization or the preceding insertion traversal.

## Private identity and receiver requirements

ECMA-262 2025 treats a private name as a unique identity with a textual
description, rather than an ordinary property string. Class evaluation creates
new identities; lexical private environments resolve the description to one
of them. Consequently, another class's identically spelled field and a public
property named `"#methods"` cannot supply this field's identity.
See [Private Names, §6.2.12](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-private-names),
[private environments, §9.2](https://tc39.es/ecma262/2025/multipage/executable-code-and-execution-contexts.html#sec-privateenvironment-records),
and [ClassDefinitionEvaluation, §15.7.14](https://tc39.es/ecma262/2025/multipage/ecmascript-language-functions-and-classes.html#sec-runtime-semantics-classdefinitionevaluation).

`MakePrivateReference` obtains the identity from the active lexical private
environment. `PrivateGet` searches the receiver's own internal private-element
list and throws if the identity is absent. This operation does not walk ordinary
prototypes or forward through a Proxy to its target. A plain Proxy wrapper around
a branded instance therefore does not acquire that instance's brand. This is
not a claim that a Proxy can never itself receive a separately installed private
element. See [MakePrivateReference, §6.2.5.9](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-makeprivatereference),
[PrivateElementFind and PrivateGet, §7.3.26/30](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-privateget).

The reviewed model keeps private slots separate from ordinary descriptors.
Its active spelling-to-stamp context and receiver-to-stamp/value table are
explicit inputs. Only valid allocated ordinary-object owners and private data
fields are admitted. The parser's default private context is empty, so an
out-of-class fragment is rejected unless its caller explicitly supplies the
needed private name. Whole-class parsing, private accessors, lexical closure
capture of private environments and native brand installation remain open.
Natural-number stamps represent opaque identities in this model; arbitrary
caller-supplied tables do not establish native identity freshness or reachability.

## Call evaluation order and errors

The normative call algorithms evaluate the callee reference and obtain its
value before arguments. `EvaluateCall` retains the receiver, evaluates the
argument list, and only then checks whether the obtained callee is callable.
See [call evaluation and EvaluateCall, §13.3.6.1–2](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluatecall).
For this source, the resulting order is:

1. Read `curNode`, resolve and read its private field, then obtain `.push`.
2. Retain that receiver and callee while constructing the complete object
   argument, including its Set snapshot and counter increment.
3. Call the retained method with the retained receiver and constructed map.

Missing private brand, a nullish field value, or a throwing push getter fails
before argument construction. A getter that successfully returns a noncallable
value permits argument effects before the later TypeError. A throwing iterator
can prevent the score increment; a failure during the eventual push occurs
after that increment. JavaScript does not roll these effects back.

The shared evaluator now prepares the receiver/member before arguments.
Its admitted array path captures a standard intrinsic and an array reference,
not the array's old contents. Invocation reads the current contents after
argument evaluation. Ordinary-object member calls retain a separately read
callee; their existing parsed-function specialization has no general `this`
or arbitrary-argument semantics. These are explicit supported domains rather
than a theorem of full native method dispatch. In particular, the array path
does not execute native accessors or model arbitrary mutable `.push` lookup.

The evaluator returns an error without an accompanying partially modified
state. Its rejection examples therefore do not prove JavaScript exception
traces, observable pre-error heaps or rollback. The successful theorem below
concerns the normal endpoint only.

## Independent normal endpoint

Let the input's object-heap length be `O` and array-heap length be `A`. Let
private field identity `p` on the existing owner contain array reference `r`,
whose current entries are `prior`. With primitive-string method `m`, handler
value `h`, ordered Set strings `keys`, and counter `n`, the independent endpoint
is:

- Construct outer map `O`, inner handler record `O + 1`, and key snapshot array
  `A`, with the own data fields and counter update specified by the earlier
  [handler-record contract](handler-record-audit.md).
- Append the outer reference to array `r`, preserving the original sequence
  of reference values: its contents become `prior ++ [object O]`.
- Return the new length, `prior.length + 1`, as the call expression's result.
- Preserve all private slots, all other old array cells, old object cells,
  function and Set cells, and other variable bindings. Change the resolved
  `order` row once to `n + 1`.

An existing array-cell read entails `r < A`, so the receiver cannot alias the
newly allocated snapshot. Other aliases to `r` are allowed and see the append.
Preserving prior element values is not deep immutability: those values can
refer back to the array that changes. Fresh allocation is relative to the old
allocated heap; native interpretation still excludes forged references to
future cells.

The [contract](../../HonoLean/Upstream/NodeMethodsPush/Contract.lean) describes
these structures directly, using the independent record shape and an explicit
array update. It does not invoke the evaluator or assume a successful append.
`Inputs` supplies resolved bindings, an existing ordinary owner, the lexical
private identity/slot, old receiver contents, Set contents and existing realm
prototype. These establish an admitted entry state, not the desired result.

The [source proof](../../HonoLean/Upstream/NodeMethodsPush/Correctness.lean)
checks the actual parse, derives the private receiver, prepares the call,
composes the earlier record-construction theorem, and proves the explicit
append equation. `parsed_source_correct` is an iff with `PushContract`;
`parsed_source_satisfies` constructs a normal result from `Inputs`. Its model
fuel is 34, independent of key count because the admitted intrinsic Set
snapshot and dense append are list operations. This is not a native cost or
resource bound. No successful call or final store shape is an input premise.

The actual statement also parses as one expression statement.
`parsed_statement_correct` proves its state projection through `execute`
with fuel 35. That wrapper retains the changed environment and discards the
push length; it does not use `runBlock`'s environment restoration. Its normal
completion omits ECMAScript's statement-completion value, and it does not
prove the surrounding `Node.insert` return or termination.

The [storage-to-loop bridge](../../HonoLean/Upstream/NodeMethodsPush/StorageBridge.lean)
derives the appended index, own method-to-inner-record edge, actual inner cell
and snapshot array from parsed execution. It carries these actual cells into
the earlier parameter loop rather than fabricating a replacement record.
`ConsumerRemainder` omits record shape, own `params` absence, resettable shape,
key-array contents and uniqueness. It still requires the separate collector
array, helper/context, descriptor-level root dispatch, prototype closure,
parameter reads and sizes. The Set trace contract supplies key uniqueness.

`selectedState` explicitly stages a caller's choice of the new inner record.
This is not an execution of `m[method] || m[ALL]`, an outer methods-array loop
or trie traversal. In particular, the new own method descriptor does not
establish how inherited names behave during later selection. The bridge's
read premises describe actual source reads, not desired captured outputs;
the inherited setter/read restrictions from the earlier consumer audit remain
visible. Private storage aliases are retained, and the receiver array must
differ from that later collector for the stated old-collector frame.

There is an important lifecycle restriction: `ConsumerRemainder.handlersOld`
requires the collector array to exist **before this registration push**. The
real [`Node.search` creates its collector at line 87](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L87),
after registration. The immediate bridge is a valid composition for an
explicitly preallocated collector, not a proof of that actual search lifecycle.
The source-storage theorem closes registration's map-to-handler-to-keys edges;
future collector allocation, intervening frames and actual selection still
need their own source connections.

The [composed examples](../../HonoLean/Upstream/NodeMethodsPush/Examples.lean)
establish actual typed Set creation and two supplied duplicate `id` add
events, derive their trace contract, and apply the universal private-call
existence/storage/consumer theorems. The input owner and private brand are
explicitly staged. The source produces outer map 4, inner record 5, key array
4 and score 8 from counter 7; the witness does not assume their fields or
uniqueness. Its separate collector already exists at array 1, matching the
bridge restriction above.

Two staged private owners share array 0, and the stored handler also points
to array 0. Appending therefore creates a genuine reference cycle through
the map and handler record. Both private slots retain the same array identity;
the example makes no claim of deep preservation or of this alias graph's
reachability through the real Node constructor. Zero-event, public-shadow,
wrong-identity/scope and no-append mutation examples supply controls. The
headline source and composed-loop axiom guards list only Lean's ordinary
`propext`, `Classical.choice` and `Quot.sound`, with no assumed host/source
equivalence or successful final endpoint.

## Native conditions and finite observations

The mathematical normal contract needs a separate native interpretation:
valid private/context correspondence, side-effect-free standard `.push`
lookup, standard stable Set iteration, a genuine realm Object prototype,
legal string/array sizes, a mutable initialized safe-integer `order` binding,
and sufficient resources. Returning the intrinsic from a side-effecting getter
is insufficient: that getter may already have changed a framed private slot.
The earlier [counter and scope restrictions](handler-record-audit.md#counter-and-native-domain-boundary)
still apply, including the unproved shared module cell and the known general
block/environment-restoration gap. This target is evaluated as an expression,
so its own counter update is retained.

Standard `Array.prototype.push` reads the receiver's length, performs ordinary
Set for each new index, sets length, and returns the new length. It can trigger
inherited setters or fail after earlier effects. Thus the dense append
interpretation needs writable/extensible standard array behavior and no
obstructing index/length dispatch. The receiver's old length is restricted to
less than `2^32 - 1`; a generic array-like push's larger limit does not justify
an unbounded dense native Array. See [Array.prototype.push, §23.1.3.23](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.push).

The durable [native harness](../../verification/methods-push/native.ts) executes
the exact extracted expression inside a supplied class with genuine private
fields. That class stages the entry context and is not the entire upstream
Node class. Independent scope replay asserted Bun 1.4.0 and checked all 315
pinned source/package blobs. Brand/prototype-clone/Proxy/other-class failures
left the wrapper counter at zero. Nullish field and throwing lookup failed
before increment; noncallable method, throwing call and frozen receiver
failed with the counter already incremented. A captured receiver remained
the call target after its owner's private slot was replaced, including during
argument iteration. Another iterator overwrote `.push` with a noncallable
value and appended a sentinel through the saved intrinsic. The already
captured callee still appended the constructed map and returned `2`, using
the receiver's current length. These hooks exceed the model's frozen lookup
and stable-iterator domain; their observations corroborate evaluation order,
not the full normal-contract frame under arbitrary hooks.

Another probe installed an inherited setter for receiver index `0`. Push
returned `1`, set length to `1`, and passed the constructed score-1 record to
that setter, but created no own index `0`. This finite observation directly
shows why intrinsic callee identity alone cannot prove dense storage. Native
faults/hooks are outside the normal model domain, not comparator exceptions
or whole-router bug theorems. Smoke checks through the real exported Node
class provide bounded observations without proving constructor or traversal
adequacy.

External source extraction and freshness checks, TypeScript/class frontend
adequacy, native engine correspondence, general Completion/error traces,
insertion traversal, pattern event production, method/ALL selection and
search traversal remain open. The containing method's stored provenance is
not a proof of these surrounding operations.
