# Trie parameter reset, append and counted loop: audit

The source target is
[`src/router/trie-router/node.ts:75–81`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L75-L81)
at commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`:

```ts
handlerSet.params = createNullObject()
handlerSets.push(handlerSet)
for (let i = 0, len = handlerSet.possibleKeys.length; i < len; i++) {
  const key = handlerSet.possibleKeys[i]
  handlerSet.params[key] =
    params?.[key] && !i ? params[key] : (nodeParams[key] ?? params?.[key])
}
```

Including the original indentation and trailing LF, this fragment's SHA-256 is
`0e326df450858658d281570b2a9dd89ee55b4b86cdd9540f80afbdbe9f34b84f`.
It begins after the outer method has selected a truthy `handlerSet`. It does
not include that selection, the outer loop or any route traversal. The
[source metadata](../../verification/param-loop/source.json) records the exact
span and containing-method provenance. The
[single-assignment audit](param-assignment-audit.md) describes the existing
per-key contract and its native interpretation limits. The block observation
is normal completion with resulting state. It discards unused normal statement
values; it does not model the entire ECMAScript Completion Record, including
the loop's accumulated value.

## Independent endpoint to establish

For an admissible entry state, the independent local endpoint is:

1. Allocate exactly one empty-own, null-prototype, extensible output object at
   a previously unallocated address. This must follow from executing the actual
   parsed allocation helper, not from an entry assumption that output is empty.
2. Set this handler object's `params` field to that new address, preserving the
   unrelated handler descriptors. Replacing the old reference does not clear
   the old object. An old parameter object at a different address from the
   handler is preserved; aliases of the handler observe its field update.
3. Append the **same handler reference** once to the handler-set array,
   preserving its former sequence of reference values as a prefix.
4. Snapshot the key count after that append. Visit each captured string key
   exactly once in increasing index order, beginning at zero and incrementing
   by one. An empty key array still performs allocation, reset and append.
5. For each key, create the own writable/enumerable/configurable data property
   selected by the independent per-key relation. Truthy prior parameters win
   only at index zero; otherwise a non-nullish node value wins; null/undefined
   node values fall back to the optional parameter read.
6. Preserve unrelated object and array cells, and restore caller bindings after
   the loop. The output has no extra own properties. Earlier written slots
   remain present while later slots are added.

The output's descriptor-store order can be specified exactly as a mathematical
list, but it must not be described as a proof of JavaScript property enumeration
order. A valid endpoint relation should state these heap, identity, descriptor
and selection facts without calling the block interpreter. Successful execution
and existence of an endpoint must be proved from entry facts; assuming the final
selected values or that execution already succeeds would make the result weak
or circular.

The inspected [determinism proof](../../HonoLean/Upstream/NodeParamLoop/Determinism.lean)
establishes selection uniqueness directly from those disjoint value cases.
Indexed induction then makes `Captures` unique, followed by `Prefix` and the
entire `BlockContract` endpoint. It does not appeal to the interpreter to define
the specification. Uniqueness alone establishes neither existence of an
endpoint nor native-heap validity; successful execution still needs its own
proof from the entry conditions.

## Entry facts, aliasing and read stability

The theorem needs an ordinary handler object whose `params` property can be
set, and a stable data property locating a dense string-key array. Supporting
both an initially absent `params` field and a previously writable data field
allows both first use and reset. Read-only properties, arbitrary accessors,
proxies and replaced methods need additional semantics.
For an existing writable data field, ordinary Set preserves its other
descriptor attributes. A contract using the all-true new-data descriptor must
therefore require that existing field's attributes already have that form,
rather than silently changing enumerability or configurability.

The inspected [setup proof](../../HonoLean/Upstream/NodeParamLoop/Setup.lean)
uses exactly that restriction: `Resettable` states ordinary descriptor-dispatch
and receiver-own-property conditions. It permits inherited writable data with
an extensible, absent-own slot, or an existing canonical writable data slot.
It does not assume that Set already produced the desired heap.
`execute_allocation` captures the left reference, invokes the actual helper AST,
derives the new empty object and then writes the saved reference. `eval_push`
runs afterwards. `execute_leading` composes these two statements with an
arbitrary continuation in the independently defined `setupState`.

The key list should have no duplicates for the absent-current-key invariant
used by the framed assignment theorem. The pinned insertion code builds a
`Set` at lines 33 and 51 and spreads it at line 58, but those lines are outside
this slice. Key uniqueness and stable dense-array interpretation are entry
obligations until their source-producing path is connected. The loop proof
must derive each new key's absence from that uniqueness and the already-written
prefix; it should not assume every future write's desired outcome.

Several alias distinctions affect the endpoint:

- **Handler-set array versus key array:** require distinct array references,
  or model what their aliasing does. Push happens before the length snapshot;
  an alias appends the handler object to the keys and changes the iteration
  domain. A pre-push claim that every array element is a string is insufficient.
- **Prior handler references:** the handler-set array may already contain this
  handler. Its old reference values stay the same, but every alias observes the
  new `params` field. Prefix preservation is not deep object immutability.
- **Read containers versus the handler:** if `params` or `nodeParams` aliases
  the handler, reset can change a subsequent read of the key `params`. Use a
  post-reset read state or state an explicit non-aliasing restriction. An
  entry-state value snapshot is not generally valid.
- **Read containers versus the new output:** native well-formed entry references
  cannot already point at an unallocated object. Abstract dangling addresses
  need exclusion or separate treatment; otherwise allocation can make a
  previously forged reference alias the evolving output.
- **Other read dependencies:** pure supported inherited reads may be admitted,
  including the legacy accessor involved in D1. Their relevant heap cells must
  stay stable across reset and each write. Arbitrary getter effects are outside
  the current pure-reader contract.

The narrow theorem may use stronger, clearly named disjointness conditions
instead of handling every alias. Such conditions describe its input domain;
they do not prove that the complete Hono call path satisfies them. The premises
should also have a constructive fixture or existence proof, so the theorem is
not vacuous.

## Counted execution and lexical environments

The initializer evaluates `i = 0` and the length snapshot once, after push.
Each successful body run is followed by exactly one increment and another
strict comparison with the saved bound. A syntax-depth budget may bound AST
traversal, but it must not impose a fixed 32-key limit. Termination can use the
remaining natural-number distance to the captured bound. The mathematical
model may cover arbitrary finite key lists; native array and numeric bounds are
a separate interpretation condition.

The source's `let i`, `let len` and body-local `const key` have lexical scope.
Caller bindings with those names must survive the block, and one iteration's
key binding must not leak into the next. The source introduces no closures
capturing these iteration bindings, so an implementation can specialize scope
handling to that declared domain while leaving general closure semantics open.

The imported `createNullObject` helper also has its own lexical environment.
Its free `Object` resolves through the helper's defining environment, not a
same-named caller variable. The shared heap is retained across its call, and
the caller environment is restored afterwards. Executing its body directly in
an arbitrary caller environment would implement dynamic scoping. An explicitly
supplied standard helper environment or a supported closure binding is needed;
neither establishes full module linking or mutable global lookup adequacy.

The official ECMA-262 2025
[ForLoopEvaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-runtime-semantics-forloopevaluation)
creates the loop environment, evaluates its initializer, runs the body process
and restores the previous environment. Its
[ForBodyEvaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-forbodyevaluation)
tests before the body, processes completion, creates the next iteration
environment and evaluates the increment. ECMAScript function objects retain
their defining environment; a new call environment takes that environment as its
outer environment. See
[NewFunctionEnvironment, §9.1.2.4](https://tc39.es/ecma262/2025/multipage/executable-code-and-execution-contexts.html#sec-newfunctionenvironment)
and [ordinary function creation, §10.2.3](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinaryfunctioncreate).

## Array and native-runtime boundary

The normative [Array `push`, §23.1.3.23](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.push)
reads array-like length, checks its generic safe-integer bound, writes each
argument at successive keys, writes the new length and returns it. Those writes
can fail or have descriptor effects on general receivers. Here the source
ignores the return value and pushes just one handler reference.

For successful native interpretation as a dense Array, require standard `push`
lookup, writable length, an extensible receiver, writable/available destination
slot, clean relevant prototype indices and capacity. An actual Array's length
must fit the array-exotic uint32 range, so before this push it must be less than
`2^32 - 1`. The generic `2^53 - 1` push bound alone is insufficient. At maximum
array length a non-index property write can precede the failing length update;
the simple successful dense-list model does not cover that exceptional trace.
See [ArraySetLength, §10.4.2.4](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-arraysetlength).

The possible-key array also has native length bounds. Its loop indices and the
single increment up to its final length remain exactly representable integers
in the successful dense-array domain. This does not justify arbitrary integer
arithmetic or all JavaScript Number values. Native keys are primitive, legally
bounded UTF-16 strings; arbitrary mathematical code-unit lists still need that
interpretation condition. Allocation, resource availability,
realm initialization and native-engine conformance remain outside the local
source-model proof.

## Independent finite observations

An isolated Bun 1.4.0 run used `ASDF_BUN_VERSION=1.4.0`, asserted `Bun.version`
in process, checked the upstream revision and clean checkout, and compared both
`node.ts` and `router/utils.ts` worktree bytes with their pinned Git blobs. It
executed the exact selected block with the actual imported helper:

| Case | Observation |
| --- | --- |
| `handlerSets` aliases the initial keys `['id']` | Push grows the array to two; output gets `id` and `[object Object]` own properties |
| An earlier array entry references the same handler, with an old parameter object at a different address | Both entries see the reset; that distinct old parameter object retains its old contents |
| Caller `i = 55`, `len = 66`, `key = 'outer'` | Those bindings retain their values after the block |
| Caller supplies a fake `Object.create` that throws | The imported helper still allocates an empty null-prototype object |
| `nodeParams` is the handler and the key is `params` | Output's `params` value is the output itself, proving reads happen after reset |

These deliberately include inputs outside a narrow disjointness domain. They
corroborate why the entry restrictions or more general semantics are necessary;
they are not full-router behavior theorems.

## Source and trust limits

The inspected
[source correctness proof](../../HonoLean/Upstream/NodeParamLoop/Correctness.lean)
establishes this endpoint for its explicit `Entry` domain. The handler owns a
canonical data `possibleKeys` field; the dense string-key array is distinct
from the handler-set array; keys are unique; the handler reset is structurally
permitted; the helper has the checked function body and a standard lexical
binding. Read containers refer to existing objects, and snapshot reads describe
the one state after reset and push. Prototype closure and a proved frame lemma
carry those reads across writes to the fresh output. This permits read-container
aliasing with the modified handler: a returned fresh-output reference can be
stored in the output itself.

`entry_loopFacts` derives the empty output from the actual setup. The body proof
derives the current key from the source index and derives its absence from the
unique-key prefix invariant. `execute_iterations` proves every remaining
condition/body/increment step by induction, with budget `remaining + 61`.
`parsed_source_satisfies` supplies budget `keys.length + 64` for the complete
parsed block and proves an endpoint exists. `parsed_source_correct` combines
that execution with independent endpoint uniqueness to obtain the iff theorem.
No public premise assumes a successful iteration trace or the desired output.

The inspected [examples](../../HonoLean/Upstream/NodeParamLoop/Examples.lean)
construct `Entry` proofs for both an empty list and three distinct keys, then
apply the universal execution theorem. Thus its premises are demonstrably
inhabited, beyond closed evaluator reduction. The three-key observation checks
the first prior value, a later node value, the inherited prototype value, the
null-prototype output, unchanged key array, same-reference handler append and
restoration of shadowed caller bindings. The prior handler array intentionally
already contains the selected handler twice.

The public `Entry` also explicitly bounds key count by `2^32 - 1` and the
pre-push handler count strictly below that maximum. The mathematical induction
does not depend on a fixed 32-key cap. These length conditions still do not
prove the full native array-descriptor, realm or engine interpretation.

The [D1 mechanism](../../HonoLean/Upstream/D1/Mechanism.lean) now executes this complete
parsed block, with the actual parsed helper installed as a lexical function.
Its manually assembled context has the temporary object at address 1, an empty
optional parameter object at 2, a chosen handler at 3, and separate one-key and
handler-set arrays. The source allocates output at 4, resets the handler field,
appends the handler reference and executes the one-key loop. Its `readValue`
observation is explicitly a temporary-property sample after the block, not an
assignment return or an event trace. The universal prototype-key result and the
`id`/`constructor` controls remain local model theorems; the temporary write and
route-entry reachability are not yet connected to the complete source trace.

The external source extraction and byte/hash freshness check remain tooling
obligations. A checked parse of this block does not verify surrounding private
fields, method selection, outer loops, insertion, module initialization or
complete `Node.search` reachability. D1 can gain a longer source-connected local
trace without becoming a verified whole-router counterexample. Existing
[trust boundaries](hono-trust-boundary.md) and the
[routing worklist](../../verification/routing-behaviors.json) still apply.
