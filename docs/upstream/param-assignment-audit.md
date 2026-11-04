# Trie parameter assignment: independent contract and audit

This slice is the assignment at
[`src/router/trie-router/node.ts:79–80`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L79-L80)
in Hono commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`:

```ts
handlerSet.params[key] =
  params?.[key] && !i ? params[key] : (nodeParams[key] ?? params?.[key])
```

The preceding line obtains `key` from `handlerSet.possibleKeys[i]`. This is the
inner loop's index, not the enclosing method loop's index. The enclosing method
first assigns a newly created null-prototype object to `handlerSet.params`.
These are source context facts; verifying this assignment does not establish
that every execution of the entire method reaches it with that context intact.
The exact fragment, byte offsets, whole-file hash and containing method are
recorded in [source.json](../../verification/param-assignment/source.json).
The fragment SHA-256 is
`f16da7b6723a3af9dbcc95526a216a1ed204c6596d85788bb12e4d15b9b4f793`.

## Independent value contract

For stable, effect-free property reads, let `p` be the result of the optional
parameter read: undefined when `params` is null or undefined, otherwise its
ordinary property lookup at `key`. Let `n` be the ordinary `nodeParams[key]`
lookup. The selected value is characterized by these disjoint cases:

| Condition | Selected value |
| --- | --- |
| `p` is truthy and the inner index is zero | `p` |
| Otherwise, `n` is neither null nor undefined | `n` |
| Otherwise | `p` |

This is a relation over values and predicates, independent of the expression
evaluator. A successful write to an initially empty, extensible null-prototype
output object creates an own data property containing that value, with writable,
enumerable and configurable attributes. Other object cells, the environment and
the array heap are preserved. The return value of the modeled assignment is
the selected value; the source uses it as an expression statement.

`parsed_source_correct_framed` also permits an output containing earlier own
properties. It requires that output to be null-prototype and extensible, with
the current key absent, and proves the exact new data-property update.
`absent_key_preserves_prior_properties` retains the complete old descriptor
store behind the new entry. That list-store fact does not model native
`OwnPropertyKeys` enumeration order. Establishing key absence from the complete
`possibleKeys` construction and loop is still outside this fragment proof;
the theorem does not assume a successful write or its desired selected value.

The predicates are different. Empty strings, zero and false fail the first
test, but all three are retained by the node fallback. Ordinary objects and
arrays pass the first test, even when empty. Under the source loop's integer
domain, `!i` is true exactly at index zero. The finite integer model does not
represent all Number values. The normative
[ToBoolean operation, §7.1.2](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-toboolean)
also treats undefined, null, either numeric zero, NaN, zero BigInt and empty
strings as false, and otherwise returns true, subject to the legacy HTMLDDA
exception. That exceptional host object is outside the ordinary-object model.

## Effects and evaluation order

The following is the independent operational reading of this particular
source, including cases deliberately beyond the pure-read proof domain:

1. Read `handlerSet.params`, evaluate `key`, and save the destination reference.
   Do not read the destination's previous value.
2. Read the optional parameter value. A nullish `params` skips evaluating the
   optional access's key expression and yields undefined.
3. If that value is truthy, evaluate `!i`. Otherwise skip the right operand of
   `&&` and take the false conditional arm.
4. If the condition is true, read `params[key]` **again**. A getter could return
   a different value on this second read.
5. Otherwise read `nodeParams[key]`. Read `params?.[key]` again only when the
   node value is null or undefined.
6. Write the selected value through the saved destination reference, using the
   descriptors and prototype chain present after the right-hand side finishes.

The 2025 expression algorithms evaluate an assignment's left reference before
its right value, then perform `PutValue` and return the right value. Optional
access stops before its computed-key evaluation on a nullish base. Logical AND
returns its original false operand; nullish coalescing tests only null and
undefined; conditionals evaluate just the selected arm. Logical NOT applies
ToBoolean and negates it. See
[assignment, §13.15.2](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-assignment-operators-runtime-semantics-evaluation),
[optional chains, §13.3.9](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-optional-chains),
[short-circuit operators, §13.13.1](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-binary-logical-operators-runtime-semantics-evaluation),
[conditionals, §13.14.1](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-conditional-operator-runtime-semantics-evaluation),
and [logical NOT, §13.5.7](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-logical-not-operator).

Saving a reference is not the same as resolving its final setter. A getter in
the right-hand side can replace `handlerSet.params`, but the assignment still
targets the original object. Changing that original object's descriptors can
affect the subsequent write. The object model supports only its declared
descriptor forms; arbitrary user getters, setters and proxies require a larger
effect model.

The reference's computed key can initially be a value rather than an already
coerced property key. In the 2025 algorithms, object-key conversion may occur
inside [PutValue, §6.2.5.6](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-putvalue),
after evaluating the right-hand side. Nullish property bases can similarly fail
there after the right-hand side's effects. The source theorem restricts `key`
to a primitive string and the destination to an object. It does not establish
general key-conversion or primitive-receiver error timing.

## Inherited values and D1

The reads use ordinary lookup, not an own-property-only operation. In
particular, a missing own `__proto__` on an ordinary object can yield its
prototype object. That object is truthy and non-nullish. A fresh null-prototype
output can then receive it as its own `__proto__` data value. An ordinary output
with the inherited legacy setter has different behavior: the setter can ignore
a string right-hand side even though the assignment expression returns that
string. These follow the limited ordinary-object and legacy-accessor model;
see the [object audit](routing-object-audit.md) and
[ordinary Set descriptor dispatch](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinarysetwithowndescriptor).

Consequently this assignment cannot be modeled as unconditional copying of a
captured string or as a map update that discards inherited values. It is one
component of the existing D1 explanation. The fragment theorem does not prove
a full `Node.search` execution, the initialization and recursive call sequence,
the original capture-name fixture, or its JSON serialization. It does not add a
comparison exception or alter the recorded D1 controls.

`d1_fragment_returns_object` checks the actual parsed assignment in a manually
assembled entry state: the optional parameter object is empty/nullproto, the
node parameter object inherits the modeled legacy accessor, and the output is
empty/nullproto. It proves the returned and stored value is that prototype
object reference. Reaching this entry state from a complete route registration
and search is still a separate obligation.

At this assignment checkpoint the local mechanism connected the parsed helper
and assignment with a modeled caller-side binding and index. The
[subsequent loop milestone](param-loop-audit.md) extends the current
[local mechanism](../../HonoLean/Upstream/D1/Mechanism.lean) through the complete
parsed allocation/reset/append/key-loop block. Temporary capture and its
chosen-handler/key-array entry are still assembled manually. `proto_transfer`
retains `id` and `constructor` controls and remains short of a full TrieRouter
counterexample. Its `readValue` field now samples the temporary lookup after
the block; it is not a returned assignment value or event trace.

## Frontend and evaluator review

The shared parser must preserve `!` binding more tightly than `&&`, with the
conditional selecting between the repeated parameter read and the grouped
nullish fallback. The language grammar forbids unparenthesized mixing of `??`
with `&&` or `||`; grouping makes the pinned expression valid. An optional chain
itself cannot be an assignment target. The
[optional punctuator, §12.8](https://tc39.es/ecma262/2025/multipage/ecmascript-language-lexical-grammar.html#sec-punctuators)
is adjacent `?.` with a decimal-digit lookahead restriction; removing whitespace
before recognizing that token would accept a different grammar.

The reviewed parser uses separate AND and coalesce tails, rejects their
unparenthesized mixture, and retains one optional computed access without
silently extending its short-circuit scope. It rejects a direct optional
assignment target, numeric-literal suffixes, negative zero, unsafe integer
literals, unsupported binary subtraction and return-newline reinterpretation.
It continues to use the previous binding and reserved-name checks. Grouped
expressions can explicitly end an optional chain. The supported syntax remains
a conservative subset, not a complete TypeScript frontend or a typechecker.

The evaluator captures raw base/key values in `PropertyReference` before RHS
evaluation and checks its object/string-key write domain when invoking
descriptor dispatch afterwards. Optional indexing, AND,
coalescing and the conditional evaluate their selected operands lazily; NOT
uses the shared truthiness function. Property reads use the existing object
model with a bounded prototype traversal budget. Intrinsic method calls still
have their prior standard-realm interpretation, rather than arbitrary dynamic
method lookup. Unsupported operations and model-fuel errors are not a proof of
native JavaScript exception behavior or retained effects after an exception.

## Corroboration and remaining boundary

Read-only checks with `ASDF_BUN_VERSION=1.4.0` and an in-process
`Bun.version === '1.4.0'` assertion, guarded by the pinned revision, clean checkout
and exact source-file Git bytes, reproduced the branch table: at zero a truthy
prior parameter wins;
at a later index the node value wins; empty prior parameters do not win the
first branch; false, zero and empty node values survive `??`; null node values
fall back; null or undefined parameter containers are optional-safe. A getter
probe confirmed two parameter reads on the true arm and a write to the saved
original target after the getter replaced the holder's target. Separate probes
confirmed right-hand-side evaluation before object-key coercion and before a
nullish destination error. These are finite engine observations, not semantic
adequacy proofs.

The [fragment correctness file](../../HonoLean/Upstream/NodeParamAssignment/Correctness.lean)
connects a kernel-checked parse of the exact selected bytes to an independently
stated selected-value and descriptor-update contract. Its `ParameterRead`
premise covers an object with a successful pure read, or a null/undefined
container yielding undefined. The empty-output-slot premise establishes neither
allocation freshness nor non-aliasing. The framed variant has the same limit
and explicitly states its key-absence invariant. Native interpretation
still needs admissible ordinary-object heaps, primitive string keys, the
declared safe-integer index domain, the relevant standard descriptors, and
resource/engine assumptions. Pure supported reads exclude arbitrary getter
effects; requiring successful skipped-branch reads is a conservative theorem
premise, not a claim that native JavaScript evaluates those branches.

The Python line-span extraction, Git identity and generated-file freshness check
remain external tooling obligations. Recording the containing method is
provenance, not verification of its enclosing loops, class fields, module
initialization, routing behavior or host runtime. The wider
[trust boundary](hono-trust-boundary.md) and
[routing worklist](../../verification/routing-behaviors.json) remain open.
