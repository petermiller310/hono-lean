# Tuple destructuring: original plan and retained native boundary

The admitted default DATA-array profile is now implemented and checked. See the
[walkthrough](pattern-binding-walkthrough.md) and [audit](pattern-binding-audit.md)
for its precise guarantees and remaining interpretation boundaries. The next
source producer is the [capturing label match](label-match-plan.md).

The original plan below records the intended obligations after
[terminal tuple construction](pattern-construct-walkthrough.md). Its custom
iterator native observations remain separate evidence, not a general iterator
adequacy theorem.

The actual node.ts138 source is44B `[4205,4249)`, SHA-256
`4bd90c878a3496b7a05edc1a3a90ba0e83afc24484b15acd1e600d5aff95a2a1`:

```ts
const [, name, matcher] = pattern
```

Bind those exact bytes and retain the ArrayBindingPattern, first elision and
two lexical bindings. This is not three ordinary index expressions. JavaScript
uses its iterator protocol for array destructuring.

## Operational work and independent contract

Start with the actual produced tuple reference, initial old realm/default-array
iterator facts and a primitive query string where relevant. Do not supply a
completed iterator, returned triple, desired name/matcher bindings or a new
initialized regex record. Compose the constructor theorem to derive the tuple
and regex prerequisites.

Implement a genuine closed standard-array iterator cursor/done state. Every
next operation derives length and indexed Get from the current dense heap;
do not replace it with a supplied snapshot or trusted iterator callback. State
exactly how iterator and result objects are represented/projected and allocated,
what standard intrinsic identities/prototypes/Symbol.iterator facts are assumed,
and which native exotic/general-iterator behaviors remain open. Do not claim
native hidden allocation observation or pretend the dense heap already models
arbitrary own symbol descriptors or prototype overrides.
Array identity alone does not establish a current default iterator after
intervening/cache alias mutations; retain relevant realm/noninterference facts.

The required order is:

1. Evaluate `pattern`, obtain the current admitted iterator method, and create
   the standard array iterator/iterator record.
2. Perform the first IteratorStep for the elision. It skips reading the iterator
   result's value property. Standard ArrayIterator.next itself still reads the
   array's index 0, so an array index 0 getter can run despite the elision.
3. Step and read the next result value for `name`, then for `matcher`.
4. Follow IteratorClose when the iterator record is not done. After three
   successful yields from a three-element array, exhaustion has not been tested;
   there must not be an invented fourth step. Default missing `return` is an
   explicit specialization. Do not assume that closing with missing return
   changes the underlying array iterator's cursor or exhausts it. IteratorClose
   itself does not set the iterator record's Done flag. Save the next method
   when obtaining the iterator; read the current return method at close time.
   Missing return requires the complete prototype-chain GetMethod result, not
   merely absence of an own ArrayIteratorPrototype.return descriptor.

Derive the new lexical bindings and current matcher identity, preserving prior
objects/arrays/regex records/metadata and outer shadows. State the fresh selected
activation/TDZ/caller-scope boundary; a flat environment is not general native
live lexical-cell adequacy. Symbol/custom-iterator/getter/abrupt completion and
IteratorClose error/precedence cases need honest native-only controls until
their operational support is proved.

## Next composition and evidence

Connect actual selected url 68 construction to actual 138 binding, then derive
the current-exec receiver path and initialized-record facts for actual 156.
This removes staged name/matcher/brand assumptions. It does not derive
restPathString: source 146–154/path-input preparation must still be composed or
remain an explicit boundary. Pattern installation, private child read, outer
branch/cache/loop reachability and full native adequacy also remain open.

Use kernel checked inhabited/default-iterator examples and symbolic arbitrary
safe-range/UTF-16 composition; exact source/tamper/fault checks; independent
binding contracts; and pinned Bun/Node comparisons. Native custom-iterator probes
must distinguish skipped result.value from standard array[0] Get, count exactly
three next calls, observe return/close and preserve constructor/cache/D1
counterexamples. Keep every prior checked source cluster and fixed target intact.

The [native boundary preview](../../verification/pattern-binding/native-boundary.mjs)
checks the exact44B statement on pinned Bun/Node, including skipped result.value,
standard array index 0 Get, saved next method, late return lookup, three successful
steps followed by close and early exhaustion without close. It is explicitly
plannedFrontier/nativeOnly/verifiedfalse, with no registered formal binding
theorem. Its temporary iterator-prototype instrumentation is restored and
remains a separate native boundary, not the default-realm proof domain.

The preview discovered `ENGINE-ELISION-1`: with a custom iterator result 0
accessor, pinned Node22.22.2 skips the value read while Bun1.4.0 performs an
additional Get. A throwing getter therefore succeeds on Node and throws on Bun.
The selected ECMA-2622025 Elision algorithm uses IteratorStep without
IteratorValue, matching Node's observed skip. This is an outside-domain native
discrepancy, not a counterexample to the current default-DATA constructor slice.

The [minimal reproducer](../../verification/pattern-binding/elision-difference.mjs),
[exact records](../../verification/pattern-binding/native-evidence.json) and
[replay check](../../verification/pattern-binding/check-native.py) preserve both
outcomes. The original Bun assertion failure is recorded rather than erased.
These observations were recorded locally on macOS arm 64; configured CI replay
has not yet been observed remotely.
These per-engine facts do not change the existing Hono comparison/D1 allowlist
or register an unproved source-binding theorem. A future binding proof must
keep its standard-domain interpretation and this discrepancy distinct.
