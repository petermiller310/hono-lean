# Possible-key Set producer: independent audit

The pinned source is Hono commit
`5ca49b0720755c585c9a9835f0a479ceea36fb52`,
[`src/router/trie-router/node.ts`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L28-L61).
Three operations contribute to the key array:

| Line | Actual source | Exact whole-line SHA-256, including indentation and LF |
| --- | --- | --- |
| 33 | `const possibleKeys = new Set<string>()` | `b7df4a9f23d3c5e90e79e372d65517305d12c13c6bd14196c523c12243be4467` |
| 51 | `possibleKeys.add(pattern[1])` | `0d625e45f8892b55c9a47b8e397d948154933fbf909b328611c4002d82a9f3ac` |
| 58 | `possibleKeys: [...possibleKeys],` | `db687e285c3aaa7ebe991f181cf9b5ab361cb8c31e18875c992bd4c9437b775c` |

The [source metadata](../../verification/key-set/source.json) records separate
byte windows. Creation and add retain their complete lines; the spread parser
consumes only the exact expression `[...possibleKeys]`, whose SHA-256 is
`6ba25aee0a3f4c964d594436a7c4884f6ff47f87206917d66a182e738249d2da`.
The surrounding field label, comma and handler record are provenance, not
verified object-literal storage.

These are **noncontiguous**. The enclosing path loop computes `pattern`, tests
`isParam`, traverses children and eventually stores the array in a handler
record. Executing the three operations for a supplied string-value sequence
does not prove which adds the complete `insert` control flow performs, that
`pattern[1]` is a string on those paths, or that storage/registration preserves
the produced array. Those are separate source obligations.

## Independent membership and order contract

Let `inputs` be the supplied sequence of primitive UTF-16 strings. Define
`FirstAt(inputs, key, i)` using a position witness: element `i` is `key`, and no
earlier element is `key`. This does not call Set add, a deduplication fold, or
the source interpreter. The output contract should establish:

- Every output value occurs in the input, and every input value occurs in the
  output.
- Output contains each value once.
- Output order follows the increasing positions of the input's first
  occurrences. Duplicate adds do not move a value to a later position.

Equivalently, output is witnessed by an increasing list of first-occurrence
indices covering all input values. Existence and uniqueness are separate
obligations from defining that relation. Membership and `Nodup` alone are
insufficient: sorting or keeping last occurrences could satisfy both while
changing the required order. For `['b', 'a', 'b', 'c', 'a']`, the required output
is `['b', 'a', 'c']`.

Order matters beyond presentation. The consumer's
[parameter loop](param-loop-audit.md) gives the optional parameter special
priority only at index zero. The producer must preserve the real first key,
as well as provide the uniqueness needed by the loop's absent-next-key proof.

## What the 2025 standard says

The reference is the official ECMA-262 2025 snapshot. The
[Set constructor, §24.2.2.1](https://tc39.es/ecma262/2025/multipage/keyed-collections.html#sec-set-iterable)
creates a branded Set with empty internal data. With omitted iterable, it
returns before obtaining an add method or iterator.
[Set `add`, §24.2.4.1](https://tc39.es/ecma262/2025/multipage/keyed-collections.html#sec-set.prototype.add)
checks its receiver, canonicalizes the key, scans existing live entries and
returns the same Set on a match; otherwise it appends and still returns that
Set. For this add-only history there are no deleted-entry holes.

This edition expresses the comparison as
[canonicalization, §24.5.1](https://tc39.es/ecma262/2025/multipage/keyed-collections.html#sec-canonicalizekeyedcollectionkey)
followed by SameValue, rather than directly calling SameValueZero.
Canonicalization changes only negative numeric zero. On primitive strings,
[SameValueNonNumber, §7.2.11](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-samevaluenonnumber)
compares length and corresponding code units; SameValue and
[SameValueZero, §7.2.10](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-samevaluezero)
therefore agree. No case folding, Unicode normalization, string boxing or
ToString conversion occurs. Equal lone-surrogate sequences compare equal;
precomposed `é` and `e` followed by a combining accent are distinct values.

The standard Set
[iterator method and iterator creation](https://tc39.es/ecma262/2025/multipage/keyed-collections.html#sec-createsetiterator)
yield live entries in insertion order. A suspended iterator can observe later
adds. The add-only, uninterrupted standard-iteration domain permits a simple
snapshot model; a claim about all mutable iterators would require more.

[Array spread, §13.2.4.1](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-runtime-semantics-arrayaccumulation)
obtains a synchronous iterator and consumes its successive values into a fresh
array using own data-property creation. It does not use `Array.prototype.push`
or ordinary assignment to inherited numeric properties. Array literals use
intrinsic ArrayCreate, not the mutable global `Array` constructor or species.

## Language, identity and snapshot boundary

`<string>` is a TypeScript argument, not a runtime conversion or guard. The
[TypeScript handbook](https://www.typescriptlang.org/docs/handbook/2/basic-types.html#erased-types)
explains that type annotations are erased. Checking the exact generic syntax
is useful source provenance, but is not a verified TypeScript erasure pipeline
or proof that every source-derived add receives a primitive string. That input
domain must be established separately from the surrounding producer path.
Boxed String objects are objects with distinct identities, not primitive keys
that Set silently converts into strings.

There is also a source-level sharing obligation before this input domain can
be discharged. The exported
[`getPattern` helper](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/utils/url.ts#L50-L74)
caches ordinary tuple arrays and returns the cached object directly. Its
`Pattern` type is annotated `readonly` at line 6, but the implementation neither
clones nor freezes that array. Later callers can receive the same tuple; native
mutation or an installed index getter can change a later `pattern[1]` read.
Thus a future proof needs appropriate ownership/noninterference conditions or
explicit cache-sharing semantics. The original string-producing branch and a
readonly type annotation alone do not establish an immutable pure-string input
for every later call. This is an open input/lifecycle obligation, not a new
whole-router bug theorem.

The bounded native finding is recorded as `URL-PATTERN-CACHE-ALIASES` in the
[routing worklist](../../verification/routing-behaviors.json), with observations
under `nativePatternCacheObservation.record`. Its
[isolated probe](../../verification/pattern-cache-probe.ts) checks Bun 1.4.0, the
pin and all 315 source/package blobs before import. Retaining and changing a
cached tuple renamed a later capture; an installed getter was read once during
add and twice in total after the first match. After changing the shared tuple,
an existing router returned an own `renamed` property with value undefined,
which its JSON representation omitted. These are finite sharing observations;
the worklist keeps the contract/source proof open and adds no comparison
allowlist exception.

The model should distinguish the mutable Set identity from its current ordered
contents. An add updates the addressed Set, returns that same reference and is
visible through aliases. A duplicate add preserves the entry's first position.
Representing every add as a fresh independent Set would miss alias behavior.

Each spread must instead allocate a fresh array. Its strings equal the Set's
ordered contents at that completed spread. Later adds can change the Set but
do not mutate an earlier spread array; later spreads allocate distinct arrays.
Existing object, array, function and unrelated Set cells must have their
appropriate frame preserved. Freshness refers to allocated cells, with the
usual native well-formedness boundary for abstract dangling references.

Native interpretation requires the normal Set constructor binding and genuine
receiver brand, standard `.add` member lookup, standard Set `Symbol.iterator`
lookup and iterator `next`, and no unmodeled getters, proxy behavior, custom
iterator effects or mutation interleaved during consumption. These are lookup
and runtime obligations; they should not be hidden behind an assumed statement
that Hono or Set is correct. The constructor's no-argument path itself does not
need to read `.add`, and spread's own-property creation does not need an
inherited-index-setter absence assumption merely to create its dense slots.

The domain also needs primitive legally bounded UTF-16 string values, sufficient
resources and a distinct output count at most `2^32 - 1` for the dense-array
length model. Above that boundary, larger numeric-looking property names cease
being array indices; spread does not have push's final length assignment and
must not be described as necessarily throwing at that point. See the
[array-exotic rules](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-array-exotic-objects).
General numeric Set keys, deletion/re-addition, arbitrary iterator mutation,
Completion-record values and partial effects on failure remain outside this
successful string-only observation.

The inspected
[primitive step model](../../HonoLean/Upstream/ECMA2025/StringSetSteps.lean)
keeps an indexed scan with explicit budget exhaustion, separately proved to
refine the compact add operation. Empty string is a yielded value, not an
end-of-iteration or deleted-slot marker. Its cursor can inspect newly appended
data on a later `next` until completion, and remains done afterwards. The
materialization theorem fixes the entry list throughout its drain and uses
budget `entries.length + 1`; it proves ordered list contents and the exhausted
cursor. Constructor lookup, native iterator/result objects and fresh array
property creation remain separate obligations.

The inspected [shared evaluator](../../HonoLean/Upstream/SourceSubset/Semantics.lean)
uses addressed mutable Set cells and a generic constructor expression whose
callee is evaluated, respecting a shadowed constructor name. The parser retains
the checked `string` type argument but the runtime model ignores it explicitly.
Array literals allocate their own address before evaluating elements, process
elements/spreads in source order and use a separate dense own-element primitive.
String iteration is rejected rather than silently treating UTF-16 units as
the native string iterator's code points. The
[kernel examples](../../HonoLean/Upstream/SourceSubset/SetExamples.lean) exercise
aliases, duplicate adds, fresh nested arrays, later-add snapshot independence,
constructor shadowing and unsupported domains. This reviews the declared
specialization; it does not supply the missing full native lookup proof.

## Guarded finite corroboration

A read-only Bun 1.4.0 run asserted its version in process, checked the pinned
revision and clean checkout, and compared `node.ts` bytes with the Git blob.
It used the actual three snippets in an explicitly supplied-value wrapper;
Bun's TypeScript transpiler erased the type argument. The wrapper supplied the
add sequence and pattern arrays, so it was not a full `insert` execution.

| Probe | Observation |
| --- | --- |
| Repeated ordinary keys, empty key, `__proto__`, `constructor` | First occurrence retained; special names were ordinary Set values |
| Repeated lone high surrogate | One equal string entry |
| Precomposed and decomposed accent strings | Two distinct entries |
| Return from every add and a retained Set alias | Same mutable Set identity |
| Spread, later add, second spread | Fresh distinct arrays; first snapshot unchanged |
| Standard iterator suspended before another add | The next step observed the new value |
| Own custom `Symbol.iterator` yielding the same value twice | Spread contained duplicates despite a two-entry Set |
| Primitive `'x'` plus two distinct boxed String objects | Three entries, with no coercion hook calls |

The last three cases explain the interpretation restrictions. They do not add
comparison exceptions or weaken the string-only contract.

The inspected [source proof](../../HonoLean/Upstream/NodeKeySet/Correctness.lean)
establishes the parsed creation, add and spread contracts separately.
`source_sequence_satisfies` composes creation with `runSuppliedTrace` and the
parsed spread. The trace executes the checked add AST for every supplied key;
`stagePattern` explicitly appends a caller-prepared `[undefined, key]` array and
binds `pattern` to it. Those staging arrays are trace scaffolding, not verified
allocations from `getPattern`. The internal fold is a proved witness for the
independent first-occurrence relation, rather than its definition. Old arrays,
object/function cells and unrelated Set cells retain the stated frame.

The [kernel examples](../../HonoLean/Upstream/NodeKeySet/Examples.lean) include an
inhabited constructor premise and apply the universal source theorem to a
nonempty trace. Ten events have first positions `[0,1,3,4,6,7,9]`, including the
empty string, surrogate values and distinct accent spellings. Snapshot and
alias examples account for the extra staged pattern array, and a quantified
later trace preserves the earlier snapshot. The `pattern[0]` mutation reaches
the caller-staged undefined slot and is unsupported in this string-only model;
it is not evidence that native `Set.add(undefined)` throws.

## Producer-to-consumer claim

A bridge can discharge the loop's unique-key premise from a proved successful
spread of this add-only producer. It must identify the actual produced array
and preserve the other loop-entry facts: handler field binding, separate
handler-set array, legal sizes, resettable field, helper binding and stable
parameter reads. A fresh spread array is still mutable: its contents must be
preserved until consumption. Later Set adds do not change it, but that frame
does not cover arbitrary later writes to the array itself. Requiring a complete
loop `Entry` that already includes
`Nodup`, then returning its same uniqueness field, would not establish the
missing producer obligation.

The inspected [loop bridge](../../HonoLean/Upstream/NodeKeySet/LoopBridge.lean)
avoids that circular shape. `ConsumerFields` omits both `unique` and
`keysFound`. `producer_snapshot_entry` obtains uniqueness from the independent
producer contract, obtains the fresh address and dense contents from the
checked actual spread, and transports that cell to the consumer state through
an explicit equality premise. It then constructs the full loop entry.
`producer_snapshot_loop` applies the proved consumer execution theorem. This
removes two assumptions from the handoff; the cell-transport premise and the
remaining storage/read/lifecycle facts are visible obligations, not proved
runtime edges between the two fragments.

The inspected
[composed witness](../../HonoLean/Upstream/NodeKeySet/LoopBridgeExamples.lean)
starts with a valid ordinary model context, proves creation, executes two
supplied duplicate `id` adds, obtains the producer contract from the universal
trace theorem, and checks the actual spread at array address 3. Caller-side
handler-field setup preserves that array cell explicitly. It constructs
`ConsumerFields` without uniqueness or array-content premises, then applies
the producer-to-loop theorem. Thus the bridge has a nonempty inhabited
composition; handler storage and the call-path handoff remain labeled
scaffolding.

Even a useful bridge for a supplied add sequence leaves `getPattern`, `isParam`,
the path loop, handler-record storage, method registration and later search
reachability open. The three snippet parse results must remain separately
identified; concatenating them must not be presented as a parsed contiguous
`insert` implementation. External source extraction/byte freshness, native
intrinsic adequacy and the wider [trust boundary](hono-trust-boundary.md) remain.
