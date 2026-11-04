# ECMA-262 2025 primitive audit

This is an independent reference and definition review for the pinned
[`splitPath` source](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/utils/url.ts#L8-L14).
The authority here is the official **2025 / 16th-edition snapshot**, using its
[stable multipage publication](https://tc39.es/ecma262/2025/multipage/).
Unversioned draft pages can describe different algorithms.

The Lean additions establish refinements between independently written
mathematical descriptions. This review supports their intended interpretation;
it does not establish a complete formal ECMAScript semantics, a verified
TypeScript frontend, or native-engine conformance.

## Strings and finding a separator

Section 6.1.4 permits sequences of 16-bit unsigned values up to length
`2^53 - 1`, including unpaired surrogates. A one-unit separator can therefore
be represented by any `UInt16`; Unicode normalization and code-point iteration
would change the domain. Section 6.1.4.1 searches eligible starting positions in
ascending order and chooses the first equal substring, otherwise reporting no
match. For one unit, searching the suffix after a cursor and adding the cursor
to the first matching offset implements that rule. See
[String values and StringIndexOf](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-stringindexof).

## The specialized split algorithm

In [§22.1.3.23](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.split):

1. Steps 1–5 check the receiver, resolve the split hook, convert strings and
   choose the limit: default `2^32 - 1`, otherwise `ToUint32`.
2. Step 6 handles zero capacity. Steps 7–9 cannot apply to `/`; step 10 handles
   empty input with one empty field.
3. Steps 11–14 search from a cursor, append the preceding field, then stop at
   the limit or advance past the separator and repeat.
4. Steps 15–17 append the remaining suffix, including an empty one, and create
   the result array.

Thus truncation precedes Hono's later removal of one leading empty field.

## Array creation, lookup and equality

[CreateArrayFromList](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-createarrayfromlist)
allocates an array, then defines consecutive own data properties; their
writable, enumerable and configurable attributes are true.
[Get](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-get-o-p)
delegates to the object's internal property lookup.
[GetMethod](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-getmethod)
uses `GetV`, which also handles primitive receivers through wrappers. A
nullish hook means absent; another non-callable value throws.
[Strict equality](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-isstrictlyequal)
first distinguishes types; string equality compares code-unit sequences.
Consequently `undefined === ''` is false, while a string equals `''` exactly
when its sequence is empty. These are the reachable comparison cases here.

[ArrayCreate](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-arraycreate)
uses the intrinsic array prototype when no prototype is supplied, bounds array
length by `2^32 - 1`, and creates writable, non-enumerable, non-configurable
length. The split path uses neither a global `Array` constructor call nor a
species hook. Under
[OrdinaryGet](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinaryget),
an absent own property continues through the prototype chain; it is not
automatically `undefined`. Getters may execute. The simplified missing-index
rule therefore needs the relevant inherited-property case excluded.

For `paths[0]`,
[property-access evaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluate-property-access-with-expression-key)
forms a reference. Reading it through
[GetValue](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-getvalue)
converts the numeric zero to property key `"0"` before internal lookup. The
natural-index model specializes this case; it does not prove general
property-key coercion.

## Dense-array shift

[§23.1.3.27](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.shift)
performs these steps:

1. Steps 1–2 obtain the object and its array-like length.
2. Step 3 handles zero length by writing zero length and returning undefined.
3. Steps 4–6 save index zero, then visit source indices `1` through `len - 1`
   in ascending order. Each present source is read and written one position
   earlier; a missing source causes deletion of that destination.
4. Steps 7–9 delete the old last property, reduce length, and return the saved
   first value.

For fresh dense arrays, every visited source and destination is an own ordinary
data property. Ascending copies leave later sources intact. Writable properties,
configurable elements and writable length make the modeled updates succeed.
Generic sparse arrays, inherited properties, accessors, proxies and failing
updates require additional semantics.

## Preconditions and corrections

The primitive interpretation restricts the receiver to an actual primitive
string and the separator to one primitive code unit. Input length and normalized
limit must respect their language bounds. Relevant method lookup must select
the standard builtins in the specified realm, without unmodeled lookup effects;
the array must remain fresh and unmodified during these operations. Resource
availability is idealized separately from the language-visible bounds.

Two distinctions matter when reviewing earlier assumptions:

- **Primitive separators still have hook lookup.** The
  [2025 step 2](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.split)
  includes primitive `/`; an Object-only guard would skip required behavior.
  The relevant lookup must find no effective custom hook.
- **Prototype restrictions are conservative.** Dense own elements shadow
  inherited indices. Default splitting produces at least one field before
  Hono's condition, so its initial index zero is present. A blanket exclusion
  of indexed prototype pollution is stronger than those particular reads need;
  it remains appropriate for the generalized missing-index abstraction.

Realm/prototype conditions concern the actual lookups and created object's
prototype. They do not require trusting replacement global constructor names.
The current observable is returned array contents; arbitrary property lookup on
the returned object, descriptors, identity and allocation traces need their own
contracts.

## Review of the formal definitions

[StringSplit.lean](../../HonoLean/Upstream/ECMA2025/StringSplit.lean) independently
defines first-match search, absolute cursors, substring extraction and remaining
capacity. Its executable definitions do not invoke `List.splitOn`;
`stringSplit_refines` proves agreement with that existing primitive. The search
lemmas establish an actual first occurrence, and `stringSplit_length_le`
supplies the bound needed before native array interpretation. Theorems over
arbitrary lists and natural limits have a broader mathematical domain than the
native interpretation.

[DenseArray.lean](../../HonoLean/Upstream/ECMA2025/DenseArray.lean) independently
defines indexed properties, ascending copies, deletion and length changes.
Its dense representation requires all indexed own properties to agree with
the represented list, including absence beyond its end. Shift refinement is
proved from those operations; list tail is the result to prove, rather than the
definition of the step model. Heap refinements separately account for fresh
addresses, shared references and other cells. String/undefined comparison is
explicitly restricted to its reachable domain.

[PrimitiveBridge.lean](../../HonoLean/Upstream/ECMA2025/PrimitiveBridge.lean)
connects execution of the parsed pinned text to the composed primitive model's
contents. `default_split_legal_array` supplies the default result's length bound.
Those results do not discharge the separate receiver, dispatch, realm,
descriptor, extraction or engine obligations merely by composing the models.

The review found no circular definition or conflicting result case in these
specializations. This conclusion is about the inspected definitions and proof
statements. Standard-library facts and ordinary Lean axioms still belong to the
proof argument; no custom source-equivalence assumption is justified. Manual
agreement with the clauses does not replace a formal refinement from an
established full semantics or prove a JavaScript engine correct.
