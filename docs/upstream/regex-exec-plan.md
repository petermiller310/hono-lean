# Exec and match production: earlier plan and current status

The ordinary-callee checkpoint and the selected genuine builtin range-plus
checkpoint are now checked. See the [builtin walkthrough](builtin-exec-walkthrough.md)
and [audit](builtin-exec-audit.md): digits source 123→156→actual 158–161 is
proved on the created capture path, with computed m and collector layout.
Constructor/cache/tuple provenance, full regex, containing control and native
adequacy remain open. The [next constructor/tuple plan](regexp-constructor-plan.md)
binds the actual terminal expression at url.ts68.

The following records the earlier staged plan; “next” below describes that
historical starting point, not an additional completed whole-search claim.

The actual line 156 is 51 bytes, `[4766,4817)`, SHA-256
`dd13b5b1aed7d6f0a70808b80bcd633f572ea02596a1368573de50a48ac8b625`:

```ts
const m = matcher.exec(restPathString)
```

The earlier collector contracts receive a supplied match array. The current
ordinary-callee singleton→guard theorem computes that array from an executed
source body. Genuine builtin-regex production and the 161 collector join are
next; supplying a desired match under another name would leave those gaps open.

## Checked ordinary-callee checkpoint

The checked checkpoint introduces a conservative one-argument member-invocation
entry without replacing
the old shared parser/evaluator. Connect the exact source to its AST, resolve
and save the current `exec` value before evaluating arguments, and invoke that
saved callable with the matcher as `this`. Bind the real argument and captured
environment, retain effects, propagate failure, and restore caller scope.

The milestone proves this using supported executable source closures and independent
call-order/receiver contracts. Do not dispatch to a builtin merely because the
property is spelled `exec`. Do not invent an abstract fallback for a missing or
noncallable direct method. Custom methods can return values other than arrays;
the following `if(m)` must test that actual value's truthiness.

Existing zero-argument ordinary invocation and the global one-unit String.match
model do not establish these semantics. The current semantics/code audit and
native probe are evidence of that boundary, not a proof that it is closed.

## Earlier bounded milestone plan: genuine builtin regex work

Start with the generated no-flags text `^[0-9]+$`. Parse its actual code units
into a supported representation and compute matching operationally. Prove
agreement with an independent nonempty ASCII-digit-string language contract,
including empty, non-digit, newline and UTF16 rejection controls. Derive null
or the fresh match array and its actual substring; do not take a match result
as a premise. Give index/input/groups and array-descriptor observations explicit
models or an explicitly limited observation projection.

Tie the semantics to the actual current builtin identity, regex internal
representation and initial state, including relevant lastIndex behavior.
Source construction/provenance must be a separate visible obligation until
proved. A theorem for this fragment does not verify every regex Hono accepts.
Keep the remaining grammar, flags, captures, alternation, lookaround,
backreferences, Unicode and syntax errors in the full-runtime worklist.

Then connect actual tuple destructuring (node.ts138), input preparation
(146–154), direct invocation (156) and result guard (157) to the existing capture
and collection proofs. Derive matcher/name from the actual current tuple under
an explicit initial iterator domain. Current cache/tuple/callee data and
noninterference must be proved or modeled; TypeScript readonly is not a runtime
freeze. Later connect pattern installation (node.ts38–48/122) and getPattern
(url.ts50–77), including failures and repeated calls.

## Finite hazards already preserved

Run the [planned-frontier probe](../../verification/regex-exec/native-boundary.mjs):

```sh
bun verification/regex-exec/native-boundary.mjs ../hono
```

It checks the clean pin, all 315 source/package blobs and exact line 156 hash.
Its output explicitly sets `verified:false` and `plannedFrontier:true`.

- `next` equal to undefined and the string `"undefined"` share a cache key but
  choose different construction branches. Isolated labels in both call orders
  demonstrate that the first tuple/matcher/source wins. Terminal-first keeps
  `^[0-9]+$`; lookahead-first keeps `^[0-9]+(?=\/undefined)`.
- Malformed `next = "("` causes a constructor SyntaxError; a later terminal
  call for that isolated label can recover. Recognition and construction errors
  are different obligations.
- A replaced current `exec` receives the actual matcher as `this` and returns
  its custom value even for non-digit input. A noncallable replacement throws
  without builtin fallback.

The wrapper, actual Bun TypeScript loading and native engine remain unverified.
These observations do not add a comparison exception or close a source/runtime
coverage row. Body/next interpolation also needs literal-source treatment:
there is no implicit grouping or escaping that would turn arbitrary supplied
regex text into a different intended expression.

## Concrete next implementation obligations

Use a genuine small codeunit grammar, such as `^[lo-hi]+$` over safe literal
range endpoints, with start/range/plus/end syntax and compiled instructions.
Prove parser soundness/completeness for that grammar, then specialize lo=48,
hi=57. Avoid an exact-string switch that simply names a digits predicate.
Operational execution must derive span(0,input.length), empty captures and
termination, and be proved equivalent to an independent nonempty range-language
contract. Include newline, fullwidth-digit and surrogate controls.

Keep frozen MemberTable unchanged. Add a closed callable target sum containing
ordinary source closures and an explicit builtin RegExpExec target, selected
from saved function-reference identity with disjoint ranges. No arbitrary
trusted callback field may provide m. RegExp brand and compiled internal record
must be keyed by original receiver identity; mutable public source/name fields
are not the internal program. Prove ordinary dispatch reduces to MemberCall.

For the no-flags builtin slice, brand checking precedes argument coercion.
Read and numeric-ToLength the actual own lastIndex even though nonglobal exec
then uses local start 0 and preserves the property on success/failure. Success
allocates the result array with own0/index/input/groups; groups is an OWN
undefined property when no groups exist. Null allocates no result array, and
no global String.match accumulator should be introduced. The
[ECMA2025 builtin-exec algorithm](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-regexpbuiltinexec)
is the primary reference; richer coercions and flags remain explicit expansion
obligations.

Represent result metadata with a checked sidecar/projection alongside existing
dense array storage, preserving relevant descriptors and source m[0] reads.
State exactly which array observations are proved. Then bind actual 156, derive
157 truthiness/guard readiness, and add the small heap-append transport required
to consume the result in 161. Do not reintroduce a future Layout or supplied m.

Use actual pinned getPattern(':id{[0-9]+}') native fixtures for finite evidence.
Formal constructor/cache/tuple/installation provenance remains open until its
own source connection; include wrong-brand and changed/noncallable current exec
controls. Remaining grammar/flags/captures/alternation/lookaround/backreferences/
Unicode/errors and the fixed full catalog stay in scope.
