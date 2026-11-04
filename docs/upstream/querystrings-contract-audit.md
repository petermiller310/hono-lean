# `getQueryStrings`: contract and source audit

This slice targets
[`src/utils/url.ts:140–152`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/utils/url.ts#L140-L152)
at Hono commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`. The helper returns raw
query text, including its initial question mark. Both delimiter searches begin
at **UTF-16 offset 8**. It accepts a string; its behavior does not require that
string to be a valid URL.

## An independent observable contract

Represent input and output as sequences of `UInt16` code units. Define
`FirstFrom(input, marker, start, index)` by three independent facts:

1. `start ≤ index`.
2. The input's element at `index` is `marker`.
3. No position from `start` up to, but excluding, `index` contains `marker`.

Define absence by the lack of that marker at every position at or after the
start. These are position witnesses, not calls to the executable search.
For start 8, the contract has three cases:

- No eligible `?`: output is empty.
- First eligible `?` at `q`, with no eligible `#`: output is the complete suffix
  starting at `q`.
- First eligible `?` at `q` and first eligible `#` at `h`: if `q < h`, output is
  exactly the segment from `q` through `h - 1`; otherwise output is empty.

The first-position witnesses must be unique, and every input must have either
a witness or absence. Those facts prevent a vacuous contract. The inspected
[correctness proof](../../HonoLean/Upstream/GetQueryStrings/Correctness.lean)
establishes successful execution, proves its output satisfies the independent
contract, proves contract-output uniqueness, and derives an exact source/output
iff theorem. The contract does not define the answer by calling its search
implementation.

`?` and `#` have different code-unit values, so their witnessed positions cannot
coincide. Replacing the reachable comparison `<` with `≤` preserves this helper's
outputs; it is not a valid fault witness. Reversing the comparison, changing the
search start, or removing fragment exclusion can change the result.

## Boundary examples

The following observations were checked directly with Bun 1.4.0 after checking
the upstream revision, clean checkout and selected file's exact Git bytes.

| Input | Output | Reason |
| --- | --- | --- |
| Empty string | Empty string | No eligible query marker |
| `1234567?x` | Empty string | Question mark at offset 7 is ignored |
| `12345678?x` | `?x` | Offset 8 is included |
| `1234567#?x` | `?x` | Hash at offset 7 is also ignored |
| `12345678#f?q` | Empty string | Eligible hash precedes query |
| `?1234567?a#b` | `?a` | Only markers at or after offset 8 participate |
| `12345678?` | `?` | An empty query still retains its question mark |
| `12345678?#` | `?` | The hash itself is excluded |
| `12345678??a##b` | `??a` | Later question marks remain ordinary text |
| Four `😀` characters followed by `?x` | `?x` | Four surrogate pairs occupy eight units |
| Three `😀` characters, then `a?x` | Empty string | The question mark is at unit 7 |
| `12345678%3Fq%23x` | Empty string | Percent text is not decoded |

A thirteenth observation used eight NUL units followed by `?`, a lone high
surrogate and `#x`; the returned sequence retained the question mark and lone
surrogate exactly. These are finite observations, distinct from universal
model proofs.

The pinned [upstream tests](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/utils/url.test.ts#L176-L190)
provide six assertions inside one test: ordinary query text, trailing `?`, no
query, fragment truncation, a fragment before query-looking text, and preserved
percent-encoded hash text. They do not themselves cover the full raw-string
domain, offset boundary or surrogate cases.

## Primitive reference and native interpretation

The authority is the official ECMA-262 2025 snapshot.
[String `indexOf`, §22.1.3.9](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.indexof)
checks/coerces its receiver and search value, normalizes the position, clamps it
into the string's bounds, and searches for the first occurrence. Absence becomes
numeric `-1`. For this nonempty one-unit search, a start past the input's end
cannot find a marker.
[String `slice`, §22.1.3.22](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.slice)
normalizes/clamps its endpoints, defaults omitted end to length, and returns
the selected code-unit interval, or empty text when the endpoints are reversed.
This source reaches slice only with a found nonnegative query position and,
when supplied, a later hash position. The primitive model also handles finite
negative integer endpoints by counting backward and clamping; those cases are
tested separately. Fractional, infinite or coercing JavaScript arguments still
require additional modeling.

Native interpretation requires a primitive string with legal length, standard
`indexOf` and `slice` method lookup in the relevant realm, and no unmodeled
lookup effects. No URL, Request, Fetch, regexp, decoding or split hook is used
by this function. Code units, including lone surrogates, must remain unchanged.
Under the language's
[string bound](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-ecmascript-language-types-string-type),
found positions and the constants 8 and `-1` are exactly representable integers;
this does not justify arbitrary integer arithmetic as a complete Number model.
Resource availability and engine conformance remain separate assumptions.

## Shared frontend review

This milestone extends the same
[syntax](../../HonoLean/Upstream/SourceSubset/Syntax.lean),
[parser](../../HonoLean/Upstream/SourceSubset/Parser.lean) and
[interpreter](../../HonoLean/Upstream/SourceSubset/Semantics.lean) used for splitPath.
The inspected implementation addresses these regression boundaries:

- Numeric literals and `indexOf` results use one signed-integer representation,
  preserving numeric equality across their origins.
- Negative array keys reject explicitly, rather than becoming index zero
  through natural-number truncation.
- Relational comparison binds more tightly than strict equality; both bind
  more tightly than the right-associative conditional operator. Repeated
  relational or equality operator chains reject.
- Only the selected conditional branch executes. The source's multiline
  conditional expression continues across its operator line breaks, while
  `return` followed immediately by a line break still rejects in this subset.
- Adding negative literals introduces an ASI trap: an expression followed by
  newline and `-1` can be subtraction continuation in JavaScript. Unsupported
  subtraction now rejects rather than silently becoming two statements.
- The parser now rejects dot/index suffixes directly on numeric literals.
  Without preserving whitespace, it must not accept invalid JavaScript such
  as an unreachable `1.slice(0)` arm. This review confirmed the syntax
  distinction with Bun; the fix includes a checked rejection example.
- Invalid bindings, escapes/comments outside the subset, unsupported operators,
  unsafe literals and trailing source remain rejected. Syntax acceptance
  alone is not proof of runtime type correctness or general JavaScript adequacy.

The old splitPath input/output theorem and its array index-zero, strict-equality,
shift and aliasing behavior remain regression obligations. A unified signed
integer representation can support this slice without claiming NaN, signed
zero, floating-point arithmetic or arbitrary property-key semantics.

The independent
[search/slice model](../../HonoLean/Upstream/ECMA2025/StringSearchSlice.lean)
uses position witnesses for first-match and missing-match characterizations;
its slice properties describe interval length and individual output elements.
The inspected definitions match the stated normalized finite-integer domain.
No circular contract, unwanted branch evaluation, negative-index clamp or
conflicting result case was found after the parser fixes. This was a source and
proof-statement review; root builds and kernel replay are recorded separately.

## Remaining source connection boundary

The exact extracted function text, parser equation, operational model,
independent contract and primitive refinements are separate review subjects.
Git/Python extraction and generated-file freshness remain external tooling
obligations. Hashes identify bytes; they do not prove what those bytes mean.

The function-text theorem does not verify initialization of the complete
`url.ts` module, import resolution, distribution transpilation, or a JavaScript
engine. Independent index/slice models can strengthen the local argument
without closing full language-model adequacy. Native observations, kernel
proofs, source identity checks and those remaining obligations must be reported
separately.
