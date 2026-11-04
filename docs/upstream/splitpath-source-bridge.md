# A checked source fragment: Hono's splitPath

This is the first source-connection experiment in the
[long-running Hono verification program](hono-verification-goal.md). The fixed
target is `honojs/hono` at `5ca49b0720755c585c9a9835f0a479ceea36fb52`, function
`splitPath` in `src/utils/url.ts`.

The result is a kernel-checked theorem about the **actual extracted function
text parsed into a small operational model**. It is stronger than hand-copying
an intended algorithm into Lean and comparing examples. Its remaining trusted
boundaries are still explicit: source extraction/freshness is checked by an
external script, and adequacy of the small model against ECMAScript is a
review obligation, not an existing theorem about an engine or full TypeScript.

The subsequent [primitive-step milestone](ecma2025-primitive-walkthrough.md)
adds independent search/cursor and indexed-property models, proves their
refinement to these compact primitives, and connects them to the parsed source.
The [year-pinned reference audit](ecma2025-primitive-audit.md) explains the
remaining interpretation boundary.

## What this function really does

Hono splits the string at every `/`, then removes the first field only if that
field is empty. Empty fields elsewhere remain. Thus:

| Input | Returned fields |
| --- | --- |
| Empty string | `[]` |
| `/` | `[""]` |
| `//a` | `["", "a"]` |
| `/a/` | `["a", ""]` |
| `a/b` | `["a", "b"]` |

This is deliberately different from the teaching router's restricted request
grammar. It does not trim, decode, repair or reject these raw string cases.
Existing router contracts and historical examples are unchanged.

JavaScript strings are represented as lists of 16-bit code units, not Lean
Unicode strings. This preserves ordinary characters, surrogate pairs, and lone
surrogates exactly. The parser's source text is ASCII; the function's input data
is not restricted to ASCII or well-formed Unicode scalar values.

The default `String.prototype.split` limit is `2^32 - 1` fields. Truncation
happens **before** the possible shift. The model includes that limit rather
than silently proving a different function for extremely long strings. Tests
also use small normalized limits to expose the ordering without allocating
billions of fields. Only default-limit tests run the original imported Hono
function; the small-limit cases separately exercise the same intrinsic steps.

## The source-to-theorem chain

1. [source.py](../../verification/splitpath/source.py) checks the exact Git revision,
   a clean checkout, and byte equality between the working `url.ts` and the pinned
   Git blob. It records the full-file/blob hashes, function byte range/hash, and
   produces the exact [function text](../../verification/splitpath/splitPath.ts.txt)
   and [Generated.lean](../../HonoLean/Upstream/SourceSubset/Generated.lean).
   The byte check also catches changes hidden by Git's `assume-unchanged` flag.
2. [Parser.lean](../../HonoLean/Upstream/SourceSubset/Parser.lean) tokenizes and parses
   that text in Lean into the generic [syntax](../../HonoLean/Upstream/SourceSubset/Syntax.lean)
   for this small fragment: declarations, variables, strings/numbers, indexing,
   method calls, strict equality, `if`, and `return`. It checks the actual
   parameter/result annotations and consumes the whole declaration. It does not
   recognize the entire function as one special token or map it straight to an
   expected answer.
3. [Semantics.lean](../../HonoLean/Upstream/SourceSubset/Semantics.lean) evaluates the
   parsed statements. Strings split into a freshly allocated model array;
   variables hold array references; `shift` updates that heap entry. An aliasing
   example proves that shifting through a second variable changes the contents
   returned through the original variable. Missing array index zero yields
   `undefined`, so a zero split limit does not trigger the empty-string branch.
4. [SplitPath.lean](../../HonoLean/Upstream/SourceSubset/SplitPath.lean) defines an
   independent contract: a nonempty delimiter partition reconstructs the whole
   input and no field contains a slash. Apply the split limit, then remove one
   leading empty field. Standard list lemmas prove uniqueness of that partition.

`parses_pinned_source` is a checked equation from the embedded text to the AST.
`run_splitPath` proves execution of that AST for every mathematical UTF-16 list
and every normalized model limit. `parsed_source_correct` combines both:

```text
parsing the pinned source and executing it returns these string-array contents
    if and only if
those contents satisfy the independent split/limit/leading-empty contract
```

The source parser uses proof-producing `cbv`; Lean's kernel checks the resulting
proof term. No `native_decide`, custom axiom, desired-result hypothesis, or
assumed source-equivalence proposition is used. The headline axiom guard allows
only Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound` foundations.

## Exact scope and remaining gaps

The evaluator theorem quantifies over all mathematical code-unit lists. For an
interpretation as native JavaScript input, `LegalString` records the ECMA string
length bound `2^53 - 1`; real engine allocation/size limitations are additional
environmental constraints. The operational model idealizes successful allocation.
The literal model limit parameter is already a normalized unsigned-32-bit limit;
it is not a proof of JavaScript's general argument coercions.

The intended native interpretation assumes a primitive string argument and an
ordinary standard-intrinsic realm: unchanged string split/array shift operations,
no custom `Symbol.split`, relevant inherited indexed properties, accessors,
proxies, or intervening prototype mutation. These assumptions belong to this
slice. They must not be generalized into an assumption that rules out Hono's
known object/prototype issues elsewhere.

The declared language reference is
[ECMA-262, 16th edition (2025), String.prototype.split](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.split)
and [Array.prototype.shift](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.shift).
These are adequacy references. The repository does not yet contain a proof
refining an established full ECMAScript semantics into this model.

The source parser deliberately rejects comments, escapes/non-ASCII source
literals, unsupported operators/calls, return-newline ASI cases, missing
same-line separators, reserved/duplicate bindings, branch declarations, unsafe
decimal integers and chained equality. This avoids silently erasing important
syntax distinctions. It is not a complete TypeScript frontend or typechecker.
Some syntactically accepted programs can still use unsupported runtime operations
such as `path.shift()` on a string; those yield model `unsupported`, not a
claim about actual TypeError objects. The shared model now supports truthiness
for its represented values, as explained in the
[parameter-assignment milestone](param-assignment-walkthrough.md). Fixed execution
fuel is an operational approximation for arbitrary programs. The concrete
universal theorem proves the pinned AST does not exhaust it for any input.

The observation here is returned array **contents**. An array-identity/freshness
contract, whole-module initialization/import resolution, arbitrary receivers,
cross-realm behavior, a verified external source extractor/TypeScript frontend,
and JavaScript engine/compiler correctness remain outside this theorem. The
external Git/Python embedding checker is part of the source-identity trust
boundary. A source hash alone is never used as a semantic proof.

## Checks and deliberate faults

```sh
python3 verification/splitpath/source.py --hono /path/to/pinned/hono
lake build HonoLean.Upstream.SourceSubset.Examples
lake env leanchecker --fresh HonoLean.Upstream.SourceSubset.Examples
python3 verification/splitpath/tests.py --hono /path/to/pinned/hono
```

The native audit compares 4,165 actual upstream/Bun, Lean-model, and independent
Python-oracle cases using numeric code-unit arrays end to end. It includes lone
high/low surrogates, astral pairs adjacent to separators, NUL, repeated/trailing
empty fields, and a long slash sequence. Another 810 small-limit cases check the
intrinsic operation order. Bun is pinned to 1.4.0 for this evidence.

Kernel examples and executable tests mutate actual source bodies: remove the
shift, read index one, or use `-` as delimiter. The generic parser accepts these
functions; execution yields concrete outputs violating the original independent
contract. Kernel-checked counterexamples show the universal contract is false
for each changed body. This tests semantic sensitivity, not merely a hash match.

Other tests reject stale generated artifacts, a wrong revision, ordinary dirty
files, hidden `assume-unchanged` file mutations, untracked inputs, and unsupported
parser cases. All source-control fault checks use private temporary clones;
the user's Hono checkout is never reset or modified.
