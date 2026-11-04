# Path-offset source and contract audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Source and grammar

The complete source at lines 146–154 is 338 bytes, range `[4427,4765)`, SHA-256
`25d15d9b81bc22ba038dea387a703528896940949ae50f9f2f1163c0be9a65c9`.
Preparation at lines 146–153 is 276 bytes, range `[4427,4703)`; the suffix
declaration at line 154 is 62 bytes, range `[4703,4765)`. The checker binds exact working/Git bytes, artifact hashes
and generated embeddings. Kernel equations parse all selected syntax and
reassemble 276+62. Earlier splitter/startup identity is recorded separately.

OffsetSyntax/Sequence retain new add/addAssign nodes, branch, declarations,
indexed assignment and actual countedFor header/body/update. No loop or operator
is replaced by a desired table. A local quote-aware lexer admits +/+=/++;
the old lexer/parser/Expr/Stmt/Value/State ABI remain unchanged. Fresh mutable
declarations acquire authority, const assignments and outer writes without
authority reject, and parser controls retain TDZ/newline/precedence boundaries.
Callbacks, unsupported expressions and unknown/trailing syntax reject. These
are exact selected-source and conservative-subset checks, not a full frontend.

## Independent contracts and before-state domains

FreshInputs identifies the first actual null cache binding, primitive UTF-16
path, allocated dense string-parts array, saved length and initial native
array/integer bounds. CumulativeTable states each start by independent prefix
sizes. A real source-loop invariant derives append-at-current-length, complete
table contents, old-array frames and the final cursor. Scope restoration retains
the first cache update and restores old offset/p entries; full source adds the
rest constant for line 156.

CachedInputs instead describes the actual existing array/index read, numeric or
undefined slice argument and exact-integer/index/length bounds. It requires no
parts, saved length, alignment or correct-cache assumption. CachedContract
preserves the complete heap and existing cache identity and returns the slice
from that actual value. Cached[] and incorrect signed/out-of-range entries are
intentionally included, without repair or silent normalization.

Split/startup composition derives parts, saved length and null cache from the
pinned source. An explicit no-truncation length bound removes `.take` only after
proving it is inactive; complete suffix-as-joined-parts is not asserted from an
arbitrarily truncated SplitPathContract. For i<len, prefix decomposition derives
the exact remaining suffix and start≤path.length. The final local cursor can be
path.length+1, so numerical bounds include it. Fresh→cached composition derives
the later cache invariant from the earlier actual source result.

Startup at lines 87–97 and this block at lines 146–154 are separate activations. The
intervening routing/control-flow path, and preservation through those actual
intervening steps, remain open. Empty path has zero source parts, so an in-range
outer index cannot be fabricated; standalone zero-loop/slice tests are not a
claim that the containing search reaches this slice for that input.

## Language interpretation and observer

Addition is mathematical Int only. Native interpretation requires integral
operands and sums represented exactly; full string concatenation/coercion,
floating rounding, negative zero and exception taxonomy are open. Compound
assignment captures its lexical reference and reads the old value before RHS,
then writes through that saved reference, consistent with the fixed
[2025 assignment algorithm](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-assignment-operators-runtime-semantics-evaluation).
Source-derived path/parts bounds establish the relevant exactness range.

The model uses dense State arrays. Indexed writes replace or append; sparse
extension rejects. The fresh loop proves p=currentLength, so its actual writes
stay within this domain. Native observation is array read values/identities,
not hole/own-undefined presence equality. Other object/private/function/Set/this
fields are explicit preserved frames, not reconstructed from a default view.
Standard frozen string/array methods, writable ordinary arrays/length, clean
numeric prototypes, legal native lengths and successful resources are explicit
interpretation premises, not assumptions of a Hono output.

Undefined slice start is supported only in the new entry as start 0. Integer
starts use the existing clamping/substring primitive. This is the intended
[2025 slice specialization](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-string.prototype.slice),
not general coercion or receiver boxing. Wrong caches remain wrong; there is
no validation silently added to the source.

## Executable and proof evidence

The suite covers 334 actual-split/fresh/reuse/raw-UTF16/long contexts and 39
cached/zero/manual-input contexts in full and preparation-only modes, plus 70
Node contexts. Seven admitted source faults change starts, increments, writes,
cache branch, loop bound or slice index. Parser/layout/source-identity controls
are separate. No cases are removed to hide an unsupported or disagreeing result.

Native controls import pinned `src/utils/url.ts` directly using Node 22.22.2 or
Bun 1.4.0 native TypeScript loading; that frontend is unverified. The 338-byte fragment
itself is plain JavaScript and inserted verbatim. The isolated parsed-split/
re-embedding model fixture is explicitly separate from the current-heap source
startup theorem. The independent oracle uses delimiter positions and prefix
sizes rather than calling the source loop. Old arrays are retained fixture
roots and new source-visible arrays are registered by identity. These addresses
and heap counts are a source-array projection, not all native allocations.
Opaque fixture objects are restricted to O0, allocated on both sides.

Native-only boundary probes preserve cached holes versus own undefined, missing
parts/len, wrong caches, signed/clamped starts and old-value capture. They also
demonstrate string concatenation and rounding outside the numeric specialization.
Those observations do not formally extend the supported domain. Failure
comparisons assert rejection only, not exception identity or partial state.

The proof registry records managed focused/root builds, fresh kernel replay,
actual registered names/kinds, standard-axiom audits and independent review.
No unfinished proofs, custom axioms or native proof shortcuts are accepted.
The seven concrete witnesses include an inhabited source-prepared universal
application and actual startup followed by offset execution on empty and raw
UTF-16 paths. They keep child-map links as explicit inputs rather than claiming
full Node.insert traversal. An intermediate fixture elaboration exceeded the
recursion budget; local options and factored normalization repaired it without
changing the program, assertions or domains. Final focused compilation passes.
The suite is added to pinned CI; remote CI and a fresh parser-registry install
remain unvalidated environment checks. The full runtime/catalog, general
language/native adequacy and complete routing behavior units remain open.
