# Component-count source and contract audit

Target: Hono `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

## Source identity and syntax

`verification/component-count/source.py` checks the clean exact checkout and
working bytes against Git. The count expression is node.ts176, bytes
`[5476,5546)`, SHA-256
`8f93b148e6dc2f2cf67003adc4e5791a8c5c7132dcab0fd7c566599201ed9c54`.
The contiguous 176–178 slice is191B, bytes`[5476,5667)`, SHA-256
`134ae3cfeeabb597d841a7e8196603fef6578c30318252cdfc24e1f7a0b61a8b`.
Its suffix is the existing121B scheduling artifact. Extraction, Git, hash and
native wrapper tooling remain outside the kernel.

Kernel-checked equations retain the original regexp literal/match/optional
length/nullish AST and reassemble the three-line source with the existing
scheduling text. A separate RegExpSequence entry admits the selected syntax;
old expression/value/state constructors and old parser admission stay intact.
The old SparseSequence adds only a token-level forwarding helper. Comments,
general patterns, nonglobal/extra flags and unsupported expressions reject;
one exact-source parse equation is not a full TypeScript frontend proof.

## Independent normal-domain contract

Inputs identify the actual `m` binding, allocated legal/wellformed indexed
array, and own primitive UTF-16 string at index 0. Slash positions are specified
by enumerating input indices, independently of the operational scanner.
Completeness, order and the count bound are proved. The public source theorem
uses an initial input-length bound; it never assumes the desired count/output.
The count relation includes exact binding, old-array frame, fresh tracked
accumulator, regexp-cell and execution-trace facts.

Count→schedule composition retains sparse own presence, live target lengths,
aliases and the unconditional extra tracked accumulator slot. Empty-queue,
positive-count specialization derives first-hole consumer readiness with an
explicit ambient nonarray frame. It does not establish source 175, intervening
body reachability or a complete for-in/search-loop theorem.

## Reference interpretation and allocation projection

The reference is the fixed
[ECMA-262 2025 global-match algorithm](https://tc39.es/ecma262/2025/multipage/text-processing.html#sec-regexp.prototype-%symbol.match%).
It resets `lastIndex`, allocates accumulator A before exec, and returns `null`
if no match was accumulated. Every successful nonempty unit match advances
past one UTF-16 unit; final global failure resets `lastIndex` to 0.

The model tracks A even on a null return and keeps fresh regexp cells in a
separate store. Internal per-exec result-array identities/properties and other
native regexp object state are projected out. The projected heap length is
not native physical allocation count. Full ECMAScript/native interpretation,
general RegExp grammar/semantics, functions, prototypes, realms, descriptors,
getters/proxies/coercions, exceptions, scope exit and resource failure remain
separate open obligations. Interpretation assumes primitive receiver strings,
standard frozen String.match/RegExp@@match/exec, clean ordinary arrays and
successful resources. These premises do not assert a Hono output.

## Executable evidence

`tests.py` checks 784 raw UTF-16 count contexts,80 other-unit contexts,269
count/schedule/consumer contexts and 72 Node controls. Contexts include empty
and no-hit inputs, slash runs, nulls and lone surrogates, sparse own slots,
aliases, repeated calls, retained targets and long512-slash inputs. The oracle
uses an independent index set and own-slot transitions. Six full-source faults
and one count-only fault change actual admitted syntax; negative parser,
layout and stale/hidden-source identity controls are separate.
The initial conformance run exposed an oracle mistake: a truthy scalar shifted
from the queue is appended by concat as one element. The corrected oracle
retains that case, including when the matched-string array is the queue itself.

Native controls use unmodified methods. Separately cloned fixtures instrument
String.match and RegExp.exec to record actual returned matches and successful
positions. The trace's initial 0 is an observed fresh literal value, not proof
of a native lastIndex reset write. Subsequent entries observe post-exec values.
The model's match observation reads actual accumulator cells; its null-vs-array
branch is derived from the execution trace and justified by the formal match
lemma, not by separately exposing an intermediate source return. The driver
checks one fresh regexp/execution and a tracked accumulator on every success,
and compares the actual new regexp cell with the final cell in its trace.
Both paths reserve an explicitly opaque accumulator ID, including null cases;
no test claims to observe unreachable A. All initial array references must be
allocated before execution, so they cannot name future opaque slots.
Rejection comparisons claim neither exact exception identity nor partial state.
The five-group suite is added to the existing pinned CI workflow. A remote CI
run and fresh registry installation remain unvalidated environment checks.

`boundary.mjs` checks incoming lastIndex999, no-hit null/final0, raw UTF-16 and
empty input. Custom object-match and replaced-exec counterexamples demonstrate
the primitive/frozen-method restrictions. These are finite, unverified native
observations, not engine-conformance findings or a new Hono discrepancy.

## Proof and coverage status

Focused managed builds, integrated root build, fresh kernel replay, actual
registered-name/kind resolution and headline axiom audits are recorded in
[the proof registry](../../verification/proofs.json). Standard Lean axioms remain
explicit; no source-equivalence axiom or native proof shortcut is introduced.
Independent review covers source/spec/proof, native projection and oracle,
initial-only composition and fixed-ledger preservation.

The conditional cluster does not close a full routing behavior unit. Complete
matcher.exec/count-input production, other regexp behavior, containing class/
module activation, full source/frontend/native adequacy, all routers, handlers,
middleware, context, helpers, client/JSX/adapters and host obligations remain
in the unchanged full-runtime denominator. The long-running goal stays active.
