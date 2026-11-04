# Literal-child branch: independent audit

This review concerns Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, specifically the contiguous
`src/router/trie-router/node.ts` window at lines 106–119. Its byte range is
`[3092,3583)` and its SHA-256 is
`8b66b71dc94881b830c28048f769a5f97bd3924ca2e760e787c549974e263e48`.
The containing file SHA-256 is
`faa72577fbea974a954c6c0e36546e3f53da97418ae154d2583ae43de1e5a825`.
The window begins with `const nextNode` at 106; 107 is blank. The surrounding
search traversal remains provenance and a separate proof obligation.
The [source record](../../verification/literal-branch/source.json), copied bytes and
Lean embedding independently passed the identity checker.

## Evaluation and contract requirements

The review uses ECMA-262 2025. An
[if statement](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-if-statement-runtime-semantics-evaluation)
evaluates its test, converts its value to Boolean, then executes only the chosen
statement. The model's
[truthiness specialization](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-toboolean)
must distinguish falsy null/undefined/zero/false/empty string from truthy modeled
references and nonempty values. It does not cover unrepresented Number or exotic
values by implication.

The independent branch contract must cover four paths:

1. A missing or falsy literal child: no propagation, wildcard read, helper call
   or queue append.
2. A truthy child and falsy `isLast`: propagate the current parent params value,
   then append that child reference to the current queue array.
3. A truthy child, truthy `isLast` and falsy wildcard test: propagate, then make
   the direct call.
4. A truthy child, truthy `isLast` and truthy wildcard test: propagate, make the
   wildcard call, then make the direct call in that resulting state.

The wildcard property expression appears twice, once in the test and again in
the first call's arguments. The parent's private params expression is also read
again for the direct call. Neither expression may be replaced by a snapshot
without deriving stability for the admitted read/effect domain. Both private
calls use the dynamic search `this`, which may differ from the parent, literal
child and wildcard target. The private callee is read before argument evaluation;
the current lexical/private/this context must be restored after each call.

The two-call proof needs a nonempty composition that derives the second call's
structural readiness and layout from the first call's result. Supplying completed
future execution, a desired capture output or a wildcard-never-present premise
would not prove this source branch. Aliases matter: helper calls append live
handler-record references, so a later reset can be visible through an earlier
collector entry. A contract that concatenates frozen capture snapshots would
miss that behavior.

[Array push](https://tc39.es/ecma262/2025/multipage/indexed-collections.html#sec-array.prototype.push)
acts on the current array. Queue append must preserve its prior prefix and
unrelated cells while allowing aliases to observe the append. The fresh queue
allocation at source 102 is outside this window; separation from a collector or
methods array must be derived by a larger composition or stated explicitly.
Native method lookup, descriptors, length limits and exotic behavior remain
interpretation obligations for the dense-array primitive.

Native [block evaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-block-runtime-semantics-evaluation)
creates and restores its lexical environment. Here `nextNode` belongs to the
enclosing loop body, which continues beyond 119. A standalone fragment runner
may restore its locals as an explicit projection boundary, but must not claim
that the native binding leaves scope at 119. A lower executor retaining the
binding supports later loop-body composition. Fresh root declarations, no nested
declarations and no lexical increments are admission restrictions rather than a
general TDZ, mutable-cell or block-scope theorem.

The source contains a `//` comment with quoted path examples. A quote-aware
comment path must preserve line terminators and string contents rather than
blindly removing text after `//`. Unsupported block comments and templates must
fail closed. Comment handling and conservative grammar admission do not prove
full TypeScript parsing, ASI or erasure correctness.

## Independent native probes

An independent wrapper ran the exact branch, module preamble, selected data
fields and complete private helper declaration with the pinned helper and ALL
imports. It guarded the clean exact revision, Bun 1.4.0 and all 315 source/package
blobs. Forty-one finite observations passed:

- Missing and falsy children skipped invalid later inputs. Nonlast queue paths
  succeeded with an unbranded dynamic `this`, while a reached private call
  rejected that receiver.
- Modeled falsy `isLast` values appended one live node reference; five truthy
  kinds selected the terminal path. Falsy wildcard values retained the direct
  call and left the queue unchanged.
- A wildcard getter ran twice and the second returned node supplied the call's
  target. The first helper's public params setter could change the parent's
  private params, and the direct call captured that later value.
- With a shared handler and wildcard equal to the literal child, both collector
  entries referenced the same handler. Its second reset changed what the first
  entry observed, while the separately retained first params object kept its
  earlier value.
- A frozen queue rejected append after propagation had already occurred.

Getter/setter mutation probes expose native boundary cases; they do not assert
that the current ordinary-object interpreter admits arbitrary callback effects.
The wrapper's input SHA-256 was
`87e0fce5b8744ffecf882ef51dec2eeb5e860827f8e5d74efaab862f5bbdffb9`;
the emitted SHA-256 was
`a5059452b0e5779635bf882b7097726cc723dda625cdff49e0663568631ecfd8`.
TypeScript erasure and wrapper construction are explicitly unverified tooling.
The current `Except` model does not expose native partial failure state or
exception objects; these probes imply no rollback or universal failure trace
theorem.

The landed native harness and independent finite oracle were also inspected.
The harness uses an immutable original source assignment to seed params, then
inserts the checked branch independently of supported source mutations. Its
observer compares live handler and params identities as well as capture values.
The oracle tracks mutable registration records and rechecks child-map aliases,
including a `'*'` key that can overwrite an aliased parent's selected child.
An independent six-case replay passed the four paths, repeated-record mutation
and this map-alias case. This is native/oracle evidence only. The landed wrapper
input SHA-256 was
`80ea6a0450a584e703dd872a35135e335559022663882fe7f4e70f4bde3ca0f7`;
the emitted SHA-256 was
`b722e772ac858a57e0b5b5e428590ba595d6cc5ffa0be3da0efb994d34deaa20`.

## Review status

The exact source window, fixed-edition control rules and contract requirements
above have been independently reviewed. The initial generic control runtime and
parser review is clean: condition evaluation occurs once, only the chosen arm
runs, return/error stops continuation, and private calls use the current dynamic
`this`. Lower execution retains root locals; the standalone runner explicitly
projects them out. Ordinary leaves reuse the old evaluator, and old expression,
statement and call-parser behavior has not been silently broadened.

The comment pass preserves CR/LF and quoted slashes, rejects unsupported Unicode
line separators even inside comments, and lets the old lexer reject copied
escape sequences. Fresh root names, rejection of nested declarations and lexical
increments, and existing statement-continuation/ASI checks were inspected.
Final generic examples were inspected: nested true/false outcomes, one condition
evaluation, skipped errors, current-state repeated calls, return/error short
circuiting, dynamic-this spoof resistance, declaration retention/projection,
quoted slashes, CRLF/ASI and both Unicode comment terminators. The implementation
owner reported its final focused 16-job gate passed in 18 seconds. This is
attributed focused evidence, not an integrated build or fresh replay.
Review also tightened ordinary invoke admission: a private read hidden under a
type assertion or conditional callee is rejected rather than routed to the old
NoArg interpreter. The recursive restriction and its regressions were inspected;
the owner reported the final 16-job gate passed again. This is conservative
syntax admission, not general function-alias or native call analysis.

The initial concrete contract and composition review is clean. Its four
constructors use independent write, live-array append and sequential helper
contracts. The wildcard and direct calls share one initial protected layout over
both row lists and all mutable records. Prefix invariants, current handler shapes,
fresh null-prototype cells and the bound on selected rows derive a fresh suffix
layout after the first call. Current private params/callability/storage reads are
transported through actual call frames rather than assumed as later execution.
Terminal queue preservation states collector separation explicitly; the nonlast
append contract itself preserves live aliases.

The parent reported the final finite suite passed four groups in 7.498 seconds:
1,152 exhaustive contexts and 469 seeded/truthiness/retained-alias contexts,
1,621 total, plus seven parsed source faults and artifact/hidden-checkout guards.
The added fault reverses wildcard/direct targets to distinguish their order.
The final driver checks the exact retained root-local lexical frame, dynamic
this, private names and Sets. Its function-table observation compares rendered
representations; formal frame lemmas use exact equality. These bounded
native/model/oracle comparisons do not establish universal native adequacy.
The walkthrough and 37-element rendered diagram were independently inspected;
the prose now correctly states that params reset precedes append.

The symbolic source-proof interfaces were inspected. `missing_satisfies` requires
only the actual declaration lookup and falsiness; `nonlast_satisfies` proves propagation
and live append. `direct_satisfies` covers the terminal path without a wildcard,
and `wildcard_satisfies` executes both actual call leaves using the derived
suffix facts. No successful suffix execution or desired capture is an entry
premise. The concrete owner reported the symbolic 80-job gate passed, and the
headline axiom guard retained only `propext`, `Classical.choice` and `Quot.sound`.

Review strengthened the terminal constructors to connect each row list to its
target's actual private methods storage. An unconstrained existential row list
could otherwise choose an empty trace despite a nonempty target. Direct storage
is now observed in the written state; the wildcard path observes wildcard
storage there and literal storage in the current state after the first call.
The proofs supply these derived facts as conclusions, without future-readiness
assumptions. The strengthened contract and constructor proofs were inspected,
and the owner reported the final 80-job gate passed again. No symbolic review
issue remains.

The nonempty examples were also inspected on disk. They execute parsed source
initialization, registration, an earlier separate source-202 seed, collector
allocation and the complete branch. Closed successful observations cover all
four paths and distinct wildcard/direct order. A shared-target example starts
with a live collector alias and proves that three entries observe the latest
params cell after two resets. A separate inhabited source-prepared domain proves
only initial structural facts, then invokes the universal wildcard theorem to
derive the second call's readiness. It contains no completed branch or future
capture premise.

The final witness factoring was reviewed. One compact initial endpoint is linked
to actual parsed preparation by the proved preamble, class definition, four
instances, two source histories and source-202 execution; ordinary child-map and
collector-prefix setup is then checked. The closed pipelines continue executing
parsed preparation directly. Reusing that source-linked endpoint for initial
domain facts changes proof normalization rather than the modeled input or
contract. The owner reported the final 95-job examples gate passed in 6.3 seconds,
checking all three public witnesses.

The parent reported the integrated root build passed all 357 jobs. Current
private-call and private-write regressions passed 908 and 3,800 contexts;
both adapter checks, the 468-lookup main comparison, three routing-worklist groups
and inventory byte checks also passed. The authoritative fresh root kernel replay
then exited successfully. The final routing-worklist rerun after registry links
passed all three groups.

The final seventeenth registry cluster and assumptions entry were independently
reviewed. Source spans, declaration references, row-storage requirements,
protected-domain restrictions and tooling/failure limits match the inspected
code. Original 30 assumption IDs/order/statuses/source-proof arrays and the
preceding 16 proof IDs/order remain intact, as do the 36 routing-worklist
units/order/statuses/summary. Unconditional runtime claims are
empty, full-runtime verification remains open and the goal remains active.
Target, generated coverage, restricted specification, D1 allowlist, comparison
baseline and historical benchmark artifacts have no diff. Final current generic,
symbolic, nonempty-witness, finite-suite, root-build and fresh-replay records all
reflect successful authoritative outcomes; the preceding checkpoint's build and
replay evidence remains historical. No unresolved issue remains in the declared
ordinary-owner/protected-layout domain.

Full traversal, native class/module/live-cell semantics, accessor/exotic effects
and complete language/host adequacy remain
open; this branch cannot establish whole-Hono correctness by itself.
