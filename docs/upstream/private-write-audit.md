# Private search assignments: independent audit

This audit concerns Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, specifically selected private
assignments in `src/router/trie-router/node.ts`. The source file SHA-256 is
`faa72577fbea974a954c6c0e36546e3f53da97418ae154d2583ae43de1e5a825`.

| Assignment | Lines | Byte range | SHA-256 |
| --- | --- | --- | --- |
| Reset receiver params | 88 | `[2539,2570)` | `9f81e8b0cb408a8680f18a02b03ff3bf13b2996460bf41e20bf0c3d5d747da80` |
| Propagate parent params | 109 | `[3163,3205)` | `9a559697c45a7065f1c521c2a8fea4b7ee6e527125976daeb4a27cc01deb7734` |
| Wildcard child params | 131 | `[4064,4103)` | `c74bf83ef2ca5c2c78d788c197fae28893f47bae7f93638e8ee5d78b767083a0` |
| Nonterminal parameter child params | 202 | `[6310,6347)` | `4a6a12c9332e95e96e5a60761ed021263bb4c191023ac0f0982f195aea516238` |

The two child assignments have the same expression but different indentation
and source positions. Line 202 belongs to the nonterminal branch, whereas the
five-argument call at line 191 belongs to the terminal branch. They must not be
presented as one contiguous executed branch. The literal-child propagation at
109 precedes the four-argument call at 115; the intervening last-component and
wildcard control flow needs its own proof or an explicit transport boundary.
The [source record](../../verification/private-write/source.json) and separate
Lean embeddings passed the identity checker independently.

## Fixed-edition assignment order

The review uses ECMA-262 2025. Its
[simple-assignment evaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-assignment-operators-runtime-semantics-evaluation)
obtains the left reference, evaluates the right expression and its value, then
performs PutValue. Successful assignment returns that right-hand value.

[MakePrivateReference](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-makeprivatereference)
resolves the private identifier using lexical private scope and retains it with
the evaluated base. It does not test the object's brand. The later
[PutValue](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-putvalue)
converts a property-reference base to an object and invokes PrivateSet for a
private reference. Thus a base-expression failure precedes the right expression,
but a successfully captured nullish, primitive or unbranded base can fail only
after right-hand evaluation. A changed variable or later lexical context must
not redirect the saved base/private identity.

[PrivateSet](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-privateset)
finds the object's own private element. A missing element rejects; a field's
value changes; a method rejects writes. An accessor uses its setter, or rejects
when it has none. Accessor execution remains unsupported unless explicitly
modeled. Ordinary property descriptors, inherited setters and extensibility
are not the dispatch mechanism for private field writes.

## Representation requirements

The implementation now uses one tagged private-element store with
data/method kinds and a computed value-only slots view for older read contracts.
There must be no independently mutable kind/value cache. Source field and method
installation must derive their respective tags. The old view must not be used
to rebuild live entries as data and thereby erase method kinds.

A field containing a function value remains writable. Read-only behavior must
come from the element's method kind, not from the value's function tag. Updating
a data field must retain its kind and all unrelated elements. Reads of both
supported kinds return their stored value.

Actual `this` needs a dedicated expression and dynamic context, not an ordinary
variable spelling. Method entry must bind that context and successful return
must restore the caller's context. Expression-only helper and field-initializer
contexts must remain fail-closed where their own `this` rules are not modeled.

The core implementation has been reviewed on disk: private reads use the
computed value view; private writes inspect the tagged store after right-hand
effects; only the first matching owner/element is replaced. The saved reference
contains a resolved identity, so PutValue does not consult later lexical names.
The shared assignment evaluator dispatches ordinary and private references
explicitly. These mechanics have no remaining semantic review issue so far;
final integration and fresh-replay evidence remain pending below.

Method call arguments retain their previous rejection of `this`. This avoids
conflating the older explicit call-entry context with the newly represented
dynamic State context. Method bodies can use the latter because entry installs
the receiver and successful return restores the caller. This remains an explicit
call-entry extension, with general nested block-method dispatch still open.

## Independent native boundary probes

A direct JavaScript probe ran with Bun 1.4.0 after checking the exact clean pin
and all 315 source/package blobs. It used plain JavaScript class syntax to avoid
using a TypeScript read-only diagnostic as runtime evidence. These are finite
language observations, separate from the Lean proofs:

- Data writes returned and retained undefined, null, false, zero, empty string
  and a number. A data field containing a function could then be overwritten.
- Nullish, primitive, unbranded, prototype-clone and proxy bases ran the right
  expression before rejecting. A private-method write did likewise and retained
  the original method value.
- Private field writes succeeded on a frozen ordinary branded object with a
  public nonwritable shadow and an inherited setter. The public property and
  setter counter were unchanged.
- A right expression rebinding the local target did not redirect the captured
  write: the original object's field became nine; the second stayed zero.

The first draft probe accidentally threw a right-expression ReferenceError;
that typo was corrected before the above successful run was recorded. Existing
`Except` results do not expose partial failure heaps or callback traces, so
these observations do not establish a formal failure-state or rollback theorem.
The model's private failure tags are coarse errors, not native exception objects
or a proof of primitive boxing, proxy behavior or exotic-owner interpretation.

An additional independent wrapper executed the exact pinned preamble, selected
data fields, private method, registration push, collector, all four assignment
windows and call 115, importing the pinned helper and ALL binding. It checked
the same clean revision, Bun 1.4.0 and all 315 blobs. Nine right-hand value kinds,
including function/array/object references, copied without a runtime shape test.
Propagation retained the exact shared object; reset replaced the destination
reference without changing that old object. Three registrations produced ordered
GET and ALL hits with two captures, scores one/two and final order three, while
the method value stayed identical.

The wrapper's input SHA-256 was
`3f67ad7a2f78aee2af3e17578d8b44607f753a9c197aa71b57191cc9874a9486`;
the emitted SHA-256 was
`2b4a99e11a7654aeefc0d474e9c7230420e03f5d136157ed36777c48b15e113f`.
TypeScript transpilation is explicitly unverified. The selected source operations
run in separate explicit wrapper activations; this does not prove intervening
search branches or full native module/class/caller linkage.

The landed finite harness was also reviewed independently, including its Lean
driver and external observation oracle. Input initialization uses a separate
canonical source assignment, so mutation controls cannot corrupt their own
starting state. A four-case native replay checked function-valued data updates,
propagation, reset and foreign-brand rejection. Successful writes retained the
private method and ordinary shadow descriptors on frozen objects. Its wrapper
input SHA-256 was
`e9e30db7ea29d27cfdc8db247c0a7b74414260648eaf78077cab5c8e91490b05`;
the emitted SHA-256 was
`be0488b52488ae13ebc34ff86f6279ec6d4b4a4219cdf56574637efe25e615b5`.
This wrapper explicitly records unverified TypeScript erasure and plain-JavaScript
assignment insertion. Invalid-owner observations record rejection only, without
a claim about the native exception's identity or failed-state contents.

## Review status

Architecture, fixed-edition ordering, tagged storage, dynamic-this mechanics,
generic raw-frame contract and concrete leaf source contracts have been
reviewed. The concrete prefix/suffix replacement relations preserve every
unrelated raw kind/value, and the source assignments return the arbitrary input
value without a TypeScript shape guard. The initialized-data and read-only-method
claims derive their kinds from the source class's tagged instance contract.
The generic contract also states that its incoming target is data. Its incoming
state is the state at PutValue, after right-hand effects; this adds no early
brand or kind check when the left reference is captured.

The final concrete examples and flow theorem have been reviewed on disk. The
positive example starts from parsed source initialization and three parsed
registrations, executes reset 88 and an earlier separate activation of 202, then
propagation 109 and call 115. It explicitly requires a successful result with
nonempty captures, so agreement between two failures cannot satisfy the check.
The composition derives callable/storage/layout conditions after propagation;
the branch-selection and intervening wildcard path remain outer obligations.
The rendered diagram was visually inspected and reflects this write ordering
and kind distinction.

Generic examples have also been inspected: data-function versus method kind,
saved base and identity, right-expression error priority, nonextensible owner
frames, dynamic-this spoof resistance/restoration and a parsed method body
containing a private assignment. The generic implementation owner reported the
final `SourceSubset.PrivateWriteExamples` focused build passed 16 jobs in 13
seconds, after the core build passed 18 jobs. These are attributed focused
outcomes; they do not imply an integrated build or fresh replay.
That final generic gate includes the explicit incoming DATA-kind condition.

The concrete implementation owner reported a final focused 83-job build passed,
including the migrated class, initialization and call proofs, new assignment
proofs, source composition and all three public example witnesses. The final
private-write source/embedding checker was independently rerun successfully
after the containing-method range correction to lines 86–220.

The parent reported the integrated managed root build passed all 329 jobs after
the tagged-store/AST/state migration and final generic-contract strengthening.
The independent fresh kernel replay then exited successfully. The migrated
private-call finite suite also passed its 908 contexts in five test groups.
The final private-write finite suite passed four groups in 8.078 seconds:
3,380 exhaustive value/alias/frozen contexts plus 420 seeded and brand-boundary
contexts, seven supported source faults, and source/artifact/hidden-checkout
identity guards. These 3,800 bounded observations compare the pinned native
assignments, parsed model and independent oracle; they do not discharge native
adequacy. Migration regressions were rerun separately from that new suite.
The parent reported all changed
driver regressions passed: class installation 1,418 contexts, Node initialization
472, methods push 643, search entry 6,452, methods loop 1,942 and its initial-state
suite 1,040. The earlier private-call suite's 908 contexts passed as noted above.
The main comparison retained 467 agreements in 468 lookups with only the exact
D1 allowlisted divergence. Adapter checks, 13 inventory fixtures, the byte check
and three routing-worklist groups also passed.

Final ledger review passed. The sixteenth source cluster remains conditional;
its source spans, declaration references, domains and explicit adequacy limits
match the reviewed code and evidence. The original 30 assumption IDs, order,
statuses and source-proof arrays are unchanged, as are the preceding 15 proof
IDs/order and 36 routing-worklist units/statuses/summary. The target, generated
coverage, restricted specification, D1 allowlist, comparison baseline and
historical benchmark artifacts have no diff. Unconditional runtime claims remain
empty, full-runtime verification remains open, and the goal remains active.
No unresolved review issue remains within the declared DATA/METHOD ordinary-owner
domain.

Full search traversal/control flow, complete class/module/native function
semantics, live cells, accessors, exotics and complete native language/host
adequacy remain separate obligations. No whole-Hono correctness claim follows
from the selected assignments.
