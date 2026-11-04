# Selected private helper calls: independent audit

This audit concerns Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, specifically the private
`#pushHandlerSets` declaration at `src/router/trie-router/node.ts:64–84`
and the selected call expressions at lines 115 and 191.

The source file SHA-256 is
`faa72577fbea974a954c6c0e36546e3f53da97418ae154d2583ae43de1e5a825`.
Source identity, parser equations, an executable call-entry interpretation and
the independent loop contract are separate links in the argument. Full class
evaluation, private-method installation and whole search traversal are not
established by parsing these fragments.

| Selected window | Byte range | SHA-256 |
| --- | --- | --- |
| Declaration 64–84 | `[1683,2430)` | `aad656effa61a33822d528bdc3f1f3f68eea9021fe3ea175e37f5c27563679b7` |
| Four-argument call 115 | `[3426,3505)` | `ce3913d56b66c42b121cd5f0d10b6083b1584359cfd0c50ab108d6c3bc95147d` |
| Reversed five-argument call 191 | `[5934,6020)` | `ebd420c64bfdfa25e03ba34e386950adaf48721d7a3c3abf71776af1e56cd82e` |

The [source record](../../verification/private-call/source.json) binds exact
indentation and trailing line feeds. The method's parsed body is checked
against the previously proved complete methods-loop AST; its signature and
selected callers now receive their own parsing checks.

## Fixed-edition call order

The review uses ECMA-262 2025. The
[call-expression rules](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-function-calls-runtime-semantics-evaluation)
evaluate the member reference and obtain its function value before entering
[EvaluateCall](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluatecall).
That operation takes the member receiver as the call's this value, evaluates
arguments in order, then checks callability. Consequently, a failed private
brand read precedes argument effects; a successfully read but noncallable
value is rejected after those effects. Receiver and callee identities must
remain captured even if argument evaluation later changes state.

[OrdinaryCallBindThis](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinarycallbindthis)
retains the supplied this value for strict methods. The
[function instantiation rules](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-functiondeclarationinstantiation)
give parameters positional argument values, using undefined when arguments
are absent. Extra arguments still evaluate even when no parameter receives
them. Parameter bindings shadow lexical captures. The private lexical
environment belongs to the function closure, rather than being taken from
arbitrary caller names.

TypeScript annotations, the optional `?` marker and the `void` result annotation
do not validate values at runtime. Normal fallthrough returns undefined;
`void` is not an instruction to erase an explicit returned value. Unsupported
default/rest/destructuring/duplicate parameters, generator/async methods and
full live lexical-cell behavior must remain visible parser/model boundaries.

## Independent native observations

An independent Bun 1.4.0 replay checked the exact pinned revision, clean
checkout, source SHA-256 and equality with `git show` before embedding the
actual selected method and two call expressions in explicit class scaffolding.
The supplied helper creates null-prototype output objects and the supplied
ALL binding is the string `ALL`; these are wrapper inputs, not proofs of module
linking or native class installation.

For two possible keys `id` and `second`, let the current node's params be
`{id: "old0", second: "old1"}` and the temporary params be
`{id: "temp0", second: "temp1"}`. The actual four-argument call at line 115
returns undefined and captures `old0`, `old1`. The actual reversed five-argument
call at line 191 returns undefined and captures `old0`, `temp1`. Both output
params objects have null prototypes. The distinction exercises positional
transport and the first-key precedence rule; an empty handler/key example
would not expose a swapped argument bug.

The independent wrapper input SHA-256 was
`47f02d5b618c957c90646be439ec5a76cc2e61a4a924cbfffea4d33cdca33dae`;
the emitted SHA-256 was
`6a2ae95476552238d046e8c4c7c5806cebc4c235a8eee250980d484bf1abdf8c`.
TypeScript transpilation remains explicitly unverified. An initial observer
assertion was corrected to distinguish null-prototype params from ordinary
objects; the final checks explicitly retain the prototype observation.

A separate generic native probe observed a bad private brand throw before any
argument effects. A valid call observed `arg0`, `arg1`, then `body`, and the
body's this identity equalled the captured receiver. These finite probes
support evaluation-order review; they do not establish general native language
adequacy or a partial exception-state semantics.

The landed [native harness](../../verification/private-call/native.ts) was also
independently replayed with a nonempty two-key reversed call and its scope
probes. All 315 pinned source/package blobs were checked. It retained the
existing collector prefix, appended the selected handler, produced the expected
two captures in a fresh null-prototype object, preserved rows/key arrays and
handler fields, returned undefined and retained outer scope. The scope probes
additionally retained a captured private data-field callee across an argument's
replacement and observed an argument effect before noncallability rejection.
That replacement probe concerns mutable private data, not writable private
methods. The harness input SHA-256 was
`0b2e846a7772927a8ed99e672e4bcc7a872eaf01338308c50283bc688661501a`;
its emitted SHA-256 was
`a7a785504aa5110b6bb0236a52352ea7d16a97c37363490cd3a02175027f194b`.
The separate source/artifact/Lean-embedding checker also passed independently.

## Restricted call-entry interpretation

The added method syntax and call runner leave the older expression/statement
interpreter unchanged. The new runner handles a selected top-level private
member call. It does not establish arbitrary nested block-method calls.
Its closure contains the parsed body, frozen lexical values and captured
private-name identities. The receiver's this value is carried separately from
ordinary lexical variables; this reads inside method bodies remain rejected
by this subset. The actual helper body needs none.

Private callability uses an explicit source-bound method table. Its function-ID
base must lie above the old zero-argument function table, preventing two
unrelated closure kinds from accidentally sharing one identity. Old function
IDs outside the admitted method table are unsupported entry cases, not proved
native noncallability errors. Likewise, private method creation, installation,
read-only enforcement and method-versus-data storage kinds remain open; the
supplied read handle does not prove those native class facts.

Successful invocation restores the post-argument caller environment and
private-name scope while preserving body heap effects. Missing arguments bind
undefined; provided arguments occupy parsed formal positions; no caller-local
name can substitute for a captured lexical/private binding. A body normal
completion returns undefined, and an explicit return keeps its actual value.
`Except` errors do not expose a partial state or prove rollback of prior effects.

Review identified a direct captured-lexical-write admission gap: copying a
captured numeric value into an activation cannot establish the native effects
of incrementing its shared lexical cell. The method parser now rejects such
direct increments throughout expressions, computed fields and nested statements,
including counted-loop increment names. Formal parameters shadow captures and
may use local increments. Same-spelling nested local/loop shadows of another
capture are conservatively rejected; no parser completeness claim is made.
Callbacks and captured bindings externally changed after closure creation still
require a live-cell interpretation. The actual Hono helper only reads its
stable admitted lexical captures.

## Implementation review status

The generic syntax/parser/runtime and concrete declaration/call parsing,
argument proofs, independent contract, complete loop composition and inhabited
examples have been reviewed. The proof requires initial reads, storage and the
previous protected structural Layout, rather than successful body execution,
a completed processing trace or desired output. It derives the parsed formal
bindings from the actual argument expressions, including omitted undefined and
the reversed parameter sources, then invokes the existing proved body and
restores the caller.

The nonempty closed examples use three distinct objects for root receiver,
target child and source parent. The caller lacks the `methods` private name,
while the closure carries its correct identity; captured ALL/helper bindings
also differ from caller guesses. Three rows combine a miss, GET hit and ALL
fallback, with two keys and a repeated handler reference. Closed observations
confirm the different positional captures and complete caller scope/private
restoration. The deliberately reduced caller private-name map is an inhabited
supported call-entry context, not a proved reachable same-class Node state;
actual same-class callsites share the full class lexical scope. Generic
witnesses also retain missing/extra argument behavior,
explicit return under void metadata, heap effects, captured private identities
and receiver effects before argument effects.

The additional `source_same_private_scope_control` repeats the nonempty direct
call with equal supplied caller/closure private-name maps. It preserves the
same captures and restores that shared map. The original different-scope
witness remains useful for closure transport; neither witness assumes or proves
surrounding whole-Node state reachability.

The root model driver, native harness, independent positional/capture oracle
and plain-English walkthrough were reviewed. The driver separates root,
parent and child owners and checks caller environment/private-name restoration.
Its mutation runner admits all available wrapper variable names; this test
domain is broader than each exact call theorem's lexical-name list. No exact
theorem was broadened to accommodate the deliberate faults.

The parent confirmed the complete five-group finite suite passed after the
captured-write guard change in 16.348 seconds: 518 exhaustive and 390
seeded/long contexts, totaling 908. Six parsed
source faults include altered loop/capture behavior, changed argument positions,
changed method and an explicit return value; two metadata controls preserve
runtime behavior. Source/artifact and hidden-checkout failures and native order
probes also passed. This suite result is attributed to the parent run, separate
from the independent native/source replays above.

The concrete owner confirmed the final focused
`lake build HonoLean.Upstream.NodePrivateCall.Examples` passed 39 jobs,
including the same-private-scope control, and source identity/embedding checks
passed. The parent then confirmed the integrated root `lake build` passed
293 jobs. The main comparison retained 468 lookups, 467 agreements, the exact
known D1 discrepancy and 98 append checks. The complete methods-loop regression
covered 1,942 contexts, routing's three groups passed, and the inventory byte
check remained unchanged. Adapter checks also passed, including 20 CLI
scenarios, 52 lookups, two append events, 30 rejection fixtures and 14 failed
registration sequences.

The parent confirmed `lake env leanchecker --fresh HonoLean` completed with
exit status zero. This fresh root replay checks the integrated proof
declarations in a fresh kernel environment. Final independent review found no
unresolved issue within the declared source/model domain. These build, replay
and finite-test results leave full class/private-method
installation, native activation, method writability/kinds, live module cells,
surrounding search traversal and complete language adequacy remain open.
