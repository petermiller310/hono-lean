# Loop-header entry audit

This milestone is a conditional source-subset result for Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. Whole search, complete routing and
the fixed published runtime catalog remain open.

## Exact source prefixes

The new source checker binds two prefixes, each ending immediately after the
actual opening brace line:

| Prefix | Source line | Bytes | SHA-256 |
| --- | --- | --- | --- |
| Outer |99|`[2850,2886)`|`0a355c4f0b0a29e3b1830752b8a4bb8dd57296688128e0228af0ef24fc42bd8e`|
| Inner |104|`[2996,3059)`|`3f6a1b09b9e96fb41991a75c0aab547243e2e1a9bbb85c4d057a3aa17979b128`|

`verification/loop-entry/source.py` checks clean pin, Git/working bytes, full
file/blob identity, exact spans/hashes, source copies, metadata and Lean
embedding. Indentation and final LF are retained. Lean parses the whole prefix
through `{` and EOF. No body or closing brace is inserted into source parsing.

The parser uses an empty `Stmt.countedFor` value solely to reuse existing
binding/TDZ admission rules. That value is neither parsed as a fabricated source
body nor executed. Actual startup 87–97, body declarations 100–102 and first 105
reuse their earlier source bindings. The selected continuation is explicit;
unsupported remainder is not represented by a silently successful empty body.

## Header and prefix contracts

Header entry first removes all newly declared names, then uses sequential
`initializeBindings`. The test evaluates the actual condition once and retains
its resulting state. Update uses `incrementVariable`, discarding the unused
postfix result. There is no general leave/restore operation that could erase a
mutable outer `curNodes` write.

The generic guard relation independently separates true/counter-below-bound
from false/bound-at-most-counter. Increment uses a first-binding replacement
relation and frames other bindings/heap/object/private/function/Set/this state.
The pure entry frame theorem is restricted to numeric literal initializers;
general admitted initializer/condition expressions may have effects and retain
them. Exact source header 104 has a separate proof of its current-array length
read and unchanged state.

The concrete universal prefix starts with the earlier startup Inputs, not
supplied i/j, a completed header, chosen guard values or a future indexed-read
result. Actual header 99 derives 0 and its guard; a nonempty source-produced
parts array admits 100–102. Actual 104 then derives j0/saved len 2=1 from the
source-produced singleton array, tests true and admits 105. Empty parts skip
all body initialization and preserve the four startup arrays.

That empty prefix state is immediately after the false guard and still has
the modeled i binding. Native lexical-scope exit/completion has not been proved.
The finite native wrapper observes no header environment at its outside-loop
false endpoint. Its agreement cannot close that environment boundary.

Progress theorems operate on a supplied current header state after a body has
finished. They do not prove that the complete Hono body reaches that point.
Saved numeric bounds do not imply current array bounds. The separate current
parts theorem requires actual current array/binding facts before another read;
the first-entry theorem derives those facts from source execution.

## ECMAScript reference audit

The primary reference is ECMA-2622025:

- [ForLoopEvaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-runtime-semantics-forloopevaluation)
  creates the loop's lexical bindings before declaration-list initialization.
- [ForBodyEvaluation](https://tc39.es/ecma262/2025/multipage/ecmascript-language-statements-and-declarations.html#sec-forbodyevaluation)
  tests before executing a body and evaluates update afterward, with native
  per-iteration environments and completion handling.
- [Postfix increment](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-postfix-increment-operator)
  writes the new numeric value while returning the old one. This source ignores
  that result. No LineTerminator may separate operand and postfix operator.

The model has no general native per-iteration cell/closure/completion theorem.
Canonical reachable counters are nonnegative and UInt32-bounded; explicit
operand/result safe bounds support the integer specialization. Fractions,
negative-zero identity, coercion/BigInt, NaN/infinities and unsafe rounding remain
outside that interpretation. Native probes preserve unsafe-stall, signed-zero
and string-coercion observations rather than silently extending the model.

## Conformance and mutation design

The native runner checks all 315 pinned source/package blobs and inserts the
exact two headers into explicitly unverified observation bodies. The main
wrapper executes actual startup 87–97 and 100–102/105 prefixes and returns from the first
observed inner entry; it does not reach either postfix increment there. The
model Driver dispatches the actual parsed headers and the same selected source
operations, reading generated bindings/heap cells. No prepared index is supplied.

Separate header probes execute controlled fixture bodies with keep/grow/shrink
actions before advancing and retesting. Their trace cap prevents a deliberately
faulted bound-increment loop from hanging. They demonstrate saved length/current
array divergence without assuming those fixture bodies are Hono's source suffix.
The oracle scans UTF16 delimiters and constructs finite counter traces
independently.

Faults change outer initialization/guard, inner initialization/saved length,
inner comparison and update target. Both `j <= len2` and `len2++` leave the
first-entry observation unchanged; the tests explicitly require their detection
through the controlled progress probes. They are not called first-prefix
behavioral counterexamples. Newline-after-++ and multiline initializer controls
retain behavior; newline-before-++, body/closing-brace suffixes and stale source
artifacts reject.

## Checked declarations and replay

The headline `NodeLoopEntry.source_prefix_satisfies` theorem couples the actual
parsed startup/header/declaration continuation to independent `PrefixContract`.
`empty_skips_body_allocation` exposes the four-array empty endpoint.
`inner_progress` and `outer_progress` establish separate current-state
update/guard effects; `outer_progress_with_current_parts` additionally requires
the current array/binding before proving a subsequent actual part read.

The source-prepared family
`Examples.source_prepared_input_has_universal_header_prefix_contract` establishes
an inhabited initial domain for every mathematical path. Its bridge parses
actual preamble/class/two owners/registration/source202 stale params/splitPath,
then uses the universal theorem. No generated parts/nodes/collector/indices are
staged. The other five public witnesses retain empty/no-body behavior,
trailing/rawUTF16 data, full first shared-handler literal fragment after both
headers, and explicitly controlled saved-array growth/shrink facts. Opaque
object references in the controlled fixtures have allocated object cells.

The final generic managed gate passed 17 jobs in7.4 seconds, the concrete
symbolic gate 102 jobs, and strengthened source-prepared Examples 117 jobs in2.2
seconds. Both headline axiom guards contain only `propext`, `Classical.choice`
and `Quot.sound`. All 41 new registry declarations were checked in the actual
imported Lean environment. The integrated root build passed 409 jobs. Fresh
root kernel replay 90663 completed exit 0 after that409-job build.

The new six-group suite passed in11.654 seconds:1,365 exhaustive first-entry
paths plus 260 seeded/repeated/empty/old-state contexts and 60 controlled header
progress probes, totaling 1,685. Eight header faults were detected with the
two probe-only distinctions above; positive/negative grammar and source/hidden
edit controls passed. The committed six native boundary groups passed in both
Bun1.4.0 and Node22.22.2, using portable PATH or `HONO_NODE` resolution.

Native wrapper input/emitted SHA-256 values are
`5a12202d2351a3b47ba085ce8bf787d2b9225903af3caf778e9adb68f3df3c50`
and `132afc11d194f523cf0d275afe9d08db2c76454bbb89263eb4100d37897744df`.
The separate controlled-probe input/emitted hashes are
`6e52ba09006f292d15278b16a8b502f1f4d9aff647cd9fd65f758ac3e7c6449c`
and `46ea00fee567743b00edbdff23a3c0c81f6ade3d367f6d14379db9510eb66830`.
These identify unverified evidence wrappers, not proved emitted artifacts.

Existing startup revalidation passed 1,760 contexts/5 groups in9.505 seconds.
The main comparison retains 467 agreements and the same one exact D1 discrepancy
across 468 lookups and 98 appends, with zero unexpected failures. The structural
inventory is byte-identical and still records zero unconditional source runtime
theorems. Updated routing evidence passed 3 groups in1.458 seconds; all 36
complete routing behavior units remain unresolved. Remote CI/npm installation
was not newly observed.

Initial generic example elaboration needed constructor reflexivity for
Int/UInt16 forms and expected axiom-output wrapping. Concrete symbolic proofs
needed alias/Except normalization and an Int/Nat comparison bridge. The first
concrete Examples gate passed; a final fixture-only improvement allocated its
opaque objects and retained every assertion. No domain/case was weakened or
removed, and no runtime/parser/Expr/Stmt/State ABI was changed. Independent
review found no semantic/scope issue in the source contracts, all witnesses,
harness/oracle, numeric/lexical boundaries or27-element diagram. Final fresh
replay,41-name actual-environment audit and ledger reconciliation passed. The
original 30 assumption IDs/order/status/source-proof arrays, historical 19 proof
clusters, fixed 36 routing-unit statuses/summary, SPEC/target/coverage/baseline/D1
and empty unconditional claims remain intact. The goal stays active.
