# Search iteration setup: independent audit

This review concerns Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52` and three selected windows in
`src/router/trie-router/node.ts`. The file SHA-256 is
`faa72577fbea974a954c6c0e36546e3f53da97418ae154d2583ae43de1e5a825`.

| Window | Lines | Bytes | SHA-256 |
| --- | --- | --- | --- |
| Saved length and offsets | 96–97 | `[2776,2849)` | `21008e5f4fa8f4fe06a6d57e9818519e9a92eb1233dcd997b99a872f955e7e22` |
| Part, last flag and fresh queue | 100–102 | `[2886,2995)` | `40c7e7effca1b775dd2e2a888512bf4de6cae3afdcc299a12960de1ab70163e1` |
| Current node and literal branch | 105–119 | `[3059,3583)` | `5b81e8170de12ec41069162ef15577a30aa7f65139f19710639dba044aee3680` |

These are separate activations. The omitted loop headers at 99 and 104 are not
parsed or executed by pasting these windows together. They still supply the
counter bindings and leave loop reachability, repeated-iteration transport and
the saved `len2` protocol open. The final window extends the earlier
[literal-child audit](literal-branch-audit.md) by deriving `node` from the current
array entry.
The [source record](../../verification/iteration-setup/source.json), three copied
windows and Lean embeddings independently passed the identity checker.

## Arithmetic interpretation

The review uses ECMA-262 2025. Its
[binary evaluation rule](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-evaluatestringornumericbinaryexpression)
obtains the left value, then the right value, before applying the operator.
[Number subtraction](https://tc39.es/ecma262/2025/multipage/ecmascript-data-types-and-values.html#sec-numeric-types-number-subtract)
uses addition with the negated right operand. The generic model instead
specializes to mathematical integers after both operand effects. Its independent
`Difference` relation requires that adding back the subtrahend recover the
minuend; it does not mention the evaluator.

The native interpretation requires both operands and their exact difference to
fit the safe integral range. Safe operands alone are insufficient. The model
continues computing mathematical integers outside that boundary; it does not
silently prove native rounding, ToNumeric/coercion, fractions, infinities, NaN,
BigInt or negative-zero identity. The selected array-length domain makes
`len - 1` range from minus one upward within the bound. In particular, zero
length must produce `-1`, never saturating natural subtraction. Ordinary source
lengths and nonnegative integral loop counters avoid negative-zero generation;
the equal-operands length-one case produces positive zero natively.

Subtraction belongs above comparison/equality and folds left. Parentheses can
change that grouping. ECMAScript's
[longest-token rule](https://tc39.es/ecma262/2025/multipage/ecmascript-language-lexical-grammar.html#sec-tokens)
makes adjacent `--` a decrement token, which remains unsupported; it cannot be
reinterpreted as subtraction followed by unary minus. Separated negative
literals and operator continuations across newlines retain their supported
meaning, while return ASI remains conservative.

The new expression constructor changes the Expr ABI. Shared parsers and all
binding/private/capture/initializer/control walkers must recurse through both
operands. A coherent rebuild is required before any cached model driver can
count as conformance evidence.

## Independent setup requirements

The search window saves `parts.length` once and initializes `partOffsets` to
null. A later `parts[i]` reads the array's current contents; `isLast` compares
`i` against the saved length minus one. Likewise `curNodes[j]` reads its current
array. A bound against an earlier `len2` does not establish that the current
array still contains that entry without a preservation argument.

The setup contract must derive the actual part, Boolean last flag, fresh queue
and current node from initial arrays, current reads and explicit bounds. The
part is an arbitrary UTF-16 string, including empty strings and lone surrogates.
It must not be replaced by a preselected desired child or an input `isLast`.
Out-of-bounds indexing itself returns undefined natively; a subsequent private
access on an absent node fails, while an undefined part can still select a
public child-map key after native key conversion. The success domain therefore
needs its precise read/type bounds rather than a blanket native rejection claim.

The empty queue literal allocates at the prior array-heap length. Initial valid
collector/method/key-array references lie below that length, so queue separation
and empty capacity can be derived. Every old array cell and ordinary/private
state must be framed through that allocation. The existing protected capture
layout must then be transported to the derived bindings and fresh heap; no
post-setup layout, future execution or expected captures may be an input.

Those old-array frames concern setup allocation. The full branch contract still
permits collector mutations: if an abstract initial collector aliases parts or
curNodes, later appends can affect that alias. The native fixture allocates these
arrays separately and observes them unchanged; that observation is not a general
whole-branch input-array frame without separation.

The final entry must connect all four literal-branch contracts, retaining the
current actual row-storage witnesses and sequential wildcard/direct behavior.
A nonempty source-prepared shared-handler example must instantiate that domain
rather than only compare two failures or suppress the wildcard path.

## Independent finite observations

A separate native wrapper executed the three exact windows as separate
activations, with pinned preamble/fields/helper, registration and source-202
preparation. It guarded the clean exact revision, Bun 1.4.0 and all 315
source/package blobs. Sixteen grouped observations passed:

- The saved length stayed one while a later parts read observed changed array
  contents and a new length. Each setup produced a distinct empty queue.
- Zero-length setup compared index zero against minus one and returned false.
  An out-of-bounds part read returned undefined; an explicitly supplied
  `children['undefined']` entry could still match and enqueue normally.
- A part getter ran before subtraction coercion. Current `curNodes[j]` followed
  replaced contents despite an earlier saved length, read its indexed getter
  once, and failed after truncation. Negative ordinary property indices remain
  a separate native boundary rather than a modeled dense-index theorem.
- Empty and lone-surrogate parts retained exact contents. Nonempty wildcard and
  direct registrations produced their actual intermediate call order and
  captures after the setup-derived last flag.
- Separate operator probes confirmed left-to-right operand evaluation before
  coercion, left associativity, negative-zero distinction, unsafe-result
  rounding, decrement tokenization and newline continuation.

The wrapper input SHA-256 was
`0bd121a195778e6d50e6eb11f192779344963d7fa16c94c7c904d2edacd0c52a`;
the emitted SHA-256 was
`ba7cc358d44bbdbc4777ff7349dbf7f32d5a2cc4b89ce4c96b5c4e17d7319d7a`.
Wrapper construction, TypeScript erasure and supplied child maps are unverified
tooling. Getter/coercion/current-array probes expose boundary behavior rather
than proving native accessors, exotics, omitted-loop reachability or error-state
traces.

An independent cached TypeScript 6.0.3 AST probe ran with Node 22.22.2. Supported
subtraction/parentheses/assertion/equality/newline shapes matched the proposed
Lean ASTs. Valid TypeScript mixes that require resuming arithmetic after an
unparenthesized assertion are deliberately rejected by the specialized parser.
This finite grammar comparison is not a full frontend or type-erasure theorem.

The expanded finite corpus exposed an independent oracle error inherited from
the literal-branch runner: a four-argument helper has no fifth params argument,
so a null node value falls through `??` to undefined. Both finite oracles were
corrected to map only null/undefined to undefined while preserving false, zero
and empty string. Eight focused controls were added to each suite. Independent
native/oracle replays passed all eight in each runner, including own undefined
output properties. This changes the test oracle, not Hono or the formal source
semantics. Historical 1,621-case literal evidence remains historical; its new
1,629-case revalidation is distinct and subsequently passed all four groups.

The landed setup runner/oracle were inspected: canonical input maps and the
source-202 seed are independent of operation faults, the setup/entry windows
remain separate activations, and observers retain fresh queues and live record
identities. Its current wrapper input SHA-256 was
`440e6a2151b3fe1758cbcff762db7dd0b5c82163be4fde6ef6968bea00e169b9`;
the emitted SHA-256 was
`cdd6f398e3ceccdc3bcd3ccdff3f10df04164ee9cae906d6c7299b0a3a903610`.
Native/oracle-only evidence is separate from model conformance.

## Review status

The initial arithmetic semantics, independent difference/boundary contract,
precedence/associativity/maximal-munch changes and recursive admission walkers
were inspected. The implementation owner reported the final 22-job core and
generic regression gate passed, including arithmetic examples and prior
private-control/private-write checks. The initial coherent build exposed old
rejection fixtures for newline subtraction that became valid with the new
operator. Those controls now use unsupported multiplication, alongside positive
parsing/full-consumption/runtime subtraction checks. Their migration was
reviewed; source truncation is still rejected. The parent reported the coherent
existing-root/arithmetic build passed 361 jobs after these repairs. No model
driver or native/model comparison was counted before that coherent Expr rebuild.

The concrete interfaces were inspected: the actual dense input arrays and
bounds determine selected strings/nodes, the source executions expose distinct
counter activations, and fresh-array transport derives old-cell frames, initial
layout preservation and queue separation/capacity. They supply no desired local
bindings or future execution. Their selected activation protocol preserves arrays
between windows; it does not assert arbitrary intervening mutation or whole-loop
reachability.

Review flagged one frontend dependency before the concrete gate: the retained
`number[] | null` annotation at 97 requires null in the type-name admission list.
The existing runtime null value was already modeled. The coordinated type-name
whitelist addition and exact nullable-array regression were inspected and are
included in the coherent build; binding-name admission and runtime null semantics
remain unchanged.

The final symbolic interfaces were inspected and the concrete owner reported its
88-job gate passed. Four public source theorems cover missing, nonlast, direct
and wildcard-plus-direct outcomes. Their inputs contain current arrays/bounds
and initial structural lookup/call/layout facts; generated local bindings,
post-allocation layout, queue separation and empty capacity are derived. The
headline axiom guard reports only `propext`, `Classical.choice` and `Quot.sound`.

The final examples were reviewed. They construct supplied arrays through
parsed literals, explicitly leaving splitPath/traversal production open, then
execute all three source windows. Nonzero indices cover all four paths, separate
controls change the actual selected entries, and a shared target/live prefix
observes the latest params reset. A compact initial-state equality connects
parsed source initialization, registration, source-202 preparation, arrays and
collector before proving initial domain facts. The universal witness supplies no
generated bindings, completed branch or later readiness.

The final compiled examples and preparation bridge were inspected. The owner
reported the 103-job gate passed in 10 seconds, checking all five public
witnesses. The final normalization repair added explicit reflexivity for ground
Int literal observations without changing their source execution or claims.

The parent reported authoritative full conformance passed four groups in 25.344
seconds: 2,592 exhaustive and 399 seeded/index/UTF-16/alias contexts, 2,991 total,
with eight supported source faults, two metadata-erasure controls and freshness
guards. These compare native execution, parsed model and the corrected
independent oracle after the coherent 361-job rebuild. Current regressions also
passed: literal branch 1,629 contexts, private call 908, private write 3,800,
querystrings 4,858 generated plus 1,050 signed-operation cases, and null-object
allocation/transfer/D1 controls. These are finite observations, not a native
Number/frontend/engine adequacy theorem.

The parent reported the final integrated root build passed all 377 jobs. The
authoritative fresh root kernel replay then exited successfully. The final
routing-worklist rerun passed all three groups after the eighteenth cluster's
evidence links. The 22-element diagram and walkthrough were inspected for
source-window, numeric, array-alias and activation boundaries.

Final ledger review preserved the original 30 assumption IDs/order/statuses and
source-proof arrays, the preceding 17 proof IDs/order, empty unconditional
runtime claims and the active full-runtime goal. All 36 routing-worklist
units/order/nested statuses/summary remain intact. The eighteenth source cluster
retains all three exact spans and explicit Number/loop/native adequacy limits.
Review corrected evaluator lemma references to their actual SourceSubset
namespace; the parent also checked all 30 new declaration names in the actual
Lean environment. Evidence paths and local document links were checked. Target,
generated coverage, restricted specification, D1 allowlist, comparison baseline
and historical benchmarks remain unchanged. All current gates have passed. No
unresolved review issue remains in the declared dense-array/protected-layout
domain.

All published runtime scope, full traversal, native class/module/live cells,
Number/frontend/host adequacy and unconditional-runtime obligations remain open.
