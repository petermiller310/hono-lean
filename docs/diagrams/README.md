# Router diagrams

The matching proof diagram covers literal paths, method matching and `ALL`,
named parameters with capture, and terminal wildcards. The request diagram
keeps a smaller example without wildcards. Two more diagrams explain persistent
router versions and the incremental-registration invariant. Two adapter diagrams
show the tested input/output boundary and failed-registration behavior. The
comparison diagrams add the pinned differential-testing flow and the exact D1
exception. Benchmark diagrams separate the timed phases and illustrate output
cardinality. Two path-parser diagrams explain the soundness/completeness
equivalence and its relationship to the typed router. The
method-parser diagrams explain exact method acceptance and the separate role of
the reserved route selector `ALL`. The pattern diagram explains exact components,
suffix and name uniqueness; the five-milestone map tracks the current goal. The
[project README](../../README.md) embeds the request and version examples and
explains the current proof boundary.

| Diagram | Preview | Editable source |
| --- | --- | --- |
| Lookahead checks text without consuming it | [PNG](getpattern-lookahead.png) | [Excalidraw](getpattern-lookahead.excalidraw) |
| One request through the trie | [PNG](router-request.png) | [Excalidraw](router-request.excalidraw) |
| What the correctness proof establishes | [PNG](correctness-proof.png) | [Excalidraw](correctness-proof.excalidraw) |
| Registration creates a new router version | [PNG](registration-versions.png) | [Excalidraw](registration-versions.excalidraw) |
| Why incremental registration follows the rules | [PNG](registration-proof.png) | [Excalidraw](registration-proof.excalidraw) |
| Method parsing, path parsing, and the core | [PNG](adapter-boundary.png) | [Excalidraw](adapter-boundary.excalidraw) |
| A rejected route does not consume a number | [PNG](adapter-failure.png) | [Excalidraw](adapter-failure.excalidraw) |
| What the pinned Hono comparison checks | [PNG](comparison-harness.png) | [Excalidraw](comparison-harness.excalidraw) |
| One exact D1 difference | [PNG](comparison-d1.png) | [Excalidraw](comparison-d1.excalidraw) |
| Measure construction and lookup separately | [PNG](benchmark-timers.png) | [Excalidraw](benchmark-timers.excalidraw) |
| Same route count, different matching work | [PNG](benchmark-workloads.png) | [Excalidraw](benchmark-workloads.excalidraw) |
| One path grammar, two proof directions | [PNG](path-parser-equivalence.png) | [Excalidraw](path-parser-equivalence.excalidraw) |
| The path proof reaches the router's input | [PNG](path-parser-boundary.png) | [Excalidraw](path-parser-boundary.excalidraw) |
| Methods: exact acceptance and spelling | [PNG](method-parser-contract.png) | [Excalidraw](method-parser-contract.excalidraw) |
| ALL is a route selector | [PNG](method-parser-all.png) | [Excalidraw](method-parser-all.excalidraw) |
| A pattern has structure | [PNG](pattern-parser-contract.png) | [Excalidraw](pattern-parser-contract.excalidraw) |
| Five milestones to text matching | [PNG](text-boundary-goal.png) | [Excalidraw](text-boundary-goal.excalidraw) |
| One record, three field promises | [PNG](record-parser-contract.png) | [Excalidraw](record-parser-contract.excalidraw) |
| Initial build is all or nothing | [PNG](text-build-contract.png) | [Excalidraw](text-build-contract.excalidraw) |
| Rejected registration keeps the exact router | [PNG](text-registration-contract.png) | [Excalidraw](text-registration-contract.excalidraw) |
| Text inputs meet the matching rules | [PNG](text-lookup-contract.png) | [Excalidraw](text-lookup-contract.excalidraw) |
| Long-running Hono verification program | [PNG](hono-verification-program.png) | [Excalidraw](hono-verification-program.excalidraw) |
| splitPath: source, proof and remaining boundary | [PNG](splitpath-source-bridge.png) | [Excalidraw](splitpath-source-bridge.excalidraw) |
| Why shift needs a heap | [PNG](ecma2025-shift-steps.png) | [Excalidraw](ecma2025-shift-steps.excalidraw) |
| Raw query extraction starts at offset 8 | [PNG](querystrings-contract.png) | [Excalidraw](querystrings-contract.excalidraw) |
| D1: inherited setter and null-prototype output | [PNG](d1-object-mechanism.png) | [Excalidraw](d1-object-mechanism.excalidraw) |
| One actual Hono parameter assignment | [PNG](param-assignment-contract.png) | [Excalidraw](param-assignment-contract.excalidraw) |
| Reset, append and the key-prefix invariant | [PNG](param-loop-contract.png) | [Excalidraw](param-loop-contract.excalidraw) |
| Set first occurrences and snapshot handoff | [PNG](key-set-producer.png) | [Excalidraw](key-set-producer.excalidraw) |
| Actual handler-record construction and loop facts | [PNG](handler-record.png) | [Excalidraw](handler-record.excalidraw) |
| Private methods-array call and stored references | [PNG](methods-push.png) | [Excalidraw](methods-push.excalidraw) |
| Later collector and lazy method/ALL selection | [PNG](search-entry.png) | [Excalidraw](search-entry.excalidraw) |
| Ordered method-row visits and shared handler references | [PNG](methods-loop.png) | [Excalidraw](methods-loop.excalidraw) |
| Initial protected layout derives loop readiness | [PNG](methods-loop-initial.png) | [Excalidraw](methods-loop-initial.excalidraw) |
| Registration histories and fresh records for equal handlers | [PNG](registration-history.png) | [Excalidraw](registration-history.excalidraw) |
| Fresh instance data, shared initial params | [PNG](node-initialization.png) | [Excalidraw](node-initialization.excalidraw) |
| From actual private call to capture loop | [PNG](private-call.png) | [Excalidraw](private-call.excalidraw) |
| Shared method value, fresh instance data | [PNG](class-installation.png) | [Excalidraw](class-installation.excalidraw) |
| Private writes preserve DATA/METHOD kind | [PNG](private-write.png) | [Excalidraw](private-write.excalidraw) |
| Literal-child branch and live handler records | [PNG](literal-branch.png) | [Excalidraw](literal-branch.excalidraw) |
| Source setup derives branch inputs and fresh queue | [PNG](iteration-setup.png) | [Excalidraw](iteration-setup.excalidraw) |
| Search startup calls the actual path-array producer | [PNG](search-setup.png) | [Excalidraw](search-setup.excalidraw) |
| The loop headers derive the first indices | [PNG](loop-entry.png) | [Excalidraw](loop-entry.excalidraw) |
| The first literal branch follows from initial facts | [PNG](first-literal.png) | [Excalidraw](first-literal.excalidraw) |
| Queue advance: mutation, identity and order | [PNG](queue-advance.png) | [Excalidraw](queue-advance.excalidraw) |
| Sparse scheduling and the read-value bridge | [PNG](queue-schedule.png) | [Excalidraw](queue-schedule.excalidraw) |
| Slash count to sparse scheduling | [PNG](component-count.png) | [Excalidraw](component-count.excalidraw) |
| Why the child loop schedules at most once | [PNG](child-enumeration.png) | [Excalidraw](child-enumeration.excalidraw) |
| Building and reusing segment starts | [PNG](part-offsets.png) | [Excalidraw](part-offsets.excalidraw) |
| Guarded capture and inherited write behavior | [PNG](capture-guard.png) | [Excalidraw](capture-guard.excalidraw) |
| Fresh params and shallow own-data copying | [PNG](params-init.png) | [Excalidraw](params-init.excalidraw) |
| Builtin regex computes the capture | [PNG](builtin-exec.png) | [Excalidraw](builtin-exec.excalidraw) |
| Hono constructs the matcher | [PNG](pattern-construct.png) | [Excalidraw](pattern-construct.excalidraw) |
| A tuple becomes actual matcher bindings | [PNG](pattern-binding.png) | [Excalidraw](pattern-binding.excalidraw) |
| Hono derives raw label captures | [PNG](label-match.png) | [Excalidraw](label-match.excalidraw) |
| Persistent cache collisions retain the first tuple | [PNG](getpattern-cache.png) | [Excalidraw](getpattern-cache.excalidraw) |
| Terminal construction, storage and same-object reuse | [PNG](getpattern-terminal-cache.png) | [Excalidraw](getpattern-terminal-cache.excalidraw) |
| Wildcard bypass and complete body boundary | [PNG](getpattern-body.png) | [Excalidraw](getpattern-body.excalidraw) |
| Lexical arrow calls and shared cache | [PNG](getpattern-invocation.png) | [Excalidraw](getpattern-invocation.excalidraw) |

The PNGs are committed so GitHub readers can see the diagrams directly, without
access to an Excalidraw account or the original private scenes. Download and open
the `.excalidraw` files in Excalidraw to edit the shapes, labels, and attached
arrows.

## Read the request example

The diagram uses this registration table; the labels below identify the opaque
handler labels returned by the matcher. The router does not execute handlers.

| Registration | Method | Pattern | Label |
| --- | --- | --- | --- |
| 0 | GET | `/students/:id` | `profile` |
| 1 | ALL | `/:kind/new` | `audit` |
| 2 | GET | `/students/new` | `create` |
| 3 | POST | `/students/:id` | `write` |
| Captured params reach the actual helper | [PNG](capture-collect.png) | [Excalidraw](capture-collect.excalidraw) |
| Current exec and computed m | [PNG](exec-call.png) | [Excalidraw](exec-call.excalidraw) |

For `GET /students/new`, the raw trie traversal finds registrations `0, 2, 1`.
Sorting by registration number produces:

```text
0  profile  {id: "new"}
1  audit    {kind: "students"}
2  create   {}
```

Registration 3 is excluded by its method. Captures stay with each result, and
neither the literal route nor the parameter routes suppress the other matches.
This example's discovery order and complete returned results were checked
against the actual Lean matcher when the diagram was added.

## Read the proof diagram

The arrows break the headline claim into supporting arguments:

1. The reference scan agrees with the independent matching rules
   (`rules_iff_reference` in
   [Reference.lean](../../HonoLean/Literal/Reference.lean)).
2. Raw trie candidates are a permutation of the reference results
   (`candidates_build` in
   [Correctness.lean](../../HonoLean/Literal/Correctness.lean)). This preserves
   whole results and their multiplicity, including labels and captures.
3. Sorting candidates by their unique registration numbers gives exactly the
   reference list (`lookup_build`). Combining the arguments yields
   `lookup_build_iff_rules`.

Terminal wildcards extend the same argument. A wildcard registration contributes
once when its complete prefix is reached, even when the remaining path is empty.
The suffix adds no parameter binding. The same contents-and-order proof includes
these results; see the [wildcard walkthrough](../router/history/wildcard-milestone.md).

This is a proof for arbitrary typed inputs, rather than a comparison of a finite
collection of examples. It covers the Lean matching definitions. It does not
verify Hono's TypeScript, the surrounding adapters, handler code, or a
performance bound. A separate path-parser theorem now covers request-path text;
see the new diagrams below. The [specification](../../SPEC.md) describes the v1
domain and its path-proof extension.

## Read the router-version diagram

Start with R0 containing `#0 GET /students/:id`. Save its lookup result for
`s1`, then append a POST registration to get R1 and an ALL wildcard to get R2.
R2 returns `#0 {id: "s2"}` and `#2 {}` for `GET /students/s2`; POST still occupies
ordinal 1 even though it does not match GET.

The separate branch appends that wildcard directly to R0, so it receives ordinal
1 there. Each router version describes its own ordered table. The old R0 and
the saved `s1` result remain usable. The diagram's lookup results and counters
were checked through the actual public API.

## Read the registration proof diagram

The two paths compare building an initial router and inserting one route with
building the appended model table. Both give the same trie and next ordinal.
The model table is used in the proof; the runtime router stores only its trie
and counter.

`Router.Represents` names this relationship. Build establishes it, registration
preserves it, and the preservation step repeats for any finite append chain.
The existing matching theorem then gives exact lookup results. See
[Router/Correctness.lean](../../HonoLean/Router/Correctness.lean) and the
[registration walkthrough](../router/history/registration-milestone.md).

The registration diagram describes valid typed operations. The later text-step
proof also covers rejected registrations and exact prior-state preservation.
JSON decoding/encoding and a surrounding HTTP application remain outside those
proofs.

## Read the adapter diagrams

The boundary diagram separates validation and JSON formatting from the proved
typed core. The parser rejects unsupported grammar, then the core performs
build/register/lookup with structured values. Ordered results are formatted as
JSON. A valid miss produces an empty match list; malformed lookup input produces
`invalid_request`. Categorized errors bypass the matching operation.

The failure diagram starts with one valid GET registration and `next = 1`.
Attempting `POST /students/:id?` fails validation because optional parameters are
outside v1. The following valid POST route still receives ordinal 1, and a POST
lookup returns that route's correct capture. The exact sequence was checked
through the compiled JSON executable. Initial builds are also all-or-nothing.

The boundary diagram now marks the composed text-record-to-match-list contract
as proved, including construction and registration histories. JSON decoding,
formatting, and the surrounding JSON command state machine retain their test
coverage. Individual parser theorems supply exact field meanings; the new
composition connects those meanings to the existing matching rules.
There is no composed JSON correctness theorem yet.
See the [adapter walkthrough](../router/history/adapter-milestone.md) for the original milestone
and the [path](../router/path-parser-walkthrough.md) and
[method](../router/method-parser-walkthrough.md) walkthroughs for the extensions.

## Read the comparison diagrams

The comparison flow sends the same ordered scenario to the compiled Lean JSON
command and the pinned raw Hono trie. Lean must agree with the normative fixture
or independent list model. Hono is compared against the same expected trace,
with D1 reported separately. Matching results keep their order, multiplicity,
parameter values, and types; only object-key order and backing prototypes are
irrelevant. Before/after snapshots also check retained raw Hono results.

The D1 diagram shows `GET /:__proto__ -> capture` looked up at `GET /alpha`.
Lean returns the required string capture, while the pinned Hono observation is
an object value. The exception requires that complete recorded case and both
outputs. A changed request, table, annotation, or observed value does not inherit
permission to differ. A wrong Lean result always fails its contract check.

These diagrams describe finite differential tests. They do not extend the Lean
matching theorem into a proof about Hono's TypeScript or every input in the
accepted language. See the [comparison walkthrough](../router/history/comparison-milestone.md).

## Read the benchmark diagrams

The timing diagram gives construction and lookup their own clocks. JSON input,
full semantic checks, and printing stay outside. Construction retains every new
root and reads it after timing; lookup uses one prebuilt router and includes a
small result digest. Lean has parsed core inputs, while Hono's internal text
handling remains timed. The diagram does not imply identical runtime boundaries
or a speed result from the correctness proof.

The workload diagram uses two 64-route tables from the benchmark generator.
`GET /api/v1/students/s42` illustrates a single literal match.
`GET /students/s1/worksheets` matches 32 general/student registrations, 16 ancestor
wildcards, and 16 worksheet-prefix registrations. All 64 results must be
returned with their own captures and in registration order. Across the actual
32-query fixtures, the average output sizes were 0.594 and 46.5.

These counts explain why equal table sizes can require different amounts of
work. They do not isolate the cost of traversal, sorting, capture allocation,
or the timed result sink. The [benchmark walkthrough](../router/history/benchmark-milestone.md)
contains raw measurements, ranges, metadata, and limitations.

## Read the path-parser diagrams

Soundness starts with `parsePath text = .ok pieces` and concludes that these
exact pieces satisfy the grammar and reconstruct `text`. Completeness starts
with that independent grammar relationship and concludes that parsing succeeds
with those pieces. Together they rule out both accepting unsupported text and
rejecting supported text, including a parser that returns the wrong pieces.

`/students/s1` and its two segments illustrate both directions. Root is `/` with
an empty list; every other path has nonempty segments drawn from ASCII letters,
digits, `_`, and `-`. The proof applies at every finite depth. The boundary
diagram shows where those segments enter the existing typed router contract,
with valid typed routes and a typed method as its other inputs. These remain
separate checked theorems.

Live editable scenes: [soundness and completeness](https://app.excalidraw.com/s/8wot9n3ajqf/76INY2AHl5W)
and [path proof boundary](https://app.excalidraw.com/s/8wot9n3ajqf/22PBOR4CfHa).
The committed PNGs and sources remain usable without access to those private
scenes. See the [walkthrough](../router/path-parser-walkthrough.md) for the actual theorem
and the remaining adapter proof boundary.

## Read the method-parser diagrams

The method grammar permits nonempty ASCII uppercase words except exactly `ALL`.
The acceptance diagram shows both successful exact spelling and rejection with
the caller's category. Soundness takes a success to the independent grammar and
unchanged name. Completeness accepts every spelling in that grammar, including
custom names such as `PURGE` and `ALLA`.

The second diagram distinguishes a request method from a route selector. The
helper rejects `ALL`; the surrounding route parser handles it in a special branch
as `Selector.all`. The later record-parser theorem now proves this route branch
and preserves handler labels; the diagram notes that addition. All-method
matching on typed routes was already proved. JSON decoding remains tested.

Live editable scenes: [method contract](https://app.excalidraw.com/s/8wot9n3ajqf/8SXp3iNROXq)
and [ALL's role](https://app.excalidraw.com/s/8wot9n3ajqf/6l0ecAChQ2g).
See the [method walkthrough](../router/method-parser-walkthrough.md) for the checked
theorems and remaining boundaries.

## Read the pattern and goal diagrams

`/students/:id/*` decomposes into the literal `students`, parameter `id`, and a
true suffix flag. The wildcard creates no capture. Root `/` has no components
and a false suffix; `*` and `/*` have no components and a true suffix. Names
must be valid identifiers and unique within a route. The parser theorem connects
these exact values to an independent grammar; it rejects malformed spelling
without normalization.

The goal map distinguishes checked milestones, current work, and pending work.
It describes the [five-milestone scope](../router/text-boundary-goal.md), ending at match
lists from text inputs. JSON serialization, the CLI, and handler execution
remain outside that proof scope.

Live editable scenes: [pattern contract](https://app.excalidraw.com/s/8wot9n3ajqf/643vRjehZQi)
and [goal map](https://app.excalidraw.com/s/8wot9n3ajqf/87P4rrDKayM).
See the [pattern walkthrough](../router/pattern-parser-walkthrough.md) for the checked
argument.

## Read the record-parser diagram

The three route fields converge into one typed record: method text determines
the exact selector, pattern text determines exact components and suffix, and the
handler label is preserved without interpretation. Request parsing composes its
method and path promises too. Grammar-only completeness constructs whole records;
an invalid route record rejects as `invalid_route`, and an invalid request as
`invalid_request`.

The [walkthrough](../router/record-parser-walkthrough.md) explains this composition.
Its [live scene](https://app.excalidraw.com/s/8wot9n3ajqf/1FbPg72LQfj) and the
updated ALL/adapter diagrams keep JSON decoding outside the proved text boundary.

## Read the initial-build diagram

A valid table containing two identical GET registrations and an ALL registration
keeps all three occurrences and has next ordinal 3. A duplicate parameter name
in the middle record makes the entire build fail as `invalid_route`. The ordered
table relation preserves every input position; the builder cannot silently
reverse, deduplicate, discard, or partially accept registrations.

See the [build walkthrough](../router/text-build-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/5kR8yedSpFc).

## Read the text-registration diagram

The total text step starts with a router representing one record and next
ordinal 1. A valid append creates a new router with next ordinal 2 and reports
assigned ordinal 1. A duplicate parameter name is rejected with the exact old
router, its next ordinal, and an `invalid_route` outcome. This is an equality of
the complete state, not only a counter check. Repeating the step preserves the
independent text-table invariant through every finite valid/invalid history.

See the [registration walkthrough](../router/text-registration-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/7PqE79JIp4B).

## Read the text-lookup diagram

The executable operations and the independent grammar/matching rules converge
on the same match list. In the pictured example a literal, parameter, and ALL
wildcard each return one occurrence, preserving the two repeated `same` labels
and the parameter's `id = new` capture. The theorem applies to every finite
supported text table and request, including after valid/invalid append histories.
The example is a witness, not a size bound.

The starting boundary is `TextRoute`/`TextRequest` records of Lean strings, and
the ending boundary is `List Match`. The diagram does not extend the claim to
JSON bytes or an HTTP application. See the
[full walkthrough](../router/text-lookup-walkthrough.md),
[goal evidence](../router/text-boundary-goal.md), and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/1jzLdOqFVs0).

## Read the long-running program roadmap

The green baseline is the existing restricted Lean router proof and finite
Hono comparison. Remaining stages are planned: map the fixed package surface,
establish a checked upstream source/model connection, verify the application
core, cover the remaining runtime catalog, and audit the complete argument.
The highlighted source connection is essential; differential tests alone do not
prove upstream equivalence. Core-only completion is a checkpoint in this larger
program.

See the [canonical goal](../upstream/hono-verification-goal.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/8TxFx75TVS1).

## Read the Node initialization diagram

The exact module preamble creates one emptyParams object and a zero order value.
Each selected data-field initialization allocates separate methods/patterns
arrays and a children object, installs undefined for pattern, and initially
shares the module's params object. The resulting `#methods` data slot and empty
array derive the registration-history seed; they are no longer staged inputs.
The source-derived seed composes with arbitrary supplied registration histories
and the complete capture loop under their existing read/realm contracts.

The diagram covers the selected data fields. Full class/private-method
installation, live module cells, actual caller transport and routing traversal
remain open. See the [walkthrough](../upstream/node-initialization-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/GPO0IqEirI).

## Read the private-call diagram

The selected call captures its receiver/private callee before argument effects,
evaluates arguments left to right, binds the parsed formal parameters and runs
the existing capture loop. Missing arguments become undefined. The four- and
five-argument calls at node.ts115/191 have different positional meanings; the
latter reverses the two params objects. Successful execution restores caller
scope while retaining heap effects.

This explicit top-level call extension starts with a source-bound method closure
and private read handle. Installation, live cells, search traversal and native
adequacy remain open. See the [walkthrough](../upstream/private-call-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/2EDpPe85ZMd).

## Read the private-element installation diagram

The selected declarations reserve six private names and create the method
closure. Both pictured instances install the same method value before their
own data initialization. Their arrays and children objects are fresh. The
installed read handle then survives registration and supports the actual
capture call, so its value is derived from initialization.

Existing closure-table captures also contribute to the initial freshness seed;
definitions without instances can already reserve private names. The full
class, public members, constructor/module semantics, traversal and native
adequacy remain open. See the
[walkthrough](../upstream/class-installation-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/4doLPic1Ye7).

## Read the private-write diagram

A private assignment captures its base and lexical identity, evaluates the
right-hand side, then finds the object's own private element. DATA updates keep
the stored kind and change only the value. A METHOD rejects after right-side
effects. A function value can live in DATA; the kind decides writability.
Ordinary prototypes, setters and extensibility do not control this operation.

The preserved heap/this frame is relative to the state after the right side,
so the diagram does not imply rollback. Accessors, full traversal and native
error-state adequacy remain open. See the
[walkthrough](../upstream/private-write-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/7DNdE9weLbQ).

## Keep the images current

Edit a source file in Excalidraw, save the `.excalidraw` file, and export a PNG
with the same basename. Keep a white background and enough padding for labels
and arrowheads. Commit both files together, and check the rendered README for
legibility.

These are explanatory snapshots, not diagrams generated from the Lean code.
When behavior or proof structure changes, update the relevant diagram and its
README explanation together. Keep future features clearly separate from
properties already proved.

## Read the literal-child branch diagram

The branch first reads and binds the next child. Falsy children skip it; real
children receive the parent's params reference. A nonfinal child enters the
current temporary queue once. A final child processes a truthy wildcard child
before the direct child, preserving that actual intermediate order.

The collector keeps handler-record references. A later call can reset a shared
record's params, changing the value observed through an earlier entry. The
proof needs sequential states and derives the second call's structural layout
from the first call's effects. The containing loops, pattern processing and
final sorting remain outside this source window. See the
[walkthrough](../upstream/literal-branch-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/7pcrdXABb3x).

## Read the iteration-setup diagram

Saved length and current array reads are separate source operations. The outer
activation supplies i; source 100–102 derives the actual part, signed last flag
and new empty queue. The inner activation supplies j; source 105 selects the
current node before the four-path branch.

The fresh queue differs from the allocated old collector, and setup preserves
old array cells so the initial helper layout transports. Later collector appends
can affect aliases; that stronger post-branch frame is not inferred. The pink
activation boxes mark the omitted loop headers and keep full-loop reachability
open. See the [walkthrough](../upstream/iteration-setup-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/XwsDFrzi8G).

## Read the search-startup diagram

Source 87–97 creates the collector, resets params, starts with `curNodes=[this]`,
calls the actual parsed `splitPath` body, and keeps its returned array before
allocating the pending queue and saving length/null offsets. The path contract
is independent of source execution. Four fresh identities and old-array frames
make the resulting data usable by the later iteration theorem.

Source 100–102 and source 105 remain separate windows across omitted headers. The
blue supplied-index arrow and amber open box keep loop progression, traversal
and native adequacy explicit. See the
[walkthrough](../upstream/search-setup-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/78xKsiN9oLc).

## Read the loop-entry diagram

Header 99 creates i=0 and tests the saved path length. A false guard stops this
prefix before any body array allocation. A true guard admits source 100–102,
then header 104 creates j=0 and saves the current singleton node-array length 1.
The true inner guard admits source 105's receiver read. No index is supplied to
this first-entry theorem.

The amber final box marks the remaining body and traversal. Updating an index
is separately modeled after a body completion; saved length alone does not
prove that a later mutated array still has that index. The false branch also
does not prove native lexical-scope exit. See the
[walkthrough](../upstream/loop-entry-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/4eyiyVPpBKi).

## Read the initial-state first-literal diagram

Initial method rows, key snapshots, read/prototype facts and captured imports
do not include a collector or future helper Layout. Actual source 87–105 creates
the arrays, resets params and derives the first indices/node. For nonempty
parts, source 106–119 follows missing/nonfinal/direct/wildcard cases and preserves
raw collection order and live aliases. Empty parts stop earlier, as shown in
the loop-entry diagram.

The final amber box keeps patterns, later loop/body traversal, sorting/map and
native adequacy outside this prefix. See the
[walkthrough](../upstream/first-literal-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/9ZfC0TB5T2n).

## Read the queue-advance diagram

The pending queue is shifted before either branch reads the temporary/shifted
arrays. A falsy head reuses the temporary identity; a truthy head, including an
empty array, takes concat and produces a fresh shallow result. Aliases use
post-shift contents, and the actual first `curNodes` binding is retained after
the fragment. The amber endpoint leaves sparse producers and full body/loop/
runtime composition open. See the [walkthrough](../upstream/queue-advance-walkthrough.md)
and [live scene](https://app.excalidraw.com/s/8wot9n3ajqf/9WTPJvyGlnu).

## Read the sparse-scheduling diagram

The selected slot either reuses a truthy array without RHS/Put, or receives a
fresh array while intervening indices remain absent. Child append acts on the
current target, including self-target aliases. Selected 209–210 consumption
preserves own holes; a separate read-value observer maps them to undefined
without claiming own-property equality. The amber endpoint leaves counts,
regexp/for-in/body/loop and native adequacy open. See the
[walkthrough](../upstream/queue-schedule-walkthrough.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/5UeEkXopWDR).

## Read the capture-to-collector diagram

The parent map enters the actual 161 call fourth; fresh local params enters
fifth. The guard attempts an assignment only when no own field exists.
The helper selects requested-method or ALL records, allocates null-prototype
params before processing keys, and preserves live handler aliases. Constructor
as a later key can choose an inherited function over the local string.
The conditional source-model proof retains explicit match/regex/traversal and
native adequacy boundaries. See the [walkthrough](../upstream/capture-collect-walkthrough.md),
[audit](../upstream/capture-collect-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/17rILjQIN0M).

## Read the current-exec diagram

The current function and original matcher are saved before the argument.
The actual body returns m, retaining dynamic this and effects. The exact 157
header test is separated from its unproved complete body; only the computed
singleton-array path is composed with 158–160. Other actual return types remain
visible. Builtin regex,161 joining, tuple/closure creation and full search/native
adequacy remain open. See the [walkthrough](../upstream/exec-call-walkthrough.md),
[audit](../upstream/exec-call-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/50taty2Enxu).

## Read the tuple-binding diagram

Actual terminal construction supplies a fresh tuple to the actual destructuring
statement. The default DATA-array iterator saves its next method, skips one
result without reading its value, then binds the next two values as name and
matcher. It reads the current return method on close without marking the
iterator exhausted. The selected digit profile then executes actual 156 using
the derived matcher and an initially supplied query. Internal protocol objects
are model observations; native visible-state comparisons are separate evidence.
The amber endpoint retains label matching, cache/tree/query provenance and
native adequacy as open obligations. The export has 28 active elements and seven
bound arrows. See the [walkthrough](../upstream/pattern-binding-walkthrough.md),
[audit](../upstream/pattern-binding-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/3j7YxLaaYsE).

## Read the label-capture diagram

The source saves current String.match before creating a fresh intrinsic regex
literal. Typed Symbol.match, current flags/getters and the same exec identity
reach a real greedy capture machine. An independent language contract determines
the name and optional RAW body; plain :id has an own undefined index 2. The
computed data supplies the selected constructor/binding/digit-exec chain. The
amber endpoint leaves cache/tree/query production and native edition/realm/full
Hono coverage open. The export has 26 active elements and seven bound arrows.
See the [walkthrough](../upstream/label-match-walkthrough.md),
[audit](../upstream/label-match-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/AMHm91Bf8cL).

## Read the persistent-cache diagram

Two distinct label/next pairs share the raw key :a#b#c. The first cold plain call
allocates and stores its tuple; a later truthy DATA hit skips cold work and the
return performs a second current Get. Both-order checked histories carry the
same heap/cache and preserve the first tuple's identity and contents. The amber
endpoint leaves universal terminal-cache, cold lookahead, module/native and full
Hono coverage open. The export has 26 active elements and seven bound arrows.
See the [walkthrough](../upstream/getpattern-cache-walkthrough.md),
[audit](../upstream/getpattern-cache-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/1RnECnclUI0).

## Read the terminal-cache diagram

Actual source 60 computes captures, then source 68 constructs a fresh safe-range
regex inside the reserved tuple. Strict ordinary Set stores the tuple, and
source 74 reads it again. The independent contract connects the actual cached
brand/code to its inclusive nonempty interval language. Actual 50 initialization
and two complete body activations carry the same heap/cache; the warm call keeps
both tuple and regex identities. Single-call aliases and reuse realm separation
have distinct domains. The open endpoint retains wildcard/function/module,
lookahead/general regex/native and full Hono obligations. The export has24active
elements and six bound arrows. See the
[walkthrough](../upstream/getpattern-terminal-cache-walkthrough.md),
[audit](../upstream/getpattern-terminal-cache-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/6wg4KglUqnD).

## Read the wildcard/body diagram

The actual744B arrow supplies checked syntax and a complete body projection.
At body entry, exact label=`*` reaches an immediate return with the ENTIRE state
unchanged; no cache/next/matcher/constructor readiness is needed. Other values
reach the retained533B code on the same state, preserving model errors and the
independent normal-profile contracts. The lower amber boundary retains real
function invocation/closure/module, lookahead/general regex/native and full Hono
work. The export has26active elements and seven bound arrows. See the
[walkthrough](../upstream/getpattern-body-walkthrough.md),
[audit](../upstream/getpattern-body-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/9GaHfOop1bM).

## Read the lexical-arrow diagram

The actual796B setup creates the cache and exported callable once. The closure
retains an environment reference; each later call gets fresh parameter cells
and reads current bindings at the expression that needs them. Calls retain the
same cache, and a warm hit retains its cached tuple. Independent contracts frame
the caller and pre-existing lexical storage. The original body diagram records
its earlier boundary; this addition connects creation and value-resolved calls
for the admitted profiles. General callbacks, partial errors, TS/module/native
adequacy, lookahead and full Hono remain open. The export has25active elements
and eight bound arrows. See the
[walkthrough](../upstream/getpattern-invocation-walkthrough.md),
[audit](../upstream/getpattern-invocation-audit.md) and
[live scene](https://app.excalidraw.com/s/8wot9n3ajqf/AKwddbfT8ZS).
