# Milestone 3: named parameters and capture

This walkthrough describes the historical milestone at `98e1e6c`. Terminal
wildcards are now implemented; see the [milestone 4 walkthrough](wildcard-milestone.md)
for the current matching core.

The matching core now supports parsed literal and named-parameter components,
with methods and `ALL` preserved. A named parameter consumes exactly one nonempty
request segment. The whole pattern must still be consumed: no optional parts,
regex, or wildcards are implemented.

## A request can follow more than one branch

Consider these registrations, in this order:

```text
0  GET /students/new        -> literal
1  GET /:kind/:id           -> general
2  GET /students/:studentId -> student
```

`GET /students/new` returns all three registrations:

```text
0  literal  {}
1  general  {kind: "students", id: "new"}
2  student  {studentId: "new"}
```

The literal route does not defeat the parameters. Lookup explores each compatible
literal or parameter edge, collecting the successful terminal results. Edges are
keyed by component, including the parameter name. A literal prefix shared by
several routes is still represented once; identical parameter-name prefixes also
share a branch. Different names may have different branches.

The terminal stores only method selector, ordinal, and label. It does not retain
complete route patterns for a second full-route scan. The reference matcher scans
routes; the trie actually traverses matching prefixes.

## Captures belong to a branch and registration

A parameter edge adds its own `(name, segment)` pair to results from that subtree.
A literal edge adds nothing. These lists are immutable values, so exploring one
branch cannot overwrite another branch's names or leak keys into it.

For `/students/s1`, the general route above receives
`[("kind", "students"), ("id", "s1")]`; the student route receives only
`[("studentId", "s1")]`. A later request for `s2` builds new results. It cannot
change a retained `s1` result or the stored trie.

A parameter cannot match the root or an empty segment. `/students/:id` does not
match `/students`, `["students", ""]`, or `/students/s1/extra`. The root remains
an exact empty path, with its own possible registrations.

## Why a final ordering step is now necessary

Previously, a literal request reached one endpoint, whose registrations were
already in order. Parameter matching can reach several endpoints. The example
above can be discovered as ordinals `[0, 2, 1]`: the `students` branch first,
then the general parameter branch. Discovery order is not registration order.

The trie therefore gathers candidates and applies Lean's standard merge sort by
registration ordinal. Sorting does not deduplicate labels, patterns, or matches.
Methods are selected at each terminal before results are collected. Interleaved
`ALL` and exact registrations retain their global order after sorting.

This milestone makes no proved speed or complexity claim. Child edges use a
finite association list, and overlapping parameter branches can require multiple
subtree searches. The final sort is an actual checked part of the algorithm.

## What makes the ordering proof complete

The proof is split into two arguments:

1. **Right contents:** `candidates_insert` and `candidates_build` prove that raw
   trie candidates are a permutation of the reference results. A permutation
   preserves every complete result, including its captures and multiplicity;
   it is stronger than saying that the same handler names appear somewhere.
2. **Right order:** `referenceFrom_strict` proves reference ordinals are strictly
   increasing, and `strict_keys_injective` proves that equal ordinals identify
   the same complete result in that list. Merge sort preserves permutation and
   orders candidates by ordinal. Two such ordered lists must be equal.

The unique-ordinal argument matters: sorting by a key would not otherwise justify
arbitrary reordering of different results with tied keys. Registration numbers
count every route, including nonmatching paths and methods, so building a table
assigns distinct ordinals even when labels and patterns repeat.

`Trie.lookup_build` establishes exact trie/reference list equality.
`Trie.lookup_build_iff_rules` connects that output to the independent ordered
matching rules. Neither theorem assumes a size limit or a desired lookup result.

## The capture specification is separate from traversal

`Captures` in `Spec.lean` states three rules: two empty paths capture nothing;
a matching literal consumes one segment without a binding; a parameter consumes
one nonempty segment and prepends its name/value binding. These rules do not
traverse the trie or sort results.

`Reference.lean` proves that the simple recursive `capture` function follows
exactly those rules, with a unique capture list for a matching pattern and path.
The route-table reference scan then combines capture and method acceptance in
registration order. Its output is proved equivalent to the independent rules.

## Lists represent finite maps without special property names

`Params` is a list of string pairs in route-appearance order. Each `Route` carries
proof that parameter names satisfy `[A-Za-z_][A-Za-z0-9_]*` and are unique within
that route. Repeated names are excluded within one route; different routes can
use different names at the same position.

The capture proofs establish:

- `captures_keys`: result keys are exactly the pattern's parameter names in order;
- `captures_unique_keys`: those keys have no duplicates for a registered route;
- `captures_nonempty`: every captured value is nonempty;
- `capture_unique`: the declarative rules determine a unique capture list.

`Trie.lookup_capture_properties` carries key uniqueness, nonempty values, exact
key domain, and capture-rule correctness through to actual returned matches.
`params_permutation_same_map` also proves that reordering a unique-key pair list
does not change any name lookup. Thus structural list equality in the main theorem
is stronger than the specification's order-insensitive finite-map equality.

Names such as `__proto__` and `constructor` have ordinary string behavior. The demo
captures their string values correctly, implementing the normative side of the
specification's documented Hono baseline difference D1.

## Typed input and the remaining boundary

Methods retain their checked uppercase/nonempty/not-ALL domain. Route patterns
are already structured components and carry their name-validity/uniqueness proof.
`literalRoute` is a convenience constructor from a list of already-parsed literal
segments; it is not a text parser.

Request paths remain finite lists of arbitrary strings. Parameter consumption
explicitly excludes empty strings, but does not itself exclude Unicode or slash
characters inside a supplied segment. The v1 text adapter will enforce the
narrower canonical request/literal-segment grammar. The theorem is stronger over
these raw lists; it does not claim that unsupported text has been validated or
normalized. JSON/text parsing, error responses, and physical resource limits
remain outside the matching proof.

## Checks

`lake build` checks the general theorems, capture-map properties, axiom guards,
and concrete regression examples. The main guards admit only the ordinary Lean
logical axioms `propext`, `Classical.choice`, and `Quot.sound`. There are no
unfinished proofs, custom axioms, or native-evaluation proof shortcuts.

Concrete logical examples reuse the general trie/reference equality theorem and
then evaluate the simple reference in Lean's kernel. The compiled demo separately
executes the actual trie traversal and sort, comparing both implementations with
explicit expected results.

Examples cover adversarial branch discovery order, literal/parameter overlap,
same shapes with different names, multiple captures, duplicates, an empty label,
method filtering and ALL, no HEAD fallback, root/empty/short/long misses, special
names, and repeated requests. Name-domain and duplicate-name witnesses are also
checked in the kernel.

Independent review also ran 40 actual trie lookups: 35 applicable non-wildcard
lookups from the existing v1 corpus, including table snapshots after append
events, plus five adversarial ordering and empty/length cases. It checked the
corresponding logical expectations through the main theorem and kernel-evaluated
reference, plus four pattern-domain witnesses. The normative `__proto__` case
returns its string value. Snapshot tests rebuild tables; they do not implement
the deferred public registration API or a text parser.

The fresh kernel replay passed with
`lake env leanchecker --fresh HonoLean`. This rechecks the built root and imports
through Lean's kernel; it is not a different proof system.

Fault experiments used a separate temporary project. The unchanged control build
passed. Each of these typed implementation changes then caused a correctness
proof to fail:

- capturing the parameter name as its value;
- omitting the final registration-order sort;
- suppressing parameter branches when a matching literal branch exists.

The working project keeps the correct capture, traversal, and sorting behavior.

Wildcards, parsers, public incremental registration, and the broader comparison
harness remain future milestones. The formal result concerns this Lean core,
not Hono's TypeScript or a surrounding HTTP application's behavior.
