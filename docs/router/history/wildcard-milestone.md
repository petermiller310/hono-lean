# Terminal wildcards, without a larger routing language

This walkthrough describes the historical milestone at `90bfdda`. Incremental
registration is now implemented; see the [registration walkthrough](registration-milestone.md)
for the current public typed API.

Milestone 4 adds one behavior: once a route's literal and parameter prefix has
matched, it can accept any remaining suffix. The trie still returns every match
in registration order, with each registration's own parameter captures.

This is a matching-core milestone. Text parsing, the public incremental
registration API, the full Hono comparison harness, and release benchmarks are
still future work.

## What a wildcard means

Consider these registrations in this order:

| Ordinal | Method | Pattern | Label |
| --- | --- | --- | --- |
| 0 | GET | `/students/:id` | `exact` |
| 1 | GET | `/students/:id/*` | `detail` |
| 2 | ALL | `/students/*` | `students` |
| 3 | ALL | `/*` | `global` |

For `GET /students/s1`, the result is:

```text
0  exact     {id: "s1"}
1  detail    {id: "s1"}
2  students  {}
3  global    {}
```

Registration 1 matches even though nothing remains after `s1`. A wildcard
accepts **zero or more** remaining segments, rather than requiring another one.

For `GET /students/s1/worksheets/w2`, the result is:

```text
1  detail    {id: "s1"}
2  students  {}
3  global    {}
```

The exact registration no longer matches. The wildcard registrations still do,
but there is no extra `*` binding: registration 1 captures only `id = "s1"`.
The remaining `worksheets/w2` is accepted, not captured.

For `GET /students`, only registrations 2 and 3 match. The `:id` prefix in
registration 1 still requires one nonempty segment; the wildcard cannot supply
a missing parameter. The global wildcard also matches `/`. An exact root route
would match only `/`.

The diagram in the [project README](../../../README.md) explains how compatible
branches combine. Wildcards add another source of candidates; they do not
suppress exact routes or named-parameter routes.

## One flag on the route

[Spec.lean](../../../HonoLean/Literal/Spec.lean) adds a Boolean field:

```lean
suffix : Bool := false
```

A route's `path` is still a list of literal and named-parameter components.
`suffix := false` requires the request to end after that prefix. Setting it to
`true` accepts any remaining suffix. Existing route definitions keep their exact
behavior because the default is `false`.

This follows the representation chosen in [the specification](../../../SPEC.md): the
wildcard operation lives at the end of a prefix, rather than being a component
that could appear in the middle. There is no optional segment, regular
expression, or wildcard capture added to the language.

The text spellings `*` and `/*` share the same parsed representation: an empty
prefix with `suffix := true`. There is still no text parser, so this milestone
does not claim to parse either spelling.

## One extra terminal list per trie node

[Trie.lean](../../../HonoLean/Literal/Trie.lean) remains a finite prefix tree. Each node
now contains:

- exact registrations that end here;
- wildcard registrations whose prefix ends here;
- the existing literal and parameter children.

Lookup collects the node's method-compatible wildcard entries whenever it
reaches the node. If the request ends here, it also collects exact entries. If
segments remain, it searches compatible children as before. The final sort
restores the original registration order across all sources of candidates.

A wildcard registration is emitted **once at its matched prefix**. It is not
copied into every descendant or emitted again for each remaining segment.
Earlier parameter branches still prepend their own captures to the returned
results. Wildcards themselves contribute an empty capture list.

The trie implementation grows from 81 to 83 lines for this milestone. It keeps
the same association-list children, method selection, immutable capture
construction, and ordinal sort, with no new dependency or route-table scan.

## What changed in the proof

The declarative `Captures` rules gain one base case: an exhausted prefix with
the suffix flag set accepts any remaining path and contributes no bindings.
The literal and parameter rules still consume one segment at a time. The
reference scan is proved equivalent to these independent rules in
[Reference.lean](../../../HonoLean/Literal/Reference.lean).

The trie proof keeps the previous structure:

1. Inserting one registration adds exactly that registration's matching result,
   if it matches, while preserving the earlier candidates up to permutation.
   The new base case handles insertion into a node's wildcard list.
2. Repeated insertion gives the same complete candidates as the reference
   scan, including labels, captures, and repeated registrations. Raw discovery
   order can differ.
3. Sorting by the unique registration ordinals produces exactly the reference
   list. This ordering argument is unchanged.

The headline theorem is still `Trie.lookup_build_iff_rules` in
[Correctness.lean](../../../HonoLean/Literal/Correctness.lean). It now covers exact and
wildcard routes together, for arbitrary finite typed route tables and request
paths. It has no fixture-size or path-length bound. The capture theorem still
establishes exactly the registered parameter names, unique keys, and nonempty
captured values. In particular, the suffix introduces no synthetic key.

The guarantee is agreement with these formalized matching rules. Those rules
remain something a maintainer must read and assess.

## Verification and scope

Run:

```sh
lake build
lake exe hono-lean
lake env leanchecker --fresh HonoLean
```

The build checks all proofs, with warnings treated as errors. The demo checks
the actual trie against explicit expected results and the reference matcher.
It retains the previous 29 examples and adds 14 wildcard examples covering
empty and long suffixes, global wildcards, exact/parameter/wildcard overlap,
methods and `ALL`, duplicate registrations, nonempty required parameters,
multiple captures, and repeated lookups with fresh values.

The regression theorem uses the general `lookup_build` theorem to reduce trie
expectations to reference expectations, then checks those expectations in the
kernel. The executable separately runs the actual trie traversal and sorting.
The examples illustrate the domain; they are not hypotheses of the general
proof. Main-proof axiom guards still permit only Lean's ordinary logical
axioms: `propext`, `Classical.choice`, and `Quot.sound`.

Independent review also checked all 52 normative lookup expectations in the v1
corpus, plus 64 additional cases across GET, POST, HEAD, and PURGE. The additional
cases combine ancestor and descendant wildcard prefixes, duplicate global and
prefix registrations, different parameter names, special string keys, empty
required parameters, exact-route misses, and a suffix of 128 extra segments.
All 116 checks executed the actual trie against explicit expected results, with
corresponding kernel-checked expectations after applying the general theorem.

Corpus registration events were checked as rebuilt route-table snapshots. These
checks do not implement the public registration API, text decoding, or the 30
rejected-input adapter cases. The normative `__proto__` expectation remains a
string capture, including the documented difference from the pinned Hono trie.

A fresh kernel replay of the root module and its imports passed. In a separate
temporary project, an unchanged control build passed, then each of three
deliberate implementation faults typechecked but failed the general correctness
proof:

- dropping wildcard matches when the suffix is empty;
- emitting wildcard results twice when the suffix is nonempty;
- inventing an extra `*` capture for wildcard results.

These fault experiments check that the proof rejects those broken implementations;
they are additional evidence, not a replacement for reading the rules or proof.

The core accepts raw lists of string segments. A wildcard suffix may therefore
include empty strings in this structured domain, while any preceding parameter
still rejects an empty segment. The future text adapter will enforce the
canonical path grammar, which excludes such empty segments. This milestone
does not verify that adapter, Hono's TypeScript, handler execution, or a
performance bound. Execution also relies on Lean's compiler, runtime, and the
machine; the mathematical proof is checked by Lean's kernel.
