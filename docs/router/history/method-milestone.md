# Milestone 2: method matching and ALL

Historical walkthrough of milestone 2 at commit `d82a12c`. Milestone 3 extends
these core modules with parameter patterns, captures, and final ordinal sorting.
See [the parameter walkthrough](parameter-milestone.md) for current types and proofs.

The literal-path trie now checks the request method as well as the path. The
tree still shares path prefixes; only its terminal entries and the final
selection step changed. There are no separate method trees or sorting passes.

## The new rule

A registration matches exactly when both conditions hold:

1. Its whole literal path equals the request path.
2. Its selector is `ALL`, or its exact method has the same spelling as the
   request method.

`ALL` adds matches. It never replaces an exact match or receives special
priority. An `ALL` registration still needs the exact same path in this
milestone. It is not a path wildcard.

For example, register:

```text
0  POST /students -> write
1  ALL  /students -> log
2  GET  /students -> read
3  ALL  /students -> audit
```

`GET /students` returns registrations `[1, 2, 3]`. `POST /students` returns
`[0, 1, 3]`. `HEAD /students` returns `[1, 3]`. Ordinals count every registration,
including the ones that do not match a particular method.

`HEAD` has no fallback to `GET`. An HTTP framework can provide such dispatch
behavior elsewhere, but our raw matching specification does not. A GET-only
route therefore does not match HEAD. Custom methods such as `PURGE` work by
the same exact-spelling rule.

## Supported methods are represented explicitly

`Method` contains a spelling and a proof that it is nonempty, contains only
ASCII `A` through `Z`, and is not `ALL`. Concrete GET, POST, HEAD, OPTIONS, and
PURGE values witness that the domain is inhabited. Kernel-checked examples show
that empty, lowercase, reserved `ALL`, non-ASCII, and hyphenated spellings do not
satisfy the predicate.

A route's selector has two forms: `all`, or `exact` with a supported `Method`.
This separates the selector from an actual request method. An exact comparison
reads only the two spellings, so validity proof terms cannot affect matching.
No lowercasing, uppercasing, or trimming occurs.

This is a typed core, not a text adapter. Code calling the core must already
provide a supported Method value and a parsed path. We have not implemented
JSON/text parsing or its error responses. Path segments retain the stronger
milestone-1 theorem domain of arbitrary finite lists of strings; input adapters
will enforce the narrower canonical path grammar specified for v1.

## How the trie changed

Each terminal stores its registrations in the same order as before, now with
a selector beside each ordinal and handler label. Lookup follows the path to
one terminal, then filters that terminal's entries by the request method.

Filtering retains the relative order of the survivors. This is why interleaved
`ALL`, GET, and POST registrations do not need to be sorted or merged. A repeated
label remains a separate registration, and an empty label remains valid data.
The final result still contains ordinal and label; the parameter map is
implicitly empty because this milestone has no named parameters.

The child-edge association list and prefix sharing are unchanged. Finding a
sibling label still scans that list; this milestone makes no speed or complexity
claim.

## How the proof changed

The independent rule judgment in `Spec.lean` now uses the two-part matching
condition. The reference scan in `Reference.lean` implements that condition,
and `rules_iff_reference` proves the rule-defined whole output is exactly the
reference output.

The insertion invariant is now:

```text
lookup(new tree, method, path)
  = lookup(old tree, method, path)
    followed by the new result exactly when its path and method both match
```

`select_append` proves the small new fact: appending one stored registration
appends one selected result if its method is accepted, and otherwise changes
nothing. `lookup_insert` combines that fact with the existing path argument.
Induction over the route table then proves `lookup_build`: trie and reference
return equal lists for every finite table, supported method, and parsed path.

`lookup_build_iff_rules` connects the trie directly to the independent rules.
List equality covers missing and extra matches, ordering, ordinals, unchanged
labels, and duplicate occurrences. There is no table-size or path-size bound,
and no assumption that a particular lookup already produces the desired result.

The method filter is inside pure lookup. Running POST after GET cannot mutate
the tree or change a retained GET result. Structural recursion still establishes
termination on finite paths, tables, and terminal lists.

## Checks and limits

`lake build` compiles every proof and checks concrete examples with kernel
evaluation. The main theorem axiom guards permit exactly the ordinary Lean
logical axioms `propext`, `Classical.choice`, and `Quot.sound`; they introduce no
unfinished proofs, custom axioms, or native-evaluation proof shortcuts.

The fresh kernel replay also passed with
`lake env leanchecker --fresh HonoLean`, covering the root module and its imports.

`lake exe hono-lean` compares compiled trie/reference results against explicit
expectations. The demo includes ALL/exact interleaving, skipped method entries,
duplicates, an empty label, HEAD without GET fallback, PURGE, root and prefix
cases, and GET again after other requests. The original literal examples still
run as all-selector registrations.

A separate review checked all 20 literal-path lookups applicable to this milestone
from the existing v1 JSON contract, plus seven valid/invalid method-spelling
witnesses, using kernel evaluation. The review translated the already-canonical
fixture paths directly into segment lists; it did not add or test a text adapter.

Fault experiments used a separate temporary project whose unchanged control
build passed. One change discarded `ALL` entries during selection. Another grouped
exact-method entries before `ALL` entries. Both caused the `select_append`
correctness proof to fail. They demonstrate why preserving matches and preserving
their original interleaving are separate requirements. The working project keeps
the correct filter.

Methods and literal paths are the implemented portion of the v1 contract.
Parameters, path wildcards, adapters, and public incremental registration remain
later milestones. Compiler/runtime/machine assumptions and physical resource
limits remain outside the matching theorem, as described in `SPEC.md`.
