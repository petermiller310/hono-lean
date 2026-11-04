# Milestone 1: a verified literal-path trie

Historical walkthrough of milestone 1 at commit `b7a5606`. Milestone 2 extends
these same core modules with method selection; their current signatures include
a request method. See [the method walkthrough](method-milestone.md) for the
milestone-2 implementation and theorem. Milestone 3 adds named parameters; see
[the current parameter walkthrough](parameter-milestone.md). The original tiny first-proof lesson in
`HonoLean/Literal.lean` is still unchanged.

## What is implemented

We match already-parsed literal paths such as `["students", "new"]`. A route
contains a path and a handler label. Each registration gets an ordinal that
counts every route, including routes that do not match a particular request.
The result is the ordered list of matching ordinals and unchanged handler labels.
Literal matches have no parameters, so their v1 parameter map is implicitly empty.

The proof covers every finite list of string segments and every finite route
table, without a size limit or ASCII hypothesis. This is a stronger core theorem
than restricting strings to the canonical v1 alphabet. It does not implement or
verify text parsing, admit unsupported route syntax through an adapter, or add
methods, parameters, wildcards, or an HTTP server.

## Three separate things

1. **Rules:** a registration matches exactly when its whole path equals the
   request path. An empty table requires an empty output. For each registration
   in order, a matching path contributes its ordinal and label; a different path
   contributes nothing. Either way, the next ordinal increases.
2. **Reference implementation:** scan every registration and collect those
   matches. It is simple enough to compare directly with the rules.
3. **Trie implementation:** store common path prefixes once, then follow the
   request's segments through that tree.

These live in `Spec.lean`, `Reference.lean`, and `Trie.lean` under
`HonoLean/Literal/`. The original tiny lesson in `HonoLean/Literal.lean` remains
available, but the new proof goes beyond its one-route example.

## What the tree stores

For the demo routes, the relevant part of the tree is:

```text
root                              terminal: [(2, "root")]
  students                        terminal: [(3, "listStudents")]
    new                           terminal: [(1, "same"), (5, "same"), (6, "")]
  unrelated                       terminal: [(0, "before")]
  elsewhere                       terminal: [(4, "between")]
```

Looking up `["students", "new"]` follows the `students` edge, then `new`, and
returns the terminal list at that node. It never scans all registered routes.
Sibling edges use a finite association list: finding an edge scans its labels,
then lookup descends only into the matching subtree. No performance bound or
speed advantage is proved in this milestone.

The root has its own terminal list. It does not automatically match descendants.
Similarly, the `students` node's terminal list is not returned when looking up
`students/new`. That is how exact matching differs from prefix matching.

## The invariant that makes the proof work

Inserting one registration at path `p` has precisely this effect:

```text
lookup(new tree, q) = lookup(old tree, q)
                     followed by [new registration] if p = q
                     followed by [] otherwise
```

This is the theorem `Trie.lookup_insert`. It holds for every finite trie, path,
request, and entry. There is no unproved `WellFormed` hypothesis hiding the
conclusion. The helper `child_alterChild` establishes that updating an edge
changes the chosen child and leaves every other chosen child unchanged.

Insertion reuses an existing edge with the same label, creating a new edge only
when none exists. Thus construction shares prefixes. Appending to the terminal
list preserves earlier matches, repeated labels, and repeated registrations.
The proof's semantic invariant does not require a separate structural uniqueness
assumption; even if someone constructs a raw tree with duplicate child labels,
the defined first-edge lookup and update agree. Normal construction starts empty
and reuses matching edges.

## Why induction covers arbitrary inputs

The insertion proof uses induction on the inserted path:

- For an empty path, append the result at this node. A request at this node sees
  the new result; a request descending further sees unchanged children.
- For a nonempty path, update its first edge and apply the same argument to the
  shorter remaining path. A request using another edge is unaffected.

The build proof then uses induction on the route table:

- Building no additional routes changes nothing.
- Insert the first route, use the insertion theorem, and apply the build argument
  to the remaining routes with the next ordinal.

The generalized build invariant permits an existing tree and starting ordinal.
It says that building more routes appends exactly their reference matches to
the old matches. Starting with the empty tree and ordinal zero gives:

```text
Trie.lookup (Trie.build routes) requestPath
  = referenceLookup routes requestPath
```

That is `Trie.lookup_build`. The theorem `Trie.lookup_build_iff_rules` goes one
step further: a proposed output equals trie lookup if and only if it is exactly
the output required by the independent rules. It uses `rules_iff_reference`, which
proves that the reference implements those rules. We therefore do not merely
compare two algorithms that happen to share the same mistake.

The rule judgment describes the whole output list, not just set membership.
That is why the theorem establishes order, ordinals, labels, and multiplicity
as well as finding all and only exact matches.

## What was checked

`lake build` builds every module through the root import. The main theorem audits
enforce only `propext`, an ordinary Lean logical axiom. A changed axiom list fails
the build and requires review. There are no
unfinished proofs, custom axioms, or native-evaluation proof shortcuts.

The built root module and its imports were also replayed through Lean's kernel
in a fresh environment with `lake env leanchecker --fresh HonoLean`. CI runs the
same check. This is a separate kernel replay, not an independent proof system.

The small regression corpus checks a table with nonmatching registrations before
and between matches, repeated identical labels, an empty label, a root handler,
a parent handler, case-sensitive misses, and extra-segment misses. It also checks
an empty table. These concrete checks use kernel-checked `decide`, and the demo
checks the compiled reference and trie against the same explicit expectations.
They illustrate and guard the intended behavior; the general theorem covers
inputs beyond these examples.

Pure functions and immutable data mean lookup cannot change a previous result
or router. Termination is checked for all recursive definitions. Compiler,
runtime, machine, memory exhaustion, and unimplemented adapters remain outside
the mathematical matching claim, as described in `SPEC.md`.

## Fault experiments

Review used a separate temporary copy of the project. Its unchanged control
build passed. Each of these changes was then tested separately:

- prepend an inserted entry instead of appending it;
- return an empty list at every terminal instead of its stored matches.

Both changes caused the `lookup_insert` correctness proof to fail with an
unsolved goal. The working project retains the correct implementation.

Suppose insertion used `new entry :: old entries` at each terminal. After the
second registration of a path, results would appear in reverse registration
order. The insertion theorem would no longer hold: its right side explicitly
appends the new registration after existing results. The build proof would fail
at that obligation, and the explicit duplicate-registration example would fail.

Likewise, a lookup that returned a parent node's terminal list for a longer
request would violate the exact-path insertion theorem. A root or parent handler
does not act as a wildcard in this milestone.
