# V1 completion and evidence

The implementation and evidence required by the existing [v1 specification](../../../SPEC.md)
are complete for local public review. All commands listed below passed locally.
The repository has not been published by this audit, and configured CI is not a
claim that a remote GitHub run has passed.

This records the v1 audit at `cddb060`. The later
[path-parser](../path-parser-walkthrough.md) and
[method-parser](../method-parser-walkthrough.md) extensions, followed by the
[completed five-milestone text goal](../text-boundary-goal.md), extend the proof
through text input to match lists. The v1 evidence below and checked-in benchmark
samples remain historical records of their original revisions.

## The proved claim

For every valid finite typed route table and structured request, lookup returns
exactly the matching registrations, with their correct labels and captures, in
registration order. The same claim holds after any finite append sequence from
a built router. The formalized matching rules remain subject to human review.

| Specification obligation | Checked implementation or argument |
| --- | --- |
| Reference correctness and unique captures | `capture_iff`, `capture_unique`, and `rules_iff_reference` in [Reference.lean](../../../HonoLean/Literal/Reference.lean). |
| Soundness | `Trie.lookup_build_iff_rules` gives exact rule-defined results; `lookup_capture_properties` gives each returned route's capture keys and values in [Correctness.lean](../../../HonoLean/Literal/Correctness.lean). |
| Completeness | The same equivalence includes every matching registration, rather than only proving that returned results are valid. |
| Order and multiplicity | `lookup_build`, `lookup_strict`, and the ordered reference scan preserve complete results and repeated registration occurrences. |
| Insertion invariant | `candidates_insert` preserves candidate contents; `Router.register_represents` preserves the exact built trie and next ordinal in [Router/Correctness.lean](../../../HonoLean/Router/Correctness.lean). |
| Incremental correctness | `lookup_registerMany_build_iff_rules` covers arbitrary initial and appended tables without assuming the desired output. |
| Lookup isolation | [Router.lean](../../../HonoLean/Router.lean) and the trie use pure immutable values; lookup changes neither the router nor retained results. Public-API tests also retain and fork old versions. |
| Totality | Lean checks structural recursion on finite patterns, paths, and route lists; standard total folds/sort complete the core operations. This is not a physical memory/time guarantee. |

`Router.Represents` connects the stored trie to its ordered model table and the
next ordinal to that table's length. Build establishes it; each append preserves
it. The table is proof-level information, not a hidden runtime reference scan.
The trie itself indexes shared prefixes and explores compatible branches.

The theorem has no fixture-size or path-length bound. Concrete GET, literal,
parameter, wildcard, and registration examples witness inhabited input domains.
Parameter lists have unique keys and represent finite maps; their structural
equality is stronger than the contract's map equality independent of key order.

## Release evidence

| Required evidence | Present and checked |
| --- | --- |
| Complete proofs and trust audit | Root imports build the proof/regression modules; warnings are errors. Main-theorem axiom guards permit only `propext`, `Classical.choice`, and `Quot.sound`. Fresh kernel replay passed; no unfinished proofs, custom axioms, or native proof shortcuts were found in project Lean sources. |
| Adapter and CLI behavior | [AdapterTests.lean](../../../AdapterTests.lean) and [adapter_cli.py](../../../tests/adapter_cli.py) cover all 20 scenarios/52 lookups, 30 rejected inputs, and 14 failed-registration sequences, plus grammar/schema/formatting and retained-state checks. |
| Pinned compatibility comparison | [compare_hono.py](../../../tests/compare_hono.py) covers the contract corpus plus 32 fixed-seed generated scenarios: 468 lookups, 98 appends, 467 agreements, one exact D1 observation, and no unexpected differences. Raw retained Hono results are checked again after later operations. |
| Deliberate fault checks | [comparison_tests.py](../../../tests/comparison_tests.py) rejects missing/reordered/duplicated/wrong-capture/type results and changed D1 evidence. The [comparison walkthrough](comparison-milestone.md) records end-to-end deduplication and other output faults; earlier walkthroughs record implementation mutations rejected by proofs. |
| Reproducible separate measurements | [Benchmark runners and settings](../../../benchmarks/config.json) separate fresh construction from lookup on a built router, with shared-prefix and overlapping workloads. The [raw example report](../../../benchmarks/example-results.json) preserves samples, checksums, input/source/binary hashes, compiler/runtime metadata, and the explicit wording-only post-run metadata correction. |
| Maintainer explanation | The [walkthroughs](../../../README.md) explain the theorem, proof boundary, capture behavior, insertion invariant, comparisons, and timings; [editable diagrams](../../diagrams/README.md) accompany them. |

The Hono baseline is raw `TrieRouter` at
`5ca49b0720755c585c9a9835f0a479ceea36fb52`, with a verified clean checkout.
**D1 remains disclosed:** `GET /:__proto__` at `/alpha` must capture the string
`"alpha"`; this pinned Hono observation returns `{}` instead. The exact witness
is recognized separately, and never changes the normative Lean expectation.

The benchmark example's input hash, sample checksums, summaries, and native
binary hash were independently checked. Only the recorded driver-description
hash differs from measurement time, exactly as its `postRunMetadataEdits` states.
Construction receives parsed components in Lean and text in Hono; lookup includes
a result sink. Warm caches, sample spread, and reclamation differences are
documented in the [benchmark walkthrough](benchmark-milestone.md). No timing
threshold determines correctness or release readiness.

## Reproduce the local checks

Use Lean from `lean-toolchain`, Python's standard library, Bun `1.4.0`, and a
clean pinned Hono checkout at `../hono`. With an asdf Bun shim, prefix Python
commands with `ASDF_BUN_VERSION=1.4.0`. The comparison walkthrough also documents
the isolated `--fetch` option.

```sh
lake build
lake exe hono-lean
lake exe adapter-tests
python3 tests/adapter_cli.py
python3 tests/comparison_tests.py --hono ../hono
python3 tests/compare_hono.py --hono ../hono
python3 benchmarks/tests.py --hono ../hono
lake env leanchecker --fresh HonoLean
```

To record another full timing run, use `python3 benchmarks/run.py --hono ../hono`.
CI is configured for proof replay, adapter/comparator tests, the pinned
comparison, and benchmark smoke checks without machine-speed thresholds.

## Scope that remains outside v1's claim

Text/JSON recognition, rejection behavior, formatting, and the CLI are tested,
not formally verified. Differential tests are finite evidence, not universal
Hono equivalence. Measurements establish no complexity or performance theorem.
Hono's HTTP application/handlers, authorization, resource exhaustion resistance,
and compiler/runtime/machine correctness are outside the proof. These are
explicit boundaries from the specification, rather than unfinished required v1
implementation milestones.
