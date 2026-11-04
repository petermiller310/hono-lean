# Literal positive-lookahead checkpoint audit

The checked claim concerns the selected actual `url.ts`60/62/67 operations and
direct closed builtin execution of their produced matcher. It is not a complete
`getPattern`, cache-history, exported-call, router or native-engine theorem.

## Identity and independent contracts

The target remains Hono revision `5ca49b0720755c585c9a9835f0a479ceea36fb52`.
`verification/getpattern-lookahead/source.py` checks 315 pinned blobs and these
exact line 67 spans:

| Fragment | Bytes | Half-open source span | SHA256 |
| --- | --- | --- | --- |
| Constructor |38|`[1679,1717)`|`b1414ae969810ebcf84d2786a02dc8fdd4f62e5e2fd5c1e40cbc60266f0040de`|
| Tuple |60|`[1658,1718)`|`a7b7bf89759e05f0d350327d7f73534a2f79c9b0ee7b845369ef235ec65faae8`|
| Complete line |75|`[1644,1719)`|`ee30569e15fe6a07bba31f61a69d2c98d921beac537c0f9fdfdbcc0dfe2ebaac`|

The checker also pins the complete actual60/62 declarations and verifies the
already retained576-byte body, including the exact older Lean string literal.
The new source theorem reuses that body's proved parse and structurally selects
its nodes. Ancestor guards and branch reachability remain outside this selection.
Source identity is externally checked; general source/frontend adequacy is open.

The independent matching relation requires a nonempty in-range prefix followed
by slash, nonempty ASCII alphanumeric `next`, and arbitrary suffix. Range
endpoints are ordered ASCII alphanumeric units; interior punctuation is allowed.
The resulting match excludes the entire assertion. Public source assumptions
contain only initial realm, label, next, constructor and representation facts.
The label producer and key expression derive their own intermediate values.

Constructor/exec contracts specify ordinary object identity, prototype,
initialized `lastIndex`, compiled records, current lastIndex Get, exact match
arrays/metadata and old-state frames. Existing ABI/records are preserved by an
additive tagged-record state. Model well-formedness scans are explicit metadata
checks, not upstream algorithm work. General effects/abrupt-state preservation,
native getter adequacy and general regex semantics are not claimed.

## Reproducible gates

Run from the repository root with the pinned clean Hono checkout at `../hono`:

```sh
lake build
lake env leanchecker --fresh HonoLean
python3 verification/getpattern-lookahead/source.py --hono ../hono
HONO_NODE=/opt/homebrew/opt/node@22/bin/node python3 verification/getpattern-lookahead/tests.py --hono ../hono
python3 verification/getpattern-lookahead/audit.py
python3 verification/getpattern-lookahead/preserve.py
```

The absolute Node path selects the installed 22.22.2 locally; elsewhere select
that exact runtime through `HONO_NODE` or PATH. The harness requires Bun 1.4.0.
CI uses the same pins. All advertised theorem names must resolve to the actual
Lean environment and pass a transitive standard-only axiom audit. The new conditional
cluster is recorded in `verification/proofs.json`.

The integrated warnings-as-errors build passes 783 jobs (45153). The final
declaration audit 83465 resolves 165 names: 104 theorems and 61 explicit definitions.
All 104 theorems pass the transitive check allowing only `propext`,
`Classical.choice` and `Quot.sound`. It also checks the actual retained body
constant and the parsed-node/execution links. Final focused9816c0 passes 93 jobs,
with the factored source examples checked in381ms. New source Examples.olean is
196KB; these witnesses avoid the earlier milestone's whole-VM reduction cost.

An intermediate audit 69807 passed the 163 names then advertised. Root's later
read-through caught two public definitions indented inside a mutual block that
the name extractor had missed. The extractor now accepts indentation, both
definitions are included, and final 83465 passes the complete165-name list.
Independent review repeated the corrected extraction. No theorem was dropped,
and no Lean statement, proof or model changed for this metadata repair.

The finite suite has nine groups:252 grammar fixtures/2520 queries, assertion
boundaries, cross-gap ranges, eight current-lastIndex descriptors, four supported
source mutations, six explicit unsupported-grammar frontiers, identity tampering,
six actual-full-module controls per engine, and an invalid current constructor.
Normal cases total 270 contexts/2700 queries. Faults, refusals and native-only
controls are categorized separately; they do not broaden D1 or any allowlist.
Final 23914 passes all nine groups in9.401s. The frozen invocation suite 7696
passes 11 groups in12.990s. Pinned comparison 96028 retains 467 agreements, one
exact D1 difference,98 appends and zero unexpected failures.

The Python oracle decomposes at the first slash independently of the VM's greedy
range scan. Native selected-source extraction, Function wrapper, observation,
TypeScript loading, module instantiation and engine adequacy remain unverified.
Entire unmodified `url.ts` controls are separately tagged native-only and use
distinct keys to avoid sharing mutated cached matchers between fixtures.

One intermediate identity-tamper test originally mutated the old generated
guard's first return string instead of the body literal actually used here.
That test failed; its target was repaired to mutate `pinnedBody` itself. The
checker was not weakened. A resumed focused build also exposed proof plumbing
around a tuple alias and an Except reduction; repairs preserved the statements
and model. Historical failures and final successful handles remain in progress.

## Preservation and remaining obligations

The baseline is local commit0535f29. All 369 previously tracked Lean modules,
38 old proof clusters,37 old additional assumption slices,30 obligation statuses
and theorem arrays,36 routing statuses, restricted SPEC, fixed target/catalog,
D1/engine controls, old source/harness artifacts and historical benchmarks remain
unchanged. The new proof cluster is conditional; unconditional runtime claims
remain empty and full-runtime verification stays open.

Resume with real 67 branch reachability, cache Set/source74 and lexical-closure
integration on the same carried state. Continue full routing and the entire
published runtime catalog after that. Pausing at this checkpoint does not change
the original completion criteria.
