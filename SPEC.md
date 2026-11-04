# hono-lean specification

This is the contract for the verified router: the supported inputs, the matching
rules, and what the proofs must show. Every proof obligation below is complete.
The [router guide](docs/router/README.md) lists the theorems that meet each one,
and the [walkthroughs](docs/router/) explain them.

## 1. Goal and claim

Build a small Hono-style trie router and prove its matching behavior against
explicit rules. Keep the implementation, specification, and proof boundaries
small enough for a maintainer to explain.

The intended release claim is:

> For every valid finite route table and parsed request in the v1 domain,
> trie lookup returns exactly the matching registrations, with their correct
> handler labels and parameter maps, in registration order.

This claim concerns the Lean matching core. It does not verify Hono's TypeScript,
an HTTP application, or every possible failure of a running program.

## 2. Supported inputs

### Methods

- Request methods are nonempty ASCII uppercase letters: `[A-Z]+`, except `ALL`.
- A route selects either one exact request method or the special selector `ALL`.
- Matching is case-sensitive. There is no conversion from `get` to `GET`.
- Custom methods such as `PURGE` are supported within this alphabet.
- `ALL` matches every supported request method, including `HEAD` and `OPTIONS`.
- `HEAD` does not fall back to `GET`. That would be HTTP application behavior.

### Request paths

Text examples use this deliberately restricted grammar:

```text
segment      = one or more ASCII letters, digits, underscores, or hyphens
request-path = "/" | "/" segment ("/" segment)*
```

The parsed core sees a list of segments. `/` becomes `[]`; `/students/new`
becomes `["students", "new"]`. Each segment satisfies the grammar above.

Paths are case-sensitive. No empty segments, trailing slashes except `/`,
percent encoding, dot segments, dots inside segments, Unicode path characters,
query strings, fragments, or full URLs are accepted. Inputs are never trimmed,
decoded, case-folded, or otherwise normalized into the accepted domain.

### Route patterns

```text
name      = an ASCII letter or underscore, then zero or more letters,
            digits, or underscores
component = segment | ":" name
pattern   = "/" | "*" | "/*"
          | "/" component ("/" component)* ["/*"]
```

A parsed pattern is a list of literal or named-parameter components, plus a
Boolean indicating whether it accepts a remaining suffix. `*` and `/*` are
aliases for an empty prefix that accepts any suffix. `/` is an exact empty path.

A wildcard appears at most once and only as the final whole component. It
does not create a captured parameter. Parameter names must be unique within
one route; different routes may use different names at the same position.
Names such as `constructor` and `__proto__` are ordinary names, not magic keys.

Excluded patterns include `/:id?`, `/:id{[0-9]+}`, `/assets*`, `/a/*/b`, and
`/:id/:id`. The first release does not reinterpret these as literal paths.

### Registrations and identity

A route registration has a method selector, parsed pattern, and opaque string
handler label. Labels can repeat and may be empty. No handler code is executed.

The router assigns each registration an ordinal starting at zero. Identity is
the registration occurrence, not its handler label or pattern. A repeated
registration appends another occurrence; it never replaces an earlier one.

## 3. Matching rules

For one registration and one request:

1. The method must equal the request method, or its selector must be `ALL`.
2. Consume pattern components and request segments from left to right.
3. A literal consumes one segment with exactly the same text.
4. A parameter consumes exactly one segment and binds its name to that text.
   A parameter never consumes zero segments or a slash-separated suffix.
5. After the pattern prefix is consumed, an exact pattern requires no remaining
   segments. A wildcard pattern accepts zero or more remaining segments.
6. Otherwise the registration does not match.

Matching produces one parameter map for that registration. Its keys are exactly
the parameter names in that pattern, with no keys inherited from another route
or request. The root pattern matches only `/`. A wildcard pattern such as
`/students/*` matches `/students` as well as `/students/s1/worksheets`.

For a route table, consider every registration and return all matches in
ascending ordinal order. A literal match does not suppress a parameter or
wildcard match. There is no "best route wins" rule and no early stopping.
The route `/students/:id` captures `id = "new"` for `/students/new`, even when
an exact `/students/new` registration also exists.

## 4. Results and operations

A successful lookup returns a list of results containing:

- `registration`: the ordinal of the matching registration;
- `handler`: its handler label, unchanged;
- `params`: its parameter map, empty for a route without parameters.

Result-list order is observable. Parameter-map equality compares keys and
values, independent of map iteration or JSON object-key order. No match means
an empty result list. It does not imply an HTTP response or status code.

The core exposes these pure operations, with concrete Lean names chosen later:

- `build(routes)`: construct a router from the ordered route table;
- `register(router, route)`: return a new router with one appended registration;
- `lookup(router, request)`: return matches without changing the router.

Registration after a lookup is supported. Lookup history must not change future
results, earlier results, or the next registration ordinal. Registering on a
router also leaves the previous router usable with its original behavior.
There is no deletion, replacement, handler execution, or middleware control flow.

The text adapter rejects malformed or unsupported inputs. Invalid route input
has category `invalid_route`; invalid request input has category
`invalid_request`. Human-readable error messages are not fixed by this spec.
Invalid lookup input is an error, not an empty successful result. A failed build
returns no partial router; a failed registration leaves the router unchanged and
does not consume an ordinal. These are adapter requirements, outside the core
proof boundary described below.

## 5. Proof obligations

Define matching rules independently of trie traversal. A simple reference
implementation scans the route list and follows those rules. Prove that this
reference implementation returns exactly the rule-defined results, then prove
the trie agrees with the reference.

The headline theorem has this informal shape:

```text
For all valid routes and parsed requests:
  trieLookup(build(routes), request) = referenceLookup(routes, request)
```

Equality includes registration ordinals, handler labels, ordered results, and
parameter maps. It must account for every finite table, path length, and segment
length in the accepted domain; test-corpus sizes are not theorem hypotheses.

The proof development must establish:

| Obligation | Required meaning |
| --- | --- |
| Reference correctness | The reference follows the matching rules, with a unique capture map for a matching registration. |
| Soundness | Every returned result belongs to a matching registration with its correct label and captures. |
| Completeness | Every matching registration is returned. |
| Order and multiplicity | The output is exactly the registration-ordered list; one result per matching occurrence, including duplicate labels and patterns. |
| Insertion invariant | Building and appending preserve the trie representation of the ordered registrations. |
| Incremental correctness | Looking up after appending agrees with reference lookup of the appended route table. |
| Lookup isolation | Lookup is pure; previous requests cannot change captures, the router, or retained results. |
| Totality | The core operations terminate on valid finite inputs. This does not promise unlimited physical memory or execution time. |

Some obligations may follow from the headline theorem or pure representation,
rather than needing redundant standalone theorems. State that connection clearly.
Include concrete witnesses that the accepted domain and theorem hypotheses are
satisfiable. Do not assume the desired lookup result as a hypothesis.

The trie must actually index shared path prefixes and search compatible branches.
It must not delegate lookup to a full-table reference scan. The reference may
share elementary types and string equality with the trie, but must not be a
wrapper around the same traversal. A formal complexity proof is not required.

## 6. Proof boundary and other evidence

The v1 theorem begins with valid, already-parsed inputs and ends with the returned
match list. V1 requires tests for the text and JSON decoding, rejection behavior,
formatting, and CLI adapters. The post-v1
[path-parser extension](docs/router/path-parser-walkthrough.md) now proves request-path
recognition and exact decomposition. The [method-parser extension](docs/router/method-parser-walkthrough.md)
also proves exact method recognition, spelling, and rejection category.
The [pattern-parser extension](docs/router/pattern-parser-walkthrough.md) proves exact
pattern decomposition, unique parameter names, and terminal wildcard placement.
The [record-parser extension](docs/router/record-parser-walkthrough.md) composes these
field contracts into exact route and request records. The
[text-build extension](docs/router/text-build-walkthrough.md) proves ordered construction
and whole-build rejection. The [text-registration extension](docs/router/text-registration-walkthrough.md)
proves success/failure steps and finite histories. The
[text-lookup extension](docs/router/text-lookup-walkthrough.md) composes these contracts
with the independent matching rules. The composed claim begins with
`TextRoute`/`TextRequest` records of Lean strings and ends with `List Match`.
JSON decoding/encoding and the CLI remain tested boundaries.
This boundary must appear beside public claims, not only in a footnote.

Lean's logic and proof checker remain part of the assumptions. Executing native
code also relies on the compiler, runtime, and machine. There is no v1 claim of
verified performance, resource exhaustion resistance, authorization correctness,
or correctness of a surrounding web application.

The release must build all proof modules, reject unfinished proofs, and audit
the main theorem's axiom dependencies. Ordinary Lean logical axioms are allowed;
custom axioms, unfinished proofs, and native-evaluation trust must not silently
stand in for the matching proof.

## 7. Hono comparison and release criteria

Comparison target: Hono's raw `TrieRouter` at revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52` in
[honojs/hono](https://github.com/honojs/hono/tree/5ca49b0720755c585c9a9835f0a479ceea36fb52).
This is a reproducible baseline, not a claim about the latest Hono release or
MathMigo's installed version.

Pass methods and canonical path text directly to `TrieRouter.add` and
`TrieRouter.match`. Do not compare HTTP response dispatch, `SmartRouter`, URL
normalization, HEAD fallback, or `strict: false` application behavior. Attach the
registration ordinal to each Hono handler payload and normalize results into
section 4's shape before comparing. Represent maps by their own key/value entries;
key iteration order and backing JavaScript object prototypes are not part of the
model. Do not coerce captured values or drop keys to make a comparison pass.

Known baseline difference D1: `GET /:__proto__` looked up at `/alpha` must capture
`{"__proto__": "alpha"}` under this specification. The pinned Hono trie returns
`{"__proto__": {}}`. Keep the correct string capture in the Lean contract and
record the exact baseline observation separately. This is a documented difference
in the raw trie, not a claim of a security vulnerability or a finding about every
Hono version. V1's public compatibility statement must disclose D1.

The release requires:

- the rule/reference and trie correctness proofs above;
- all contract examples, plus generated compatibility cases and request/register
  sequences, checked against the pinned Hono baseline, with D1 reported separately;
- adapter tests for rejected inputs and atomic failed registrations;
- deliberate fault experiments showing relevant checks catch missing matches,
  reversed ordering, wrong captures, and accidental deduplication;
- reproducible benchmarks separating construction and lookup, including both
  shared-prefix and heavily overlapping cases, with no throughput claim derived
  from proof correctness alone;
- an explanation of the theorem, its assumptions, and one traversal invariant
  that the maintainer can follow.

A discrepancy with Hono is investigated and recorded. Neither the expected
examples nor the specification should be silently changed to hide it. Out-of-
domain inputs that Hono accepts are intentional scope exclusions, not Hono bugs.
An exception records one exact observed case; it never exempts the Lean matcher
from the normal contract or permits skipping arbitrary comparison failures.

## 8. Implementation sequence

1. Literal paths: formal matching rules, reference matcher, literal trie, proof.
2. Methods and `ALL`: extend the matching rule and correctness theorem.
3. Named parameters: captures and overlapping literal/parameter branches.
4. Terminal wildcards: zero-length and longer suffixes, ordered combined matches.
5. Incremental registration, adapters, comparison harness, and release evidence.

Each milestone includes its proof and a plain-English walkthrough before the
next feature. Agents should explain any proposed behavioral or scope change,
including the example motivating it. Proof difficulty is not permission to
quietly narrow the accepted domain or weaken the guarantee.

See [the examples](docs/router/examples.md) for the decision walkthrough and
[examples/v1.json](examples/v1.json) for the exact expected cases.

## Sources

- [Hono routing behavior](https://hono.dev/docs/api/routing)
- [Hono router implementations](https://hono.dev/docs/concepts/routers)
- [Pinned trie source](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts)
- [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
