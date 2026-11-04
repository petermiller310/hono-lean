# v1 examples and decisions

These examples explain [SPEC.md](../../SPEC.md). The exact inputs and expected outputs
live in [examples/v1.json](../../examples/v1.json): 20 scenarios, 52 lookups, and 30
inputs the future text adapter must reject. This corpus is a contract, not a
formal proof or a report that hono-lean v1 is implemented.

## 1. Return every matching registration

Register these routes in this order:

| Ordinal | Method | Pattern | Handler |
| --- | --- | --- | --- |
| 0 | ALL | `/students/*` | `log` |
| 1 | GET | `/students/:id` | `read` |
| 2 | GET | `/students/new` | `new` |

`GET /students/new` must return:

```json
[
  {"registration": 0, "handler": "log", "params": {}},
  {"registration": 1, "handler": "read", "params": {"id": "new"}},
  {"registration": 2, "handler": "new", "params": {}}
]
```

The parameter matches the text `new`; the literal route does not defeat it.
The matching core chooses a list. Whether a handler later stops middleware
execution is outside this project. Case: `overlap-keeps-all-matches`.

## 2. Registration order beats traversal order

Register the literal first, wildcard second, and parameter third. The same
request must then return `new`, `log`, `read`. A trie may discover those matches
in another order internally, but must return registration order.
Case: `order-follows-registration`.

## 3. Keep captures local to each match

For `GET /students/s1`, two registrations can produce different maps:

| Pattern | Captures |
| --- | --- |
| `/:kind/:id` | `{"kind": "students", "id": "s1"}` |
| `/students/:studentId` | `{"studentId": "s1"}` |

Neither route inherits the other's names. The same principle applies across
requests: looking up `s2` later cannot change a retained `s1` result.
Cases: `branch-capture-isolation`, `same-shape-different-names`, and
`request-and-registration-sequence`.

## 4. A wildcard can consume nothing; a parameter cannot

| Pattern | Request path | Result |
| --- | --- | --- |
| `/students/*` | `/students` | Match, no captures |
| `/students/*` | `/students/s1/worksheets` | Match, no captures |
| `/students/*` | `/studentship` | No match |
| `/students/:id/*` | `/students` | No match; `id` needs a segment |
| `/students/:id/*` | `/students/s1` | Match with `id = "s1"` |
| `/` | `/students` | No match; the root is exact |
| `*` or `/*` | `/` | Match; these are global wildcard aliases |

There is no wildcard capture value. Cases: `terminal-wildcard`,
`parameter-before-wildcard`, `root-is-exact`, and `global-wildcard-aliases`.

## 5. Identity belongs to registrations

Register `GET /students/:id -> same` twice. Looking up `/students/s1` must return
two results, with ordinals 0 and 1, both labeled `same` and capturing `id = "s1"`.
Deduplicating by handler or pattern would lose an actual registration.
Case: `duplicate-registrations`.

## 6. A supported request that misses differs from unsupported input

`GET /missing` is valid and may return `[]`. `/students/`, `/a//b`,
`/students?limit=2`, and `/a%2Fb` are outside the text grammar and must produce an
`invalid_request` error. The adapter never silently repairs them.

`HEAD /students` does not select a `GET /students` registration. An `ALL` route
does match HEAD. We are defining raw matching, separate from Hono's HTTP dispatch
and URL normalization. Cases: `no-head-fallback`, `methods-and-all`, and
the fixture's `rejected` array.

## 7. Prove the algorithm independently of its input adapter

The main v1 theorem will compare two functions on parsed data: a reference that scans
the registrations and a trie that indexes shared prefixes. A human can read the
simple rules, and Lean will check that the trie implements them for every valid
finite input, including inputs larger than this example corpus.

The text adapter translates `/students/new` into segments. V1 requires tests for
that translation and for errors, but does not formally verify the adapter. Public
claims must say the matching core is verified and name this boundary.

## 8. Known baseline difference D1: a parameter name is data

At the pinned Hono revision, register `GET /:__proto__ -> capture`, then look up
`GET /alpha`.

| Implementation or contract | Captures |
| --- | --- |
| This specification | `{"__proto__": "alpha"}` |
| Pinned Hono `TrieRouter` observation | `{"__proto__": {}}` |

Our rule requires the parameter to retain the captured string. The name is valid
under the declared grammar, so dropping it from the domain merely to make the
comparison pass would obscure the decision. We retain this rule and disclose the
specific compatibility difference. This observation is limited to the pinned raw
trie; it does not establish a security vulnerability or behavior of other versions.

Case: `parameter-name-is-data`. Its `expected` is the Lean contract. Its separate
`baselineExpected` records the Hono observation for D1, and never substitutes for
the result that the Lean implementation must produce.

## How to read and use the machine-readable corpus

Each scenario starts with a fresh router. Initial `routes` assign ordinals from
zero. A step either looks up a request or appends a registration. Expected match
lists include ordinals so duplicates and ordering remain observable. Retain
lookup results and compare them again after later steps to catch accidental
mutation. Compare parameter maps by their own key/value entries, ignoring key
iteration order and JavaScript backing-object prototypes.

The rejected-input examples specify future adapter behavior, not Hono behavior.
For failed registration, future adapter tests must also show that the old router
still works and the next valid registration receives the unconsumed ordinal.

An initial one-off check against the clean local checkout at the pinned revision
found 51 agreeing lookups and the one exact D1 difference. Retained results stayed
unchanged after later operations. The 30 rejected examples were checked for
consistency with the declared grammar; no hono-lean adapter exists yet. A reusable
comparison harness is part of the implementation milestones, not part of this
documentation change.
