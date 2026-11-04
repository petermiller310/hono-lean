# What the Hono verification claim depends on

The completed teaching project proves the restricted [text-router
contract](../../SPEC.md). Its theorems start with Lean route/request records and end
with an ordered list of matches. They do not establish that the original Hono
TypeScript follows that contract. The [full verification
goal](hono-verification-goal.md) adds that separate obligation for the exact
revision `5ca49b0720755c585c9a9835f0a479ceea36fb52`.

This audit keeps three questions separate: what the contract promises, what Lean
has checked, and why the checked program represents upstream execution. A
correct proof can still have an inappropriate specification or an incomplete
language model. Passing comparisons answer a narrower, fourth question: whether
the implementations agreed on the observations we actually ran.

## Read the ledgers together

| Record | What it records | What it does not establish |
| --- | --- | --- |
| [Target](../../verification/target.json) | The authoritative upstream commit and intended package scope | Completed coverage |
| [Coverage](../../verification/coverage.json) | Export/source/public-behavior candidates and missing evidence | A proof from an AST inventory |
| [Assumptions](../../verification/assumptions.json) | 28 initial trust, modeling, source-link and host obligations, with witnessed source locations | 28 accepted axioms |
| [Divergences](../../verification/divergences.json) | Exact D1 evidence and nine other classified behavior differences | Nine additional comparator exceptions |

`explicit_tcb` identifies something the argument trusts, such as Lean's kernel.
`candidate_precondition` proposes a domain or environment restriction that still
needs review. `open` means the obligation is unresolved. A source reference
identifies an actual use at this pin; it is not an exhaustive dependency proof.
Each behavior in coverage must eventually identify its complete dependency set.

The TypeScript inventory scanner is a discovery tool using TypeScript 6.0.3. It
does not verify the TypeScript compiler or settle dynamic method creation,
external imports, runtime reflection or callback behavior. Those remain explicit
review tasks. Erased type declarations have a separate classification; runtime
proofs do not establish TypeScript type-system soundness.

## The first source connection: `splitPath`

The selected upstream function is
[`src/utils/url.ts:8–14`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/utils/url.ts#L8-L14).
It splits a string at `/`, removes one initial empty component, and returns the
same local array. It does not validate the restricted route grammar or decode
URL escapes. For example, `/` becomes `[""]`, `//a` becomes `["", "a"]`, and
`/a/` becomes `["a", ""]`; the empty string becomes `[]`.

The prototype has a small [syntax](../../HonoLean/Upstream/SourceSubset/Syntax.lean),
[parser](../../HonoLean/Upstream/SourceSubset/Parser.lean), and
[interpreter](../../HonoLean/Upstream/SourceSubset/Semantics.lean). It parses the
embedded upstream declaration rather than only executing a handwritten AST.
[Theorems](../../HonoLean/Upstream/SourceSubset/SplitPath.lean) connect that parsed
text to a contract: components rejoin to the input, none contains a slash, the
split limit is applied, and then one initial empty component is removed.

That source-to-model connection has a precise boundary:

- **Strings are UTF-16 code units.** Inputs are lists of `UInt16`, including lone
  surrogates. The mathematical theorem accepts arbitrary finite lists; a native
  string interpretation additionally uses `LegalString`, length at most
  `2^53 - 1`. Lean Unicode scalar strings are not substituted for this domain.
- **The split limit matters.** Standard default splitting keeps at most
  `2^32 - 1` components. The model applies that truncation before `shift`, rather
  than treating an unlimited list split as exact JavaScript behavior.
- **The receiver and realm are restricted.** The input is a primitive string;
  relevant string/array methods have their standard behavior, including relevant
  method and `Symbol.split` lookup. No replaced intrinsic or inherited indexed
  property changes the observed operations. TypeScript's `string` annotation is
  not a runtime check enforcing this restriction.
- **Arrays have references and mutation.** Splitting allocates a fresh ordinary
  dense array; indexing and `shift` use a local heap. The model preserves the
  alias through mutation and reads the returned reference. It does not yet give
  semantics to arbitrary holes, getters, proxies or adversarial prototypes.
- **Resources are idealized.** Language-visible limits remain explicit. The
  theorem does not promise enough physical memory or protect against engine
  crashes. No network, Fetch, crypto or other host API is needed for this helper.

The prototype declares ECMA-262, 16th edition (2025), as its language reference.
Auditing the supported operations against that edition is still an open
**model adequacy** obligation. General parser soundness relative to the full
TypeScript/JavaScript language is not established by calculating that one text
parses to one AST. Unsupported syntax must reject; it must not be silently
discarded. In particular, source comments, escapes, automatic semicolon
insertion and type erasure require deliberate treatment as the subset grows.

## Exact bytes and the checking toolchain

[Source metadata](../../verification/splitpath/source.json) records the file hash,
Git blob, selected byte span and function hash. The source file SHA-256 is
`d1f85f414ed8fd3682000499e74e8723139810fd612e1e1a1b4075a52ef91248`;
the function SHA-256 is
`53f73636562b6189de735c3bcd587941b6de4f4038e1651c616ce9c5a0b48652`.
These identify content, not its correctness.

From the repository root, with the clean pinned source checkout at `../hono`:

```sh
python3 verification/splitpath/source.py --hono ../hono
lake env lean HonoLean/Upstream/SourceSubset/SplitPath.lean
```

The first command checks Git identity and regenerates expected artifacts in
memory to detect stale extraction/embedding. Python, Git and that checker remain
an external freshness and identity boundary. The second command checks the Lean
declarations, including parsing the embedded text and the model theorem. Neither
command verifies the entire TypeScript frontend, a distribution bundler, or a
JavaScript engine. Claims about emitted package artifacts will need their own
identity and compilation argument.

Lean's kernel and its ordinary foundations are trusted. Existing axiom guards
permit `propext`, `Classical.choice` and `Quot.sound`; the ledger authorizes no
new source-equivalence or host-correctness axioms. Compiled Lean execution,
Bun, Python, the operating system and hardware are separate execution trust
dependencies. Native tests and benchmark timings do not replace kernel proofs.

## Differences that must stay visible

**D1 remains the one exact comparison exception.** With only
`GET /:__proto__ -> capture`, a raw TrieRouter lookup of `GET /alpha` returns an
own `__proto__` value of object type, observed as `{}`. The restricted contract
requires the string `"alpha"`. The ledger copies the complete existing
[`parameter-name-is-data` fixture](../../examples/v1.json), records its canonical
hash, and retains the `id` and `constructor` controls, which captured `"alpha"`.

The source creates a temporary ordinary object at
[`node.ts:123`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L123),
assigns a parameter at
[`186–191`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L186-L191),
and later reads its key into a null-prototype output at
[`75–80`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L75-L80).
Native controls support the inherited `__proto__` accessor explanation. This is
source inspection and finite execution evidence; a checked source-semantics
counterexample remains open. Arbitrary property names cannot be modeled as
ordinary mathematical map keys without accounting for these operations.

The other ledger entries separate layers and domains:

- Application HEAD matches GET routes, leaves `HEAD` visible to the handler,
  and removes the response body. The raw matcher has its own method contract.
- Default Hono uses SmartRouter with RegExpRouter and TrieRouter. SmartRouter
  finalizes selection on first match and rejects later registration; the raw
  TrieRouter accepted a later append in the recorded observation.
- Optional/regexp parameters and duplicate parameter names are accepted by
  pinned TrieRouter in the recorded cases, beyond the restricted grammar.
- Application registration uppercases method names. Non-strict path handling
  has a trailing-slash rule; `splitPath` alone has different responsibilities.
- Middleware executes callbacks and carries effects. The observed
  `before → handler → after` trace and repeated-`next()` error are outside a
  matcher whose outputs are handler labels.

Those are not automatically defects. Their ledger entries specify the layer,
input, output and evidence level. The non-strict option entry is source
inspection only; the other observations use Bun 1.4.0 and local in-process
requests. None extends D1's allowlist or proves universal compatibility.

The durable [runtime probe](../../verification/trust_probe.ts) reproduces all nine
ledger rows with native observations, including the D1 name controls:

```sh
ASDF_BUN_VERSION=1.4.0 bun verification/trust_probe.ts --hono ../hono
```

It checks the pinned revision, runtime and clean checkout, then compares actual
package/source bytes with pinned Git blobs before importing them. That last
check also catches edits hidden by Git's `assume-unchanged` or `skip-worktree`
flags. It invokes application requests locally, starts no server, and does not
edit the upstream checkout. A changed observation fails against the ledger;
success emits the complete finite evidence as JSON.

## What the rest of the package needs

Routing needs object/prototype semantics, regexp behavior and numeric precision.
For example, the source uses a module-global JavaScript Number score; an
unbounded natural-number registration ordinal needs a representation argument
or a stated bound. No overflow counterexample is claimed by this audit.

Framework proofs also need synchronous throws, non-Error throws, promises,
cross-realm `instanceof`, asynchronous ordering, closure/shared state, repeated
`next()` and arbitrary permitted user-handler effects. Client proxies and DOM
callbacks add further language behavior. Successful string-label handlers do
not model that domain.

Host boundaries include URL/Request/Response/Headers, body consumption and form
conversion, stream backpressure/cancellation, clocks/timers, randomness,
Web Crypto, encodings/JSON, filesystem/network services, WebSockets and each
platform adapter. The assumptions ledger maps representative call sites to
these obligations. Each host model must permit relevant failures and observable
ordering, then support a proof about Hono's use of it. It must not assume the
Hono result we intend to prove. Functional token or crypto-interface proofs
would not establish broad security or cryptographic guarantees.

The next review work is to reconcile those dependencies with coverage, replay
the source-slice proof, audit the chosen language rules, and extend the smallest
unresolved behavior. Closing a model theorem, source identity check, native test,
or host obligation is recorded separately so that one cannot conceal another.
