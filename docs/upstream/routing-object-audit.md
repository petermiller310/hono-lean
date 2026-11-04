# Routing behavior and object-semantics audit

The [routing worklist](../../verification/routing-behaviors.json) now records **36
candidate behavior units** at Hono revision
`5ca49b0720755c585c9a9835f0a479ceea36fb52`. It is an initial source/test map, with
zero source-connected proofs of those full routing units. It does not claim a
complete behavioral denominator or that every router implements one universal
matching contract.

Each unit records domains to specify, observable results/errors/mutations,
source ranges and file hashes, representative test ranges, and open obligations.
The [structural catalog](../../verification/coverage.json) remains the wider export
inventory. Existing restricted Lean-router proofs and individual helper proofs
do not automatically close these upstream behavior units.

## Preserve the implementation differences

| Component | Contract distinctions visible at the pin |
| --- | --- |
| TrieRouter | Traverses shared nodes; captures pass through ordinary temporary objects and null-prototype outputs; sorts handler sets using module-global Number scores |
| RegExpRouter | Rejects some ambiguous route combinations; compiles matchers on first lookup; returns parameter-index maps plus a stash; later registration rejects |
| SmartRouter | Replays registrations through ordered candidates; falls back only on `UnsupportedPathError`; finalizes selection and delegates later matching |
| LinearRouter | Scans registrations; accepts one trailing slash in literal matching; mixed labels/stars can reject during lookup |
| PatternRouter | Compiles each registration into a regexp with named groups; accepts trailing slashes; recorded duplicate parameter names reject during registration |
| PreparedRegExpRouter | Uses precompiled matcher/relocation structures; supports a distinct handler-addition lifecycle; also exports initialization and serialization helpers |
| Default Hono | Honors its custom-router option or chooses SmartRouter with RegExpRouter then TrieRouter |
| Quick / tiny | Install their preset routers after the base constructor: Linear-first SmartRouter or PatternRouter respectively |

The published RegExpRouter entry also exports `PreparedRegExpRouter`,
`buildInitParams` and `serializeInitParams`. Their constructor data, relocation,
wildcard/ALL updates, result aliases and serialization behavior remain explicit
work. Tests that serialize and evaluate initialization text are finite evidence,
not a verified serializer or a full JavaScript evaluator.

The common suite contains 100 literal test cases. Its helper converts parameter
indices/stashes into parameter objects, so agreement there does not establish
identical raw result representations. The worklist preserves exact skip
profiles: Linear skips 15 selectors, Pattern 4, RegExp 7 and Prepared 7;
Trie and the default Smart configuration declare none. These are fixture
declarations, not test executions or universal compatibility results. Prepared's
fixture also wraps construction behind a route-buffering builder.

Open work includes exact optional/regexp/wildcard domains; ordering and duplicate
occurrences; errors and state after failure; post-match registration; retained
result references and caller mutation; reserved names; numeric limits; and
application-versus-raw-router behavior. Unsupported paths can fail at different
phases in different implementations. SmartRouter can finalize on a miss, so
first-request-dependent selection and later delegated errors need their own
lifecycle contract.

## The object rules behind D1

The authority is the official ECMA-262 2025 snapshot.
[OrdinaryGet](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinaryget)
checks an own descriptor, otherwise traverses the prototype chain while retaining
the receiver. Data descriptors supply their value; accessors invoke their
getter with that receiver.
[OrdinarySetWithOwnDescriptor](https://tc39.es/ecma262/2025/multipage/ordinary-and-exotic-objects-behaviours.html#sec-ordinarysetwithowndescriptor)
can delegate to a prototype. Writable data permits receiver-side own data
creation/update; non-writable data or incompatible receiver descriptors reject.
An inherited accessor invokes its setter instead of creating ordinary own data.
Existing writable data retains its other attributes; configurability is not a
condition for a simple writable-value assignment. These dispatch steps are why
a map keyed only by strings is insufficient.

In this edition the legacy
[`__proto__` accessor](https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-object.prototype.__proto__)
appears in **§20.1.3.8**, labeled normative optional/legacy; using an older
Annex-B location would misidentify the reference. Its getter returns the
receiver's internal prototype after object conversion. Its setter ignores a
right-hand value that is neither an object nor null, including a captured
string. The D1 interpretation therefore requires the standard optional accessor
to be present. A realm without it has a different property path.

[`Object.create(null)`](https://tc39.es/ecma262/2025/multipage/fundamental-objects.html#sec-object.create)
allocates an ordinary object with the specified null prototype. With no second
argument, it applies no property descriptors. The underlying
[creation operations](https://tc39.es/ecma262/2025/multipage/abstract-operations.html#sec-makebasicobject)
start with no own properties and make the object extensible. This does not make
the object immutable or prevent later own `__proto__` data.

## What the recorded capture actually contains

The original D1 fixture is unchanged: register only
`GET /:__proto__ -> capture`, then look up `GET /alpha`. The restricted contract
expects an own string value `"alpha"`; the pinned TrieRouter observation has an
own object value, displayed as `{}`. The exact fixture and its controls remain
in [the divergence ledger](../../verification/divergences.json).

The inspected source provides this mechanism:

1. [`node.ts:123`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L123)
   creates an ordinary temporary capture object.
2. Its parameter assignment at
   [`186–191`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L186-L191)
   reaches the inherited setter for that key. The string write creates no own
   property; a subsequent inherited getter reads Object.prototype.
3. [`75–80`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L75-L80)
   copies the looked-up value into a newly allocated null-prototype output.
   There it becomes an ordinary own data property.

**Object.prototype is not an empty object.** Its standard constructor and
methods remain present as non-enumerable properties. Default
[JSON object serialization](https://tc39.es/ecma262/2025/multipage/structured-data.html#sec-serializejsonobject)
selects enumerable own properties; `{}` does not establish the absence of
methods, descriptors, identity or prototype behavior. The local model therefore
uses a projection of relevant descriptors with an explicit frame, rather than
claiming a complete empty standard prototype.

The capture-name controls `id` and `constructor` create own strings in this
setting. That does not establish how the same spelling behaves in another role,
such as a requested method name.

## A separate raw-method finding

Fifteen isolated Bun 1.4.0 observations used one `GET /a` registration and then
looked up each of `constructor`, `toString` and `__proto__`. Each ran in a fresh
process after pin, clean-checkout and all 315 package/source-blob checks.

TrieRouter threw a TypeError while accessing `handlerSet.possibleKeys.length`.
Before throwing, it created an own `params` property on the object below:

| Requested method | Watched object changed |
| --- | --- |
| `constructor` | The Object constructor function |
| `toString` | Object.prototype.toString |
| `__proto__` | Object.prototype |

In each case that property was writable, enumerable and configurable, containing
an empty null-prototype object. RegExpRouter and the default Smart configuration
returned `[[], []]`; Linear and Pattern returned `[[]]`, without changes to those
three watched objects. No claim about every other possible effect is made.

These finite observations have their own `RAW-METHOD-INHERITED-KEYS` work item.
They are distinct from capture-name D1, add no comparison exception, and are not
a whole-router source proof or broad security claim. Process isolation prevents
the observed builtin mutations from contaminating another observation.

The durable probe runs exactly one case per invocation:

```sh
ASDF_BUN_VERSION=1.4.0 bun verification/routing-method-probe.ts ../hono TrieRouter constructor
```

Its JSON matches a worklist record after removing that record's `id`. Records
are at `nativeMethodObservations.records`; their complete route/request and
before/after descriptor observations are retained.

## Proof review and remaining boundaries

[Objects.lean](../../HonoLean/Upstream/ECMA2025/Objects.lean) separates descriptor
lookup, receiver-aware accessors, writable data and extensibility checks. Its
string-RHS theorem follows descriptor dispatch rather than recognizing a key
and assuming the D1 result. The local composed example establishes that property
mechanism in its declared model. It does not execute the complete extracted
Trie Node program or prove JSON serialization.

Native interpretation of the projected realm still requires the standard
relevant descriptors, admissible frame/heap references and sufficient traversal
fuel. Unique keys and valid references alone do not establish an acyclic,
fully initialized JavaScript realm. User functions, proxies, symbol keys,
prototype mutation, general enumeration and detailed exception behavior remain
outside this small model. The special immutable prototype behavior of the real
Object.prototype is not exercised by an ignored string setter argument.

[CreateNullObject's contract](../../HonoLean/Upstream/CreateNullObject/Correctness.lean)
is independently stated over the returned address and complete model state:
one new empty-own/null-prototype/extensible object, with previous cells,
environment and array heap preserved. The source theorem parses the entire
pinned one-line module and assumes `StandardObjectBinding`. That is a model
binding condition; actual global lookup and mutable `Object.create` dispatch
still require interpretation assumptions. Freshness is relative to allocated
heap cells, with wellformed native states excluding forged dangling references.

This inspection found no circular contract or conflicting result case in those
local definitions. Source extraction/freshness remains external tooling;
ordinary Lean axiom guards do not prove a complete frontend, initialized realm
or engine. The wider routing worklist remains open until the relevant source
traces and independent contracts are connected explicitly.
