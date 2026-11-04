# Handler-record construction: independent audit

The target is the complete object argument at
[`src/router/trie-router/node.ts:55–61`](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L55-L61),
Hono commit `5ca49b0720755c585c9a9835f0a479ceea36fb52`:

```ts
{
  [method]: {
    handler,
    possibleKeys: [...possibleKeys],
    score: ++order,
  },
}
```

The [source metadata](../../verification/handler-record/source.json) binds its
exact 116 bytes to the pinned file, including internal indentation, newlines
and trailing comma. SHA-256 is
`42ad4068eecf604957cd2dbb91cb23c617537918b24bd095dcb85ed0b461e41a`.
The private receiver, `.push` lookup and call, and following LF are excluded.
At a real call site, the callee reference and method lookup precede argument
evaluation. This contract starts at the argument's entry state, after such
lookup effects; it does not verify the entire line-55 call.

## Independent structural contract

Let the entry state contain primitive-string method `m`, handler value `h`, a
Set with ordered primitive-string entries `keys`, and integer counter `n`.
Let `O` be the original object-heap length and `A` the original array-heap
length. The independent successful endpoint is:

- Return the fresh outer object at `O`; allocate the inner handler record at
  `O + 1`, and the key array at `A`.
- Both objects are ordinary, extensible, and have the realm's intrinsic
  Object prototype, represented by an already existing object at address 0.
- The outer object has exactly one **own** writable/enumerable/configurable
  data property, `m`, containing the inner reference.
- The inner object has exactly three own data properties with those attributes:
  `handler` contains the original value `h`; `possibleKeys` contains array `A`;
  `score` contains `n + 1`. It has no own `params` property.
- Array `A` contains the ordered Set strings. The Set is preserved, and the
  array is a fresh snapshot rather than an alias of the mutable Set.
- Update the first resolved `order` binding once to `n + 1`. Preserve other
  bindings, old allocated object/array cells, functions and Set cells.

These are record shapes and state equations, not a call to the evaluator.
Descriptor-store list order is a model representation detail; it is not a proof
of native `OwnPropertyKeys` enumeration. “Own” also matters: both objects retain
an ordinary prototype and can expose inherited names. No unregistered-method
miss theorem follows from the outer object having only one own method entry.

The [contract](../../HonoLean/Upstream/HandlerRecord/Contract.lean) states these
shapes independently. Its `Inputs` contains binding, Set-read and existing-root
facts, not an assumed construction result. `replaceOrder` independently
describes first-binding replacement, including preservation of later shadowed
bindings. The
[source proof](../../HonoLean/Upstream/HandlerRecord/Correctness.lean) checks the
actual parse, proves execution and existence, and establishes the exact
`RecordContract` iff theorem. It separately proves descriptor lookup and frame
consequences. No desired endpoint or successful future consumer trace is an
input premise.

## Source order and language specialization

The outer object is allocated first. Its computed key is evaluated and
converted before the nested value. The inner object is then allocated;
`handler` is read and stored, the Set spread completes and is stored, and
prefix increment supplies the score. Finally the outer own method property
receives the inner reference.

The official ECMA-262 2025
[object-initializer algorithms, §13.2.5.4–5](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-object-initializer)
create ordinary objects with intrinsic `%Object.prototype%`, process properties
in source order, and apply ToPropertyKey to a computed name before evaluating
its value. Shorthand and ordinary data definitions create own data properties.
A computed `__proto__` is data, while a noncomputed colon definition with that
name has separate prototype-initializer semantics. The latter is not a call to
the inherited legacy accessor.
[Prefix increment, §13.4.4.1](https://tc39.es/ecma262/2025/multipage/ecmascript-language-expressions.html#sec-prefix-increment-operator)
reads the reference, converts numerically, adds one, writes back and returns
the new value.

This differs from property assignment's deferred PutValue key conversion.
The reviewed evaluator validates the primitive-string computed key **before**
the value expression. Unsupported keys reject at that point. It uses own data
definition rather than inherited Set dispatch, so computed `__proto__` and
ordinary inherited setters do not redirect construction.

The shared parser supports the required computed, static and shorthand forms.
It rejects unsupported noncomputed `__proto__: value` initializers instead of
silently treating them as data; computed and shorthand `__proto__` remain data.
It supports prefix increment on an identifier, with other lvalues/postfix forms
outside this subset. Expression-context object braces are distinguished from
statement and arrow-function block braces. Kernel examples check allocation
order, duplicate field replacement, key-before-value validation and special
names. An empty object heap rejects literal allocation instead of creating
object 0 with itself as its supposed intrinsic prototype.

The intrinsic prototype is independent of a caller variable named `Object`.
The mathematical check that cell 0 exists is not a proof that it is the native
realm's actual Object prototype. Native interpretation still needs that
identity, valid heaps and standard allocation/descriptor behavior. A standard
Object prototype has methods and descriptors; it must not be mistaken for an
empty dictionary merely because JSON serialization can display `{}`.

## Counter and native-domain boundary

The actual module declares
[`let order = 0` at line 18](https://github.com/honojs/hono/blob/5ca49b0720755c585c9a9835f0a479ceea36fb52/src/router/trie-router/node.ts#L18).
It is shared by instances in that module. This checkpoint proves one
expression's resolved-binding update. The current flat value environment and
frozen function-capture model do not prove a persistent shared module cell
across `insert` calls, distinct instances or module instantiations. A caller
binding transported into the expression is explicit scaffolding for that
remaining scope obligation.

There is a known general mutable-scope gap, not merely an untested case:
`runBlock` and the counted-loop wrapper restore an entire saved environment,
while closed invocation restores the caller and uses frozen captures. With an
outer `++order` inside an accepted block or loop body, that restoration can
discard an update that JavaScript would retain. Const/let binding kinds are
also not represented, so parser acceptance does not establish that an increment
targets a writable binding. The current theorem evaluates the object
**expression** directly and preserves its changed environment; it does not
claim native adequacy for all accepted block/prefix programs. General mutable
lexical cells, const errors and captured-cell persistence remain open.

Native prefix interpretation requires a mutable initialized numeric binding,
not merely an environment row containing a number. General const-binding
errors, ToNumeric coercions, BigInt, NaN and infinity are outside this model.
`SafeOrder` restricts the old counter to
`-9007199254740991 ≤ n < 9007199254740991`, so both old and incremented values
are exact safe integers. `score_safe` proves the mathematical bound; IEEE
operation and native-engine adequacy remain separate. There is no theorem of
unbounded globally unique scores.

`NativeBounds` also states legal method/key string sizes, dense-array count and
an existing root. It is not a complete native admissibility checker: standard
stable Set iteration, valid handler identities, mutable binding interpretation,
realm correspondence and resources remain conditions. Handler values are
stored without cloning or invocation. Freshness is relative to allocated
cells; native well-formedness excludes forged dangling references to future
addresses.

## Finite engine disagreement outside the method domain

Independent runs asserted Bun 1.4.0 and Node 22.22.2, checked the upstream pin
and exact source bytes, and reproduced the following traces. The durable
[coercion probe](../../verification/handler-record/coercion-probe.mjs) additionally
checks all 315 source/package blobs and the extracted argument hash.

| Probe with object-valued computed key | Bun 1.4.0 | Node 22.22.2 |
| --- | --- | --- |
| `{[key]: value()}` | `value, key` | `key, value` |
| Actual extracted argument with iterator hook | `iterate, key` | `key, iterate` |
| Supplied call wrapper with push getter | `lookup, iterate, key, push` | `lookup, key, iterate, push` |

Here `key` records an effectful Symbol.toPrimitive call. The normative 2025
ordering is pre-value conversion, as Node observed. The model retains that
ordering and rejects object-valued computed keys; it does not copy the Bun
observation into the specification. The proved method domain uses an already
primitive string, whose conversion has no such effects. These are finite
engine/version observations outside that domain, not comparison exceptions or
a full native-conformance theorem.

Other bounded [native probes](../../verification/handler-record/native.ts)
corroborate relevant restrictions. A throwing iterator leaves the counter
unincremented; a later throwing push leaves an increment already performed.
Inherited `possibleKeys` setters are bypassed by literal own creation. Starting
a wrapper counter at MAX_SAFE_INTEGER yields two equal subsequent native
scores of `9007199254740992`, outside `SafeOrder`. These observations do not
establish error-state rollback or prove that the full Hono module reaches such
a high counter.

## Record-to-loop bridge and remaining source edges

The [bridge](../../HonoLean/Upstream/HandlerRecord/LoopBridge.lean) derives the
actual inner record cell, its own `possibleKeys` descriptor, the array contents,
own `params` absence and the producer's unique-key fact. `ConsumerDomain`
deliberately omits those construction outcomes. It retains explicit transport
of the actual record and array cells, selected-handler binding, helper/read
facts, sizes, prototype closure and other consumer conditions. Record and array
contents are not automatically immutable during the intervening lifecycle.

Own `params` absence alone does not guarantee reset behavior: subsequent
assignment still uses ordinary Set and may find an inherited accessor or
non-writable data. The bridge uses `rootDispatch`, a **descriptor-level** root
lookup with budget 31 that permits absence or writable inherited data. A read
returning undefined would be insufficient. With the newly constructed ordinary
record's prototype and extensibility, that condition establishes the loop's
resettable domain; it is a sufficient admitted domain, not a model of arbitrary
native setters.

The native root-parameter probe installs an inherited setter without a getter.
The actual prior checked reset/append/loop block invokes it, creates no own
`params`, appends the handler and later throws TypeError on its undefined target.
This finite observation explains why own absence cannot replace the descriptor
condition. It does not broaden the proved domain or comparator allowlist.

The [composed kernel example](../../HonoLean/Upstream/HandlerRecord/Examples.lean)
checks actual typed Set creation, two supplied duplicate `id` adds, and this
actual object expression. Construction yields outer object 3, inner record 4,
array 3 and score 8 from counter 7. The later consumer stages only its selected
handler binding and preserves those actual cells. Its domain proof assumes no
handler fields, resettable shape, array contents or uniqueness. Thus the
producer/record/consumer composition is nonempty and obtains those facts from
source execution. Separate zero-key, computed-special-name and score-read
mutant examples exercise the boundary cases.

The private methods-array lookup/push, storage, method/ALL selection, pattern
event production, module-counter cell and full insertion/search control flow
remain unproved edges. The cached pattern sharing described in the
[Set-producer audit](key-set-audit.md) still prevents assuming every pattern
read is pure merely from a readonly TypeScript annotation. External extraction
and byte freshness, the complete TypeScript frontend, general Completion/error
traces and native-runtime adequacy remain part of the wider
[trust boundary](hono-trust-boundary.md). Both whole-insertion and private-push
theorem fields remain unset in the source metadata.
