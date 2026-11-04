# From a function body to an exported closure

The new milestone proves conditional source-model contracts for closure creation
and invocation. It covers the admitted profiles described below; native and
whole-Hono adequacy remain open. The [audit](getpattern-invocation-audit.md)
records the build, fresh-replay and declaration checks.

The [new diagram](../diagrams/getpattern-invocation.png) separates creation once
from calls made later, with the remaining adequacy obligations kept explicit.
[Editable source](../diagrams/getpattern-invocation.excalidraw) ·
[Live scene](https://app.excalidraw.com/s/8wot9n3ajqf/AKwddbfT8ZS).

## What was missing

The existing proof starts with a function body's variables already available.
For example, it can prove what the actual body does when `label` is `'*'`.
That leaves a practical question: how did a call supply that variable, and how
does the function retain access to the same cache between calls?

The new source boundary is the actual contiguous 796 bytes at `url.ts` lines
50–79 in the fixed Hono revision. It includes the typed cache declaration and
the complete exported arrow declaration, with its original comments and body.
The source checker verifies all 315 pinned blobs and exact reassembly from the
previous 52-byte initializer and 744-byte arrow excerpts. Those byte checks are
separate from the semantics and proof.

## A closure remembers where to look

Think of a binding as a named drawer. A cell holds its current value; an
environment maps names to cell identities and refers to its parent environment.
The arrow holds an environment reference. It does not copy a snapshot of every
value at creation time.

That explains two different behaviors. `patternCache` is a constant binding to
a mutable object, so later calls reach the same cache object. `RegExp` is read
when the body reaches the constructor expression, so changing its current
binding can affect a later cold call. A warm hit returns the existing cache
value before it reaches that expression.

A warm call still runs `label.match` before checking the cache. Its temporary
regex literal and capture array may be allocated again. Reusing the cached
tuple and compiled route regex does not make the entire call allocation-free;
the native observer reports the identities it can actually see.

The new interpreter resolves each variable at its evaluation point. Its older
list of name/value pairs is a compatibility projection for the admitted body
semantics, not the authority for live variable reads. In particular, the
wildcard path must not require an initialized cache or constructor that it never
reads. The nearest uninitialized binding is a temporal-dead-zone error; lookup
cannot skip it and silently use an outer binding with the same name.

## An exported function needs an identity

Creating a closure record is insufficient if the exported name is unrelated to
it. Setup reserves the constant `getPattern` binding, creates a function object
linked to the arrow payload and captured environment, and initializes the
binding with that callable object. The binding-call entry resolves the exported
value back to that payload.

The creation-time metadata is also observable: `name` is `getPattern`, `length`
is 2, and there is no own `prototype` property. The optional TypeScript marker
on `next` does not remove the second runtime parameter. Arrow functions are not
constructible: adding a property called `prototype` later does not change their
callable kind. The model makes that distinction explicit.

## Each call gets fresh parameters

Call arguments here are values that the caller has already evaluated. Fresh
parameter cells receive the positional arguments. Missing `next` receives
`undefined`; additional argument values do not bind extra named parameters.
Argument-expression evaluation remains a separate caller obligation.

The arrow retains its creation-time `this`. On return, the interpreter restores
the caller's environment and `this` while preserving the body's actual cache
effects. Fresh activation/local cells may remain in the model's storage. A
zero-effect wildcard body does not imply that the entire invocation allocated
nothing, and no claim is made about native garbage collection or allocation
counts.

## What the checks can teach us

The new native harness loads the exact selected TypeScript setup once per
history, appending an explicitly unverified private-cache observer. It calls the
actual exported arrow with supplied argument lists. An independent oracle
derives parameter, descriptor, cache and identity observations without asking
either implementation for the expected result.

The current cases exercise shared histories, omitted/explicit/extra arguments,
current constructor changes after creation and earlier calls, UTF-16 labels,
terminal-next forms, raw cache-key collisions and inherited/own DATA entries.
Five source mutations include a swapped parameter signature, so a hard-coded
argument-to-name mapping cannot pass merely because the original declaration
happens to use the expected names. The final model/native suite passes all
11 groups; its 348 finite contexts include negative cases alongside the admitted
normal profiles. It also retains the explicit reached-lookahead refusal.

The raw cache key also teaches something about verification. These different
argument pairs produce the same key:

| `label` | `next` | `${label}#${next}` |
| --- | --- | --- |
| `:a#b` | `c` | `:a#b#c` |
| `:a` | `b#c` | `:a#b#c` |

Hono then reuses the first cached tuple. Proving that behavior does not prove
that the cache distinguishes every argument pair, or that the returned tuple
is always the one a caller would expect for the later label. Those are different
properties to state and check. Formal verification gives guarantees about the
stated contract; a contract describing compatibility must preserve the pinned
program's quirks too. The source-created collision histories and the
[checked noninjectivity example](../../HonoLean/Upstream/GetPatternInvocation/Examples.lean)
make this distinction concrete.

Separate controls execute the entire pinned `url.ts` module under Bun 1.4.0 and
Node 22.22.2. Both show that a user-visible `match` callback can replace the
global constructor during the call, before its later read. That is a useful
frontier example: the current closed intrinsic profiles cannot mutate the new
lexical-cell heap through arbitrary callbacks. A finite native observation
cannot establish the missing general callback theorem.

## The limits remain part of the result

The intended contracts cover wildcard and the existing admitted miss, warm,
plain and safe terminal-range profiles. General regex/lookahead behavior remains
open. Sequential constant reservation is sufficient for these actual
declarations; it is not a general proof of module/block declaration
instantiation or all temporal-dead-zone behavior.

Legacy body errors do not retain partial state. The new `outsideModel` outcome
therefore withholds a native throw-state or rollback claim. TypeScript frontend
adequacy, full module instantiation, global-object/accessor coupling, arbitrary
callback effects, native engine/host adequacy and the rest of Hono remain
separate obligations under the [full verification goal](hono-verification-goal.md).
